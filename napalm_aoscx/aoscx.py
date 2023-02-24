"""NAPALM driver for Aruba AOS-CX."""
# Copyright 2020 Hewlett Packard Enterprise Development LP. All rights reserved.
#
# The contents of this file are licensed under the Apache License, Version 2.0
# (the "License"); you may not use this file except in compliance with the
# License. You may obtain a copy of the License at
#
# http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS, WITHOUT
# WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the
# License for the specific language governing permissions and limitations under
# the License.

import copy
import functools
import os
import re
import socket
import telnetlib
import tempfile
import uuid
import inspect
import logging
from collections import defaultdict

from netaddr import IPNetwork
from netaddr.core import AddrFormatError
from netmiko import FileTransfer, InLineTransfer

# NAPALM Base libs
import napalm.base.helpers
from napalm.base.base import NetworkDriver
from napalm.base.exceptions import (
    ConnectionException,
    ReplaceConfigException,
    MergeConfigException,
    ConnectionClosedException,
    SessionLockedException,
    CommandErrorException,
)
from napalm.base.helpers import (
    canonical_interface_name,
    transform_lldp_capab,
    textfsm_extractor,
)
import napalm.base.constants as c

# Aruba AOS-CX lib
import pyaoscx
from pyaoscx.session import Session
from pyaoscx.vlan import Vlan
from pyaoscx.interface import Interface
from pyaoscx.device import Device
from pyaoscx.mac import Mac
from pyaoscx.configuration import Configuration

class AOSCXDriver(NetworkDriver):
    """NAPALM driver for Aruba AOS-CX."""

    def __init__(self, hostname, username, password, version, timeout=60, optional_args=None):
        """NAPALM Constructor for AOS-CX."""
        if optional_args is None:
            optional_args = {}
        self.hostname = hostname
        self.username = username
        self.password = password
        self.timeout = timeout
        self.version = version

        self.platform = "aoscx"
        self.profile = [self.platform]
        self.session = None
        self.isAlive = False
        self.candidate_config = ''

        self.base_url = "https://{0}/rest/v{1}/".format(self.hostname, self.version)

    def open(self):
        """
        Implementation of NAPALM method 'open' to open a connection to the device.
        """
        try:
            self.session = Session(self.hostname, self.version)
            self.session.open(self.username, self.password)
            self.isAlive = True
        except ConnectionError as error:
            # Raised if device not available or HTTPS REST is not enabled
            raise ConnectionException(str(error))

    def close(self):
        """
        Implementation of NAPALM method 'close'. Closes the connection to the device and does
        the necessary cleanup.
        """
        session_info = {
            's' : self.session.s,
            'url': self.base_url
        }
        Session.logout(**session_info)
        self.isAlive = False

    def is_alive(self):
        """
        Implementation of NAPALM method 'is_alive'. This is used to determine if there is a
        pre-existing REST connection that must be closed.
        :return: Returns a flag with the state of the connection.
        """
        return {"is_alive": self.isAlive}

    def get_facts(self):
        """
        Implementation of NAPALM method 'get_facts'.  This is used to retrieve device information
        in a dictionary.
        :return: Returns a dictionary containing the following information:
         * uptime - Uptime of the device in seconds.
         * vendor - Manufacturer of the device.
         * model - Device model.
         * hostname - Hostname of the device
         * fqdn - Fqdn of the device
         * os_version - String with the OS version running on the device.
         * serial_number - Serial number of the device
         * interface_list - List of the interfaces of the device
        """
        switch = Device(self.session)
        switch.get()
        switch.get_subsystems()
        uptime_seconds = (int(switch.boot_time)/1000)
        interface_list = Interface.get_all(self.session)
        product_info = {}
        keys = ['management_module,1/1', 'chassis,1']
        for key in keys:
            if (len(switch.subsystems[key]['product_info']['serial_number']) > 0):
                product_info = switch.subsystems[key]['product_info']
                break
        
        fact_info = {
            'uptime': uptime_seconds,
            'vendor': product_info['vendor'],
            'os_version': switch.software_info['build_id'],
            'serial_number': product_info['serial_number'],
            'model': product_info['product_name'],
            'hostname': switch.hostname,
            'fqdn': switch.hostname,
            'interface_list': list(interface_list.keys())
        }
        return fact_info

    def get_vlans(self):
        """
        Implementation of NAPALM method 'get_vlans'. This is used to retrieve all vlan
        information. 
        :return: Returns a dictionary of dictionaries. The keys for the first dictionary will be the
        vlan_id of the vlan. The inner dictionary will containing the following data for
        each vlan:
         * name (text_type)
         * interfaces (list)
        """
        vlan_json = {}
        vlan_list = Vlan.get_facts(self.session)

        for vlan_id in vlan_list:
            vlan_json[int(vlan_id)] = {
                "name": vlan_list[vlan_id]["name"],
                "interfaces": []
            }
        interface_list = Interface.get_facts(self.session)
        physical_interface_list = {key: value for key, value in interface_list.items() if '/' in key}

        for interface in physical_interface_list:
            interface_facts = physical_interface_list[interface]
            vlan_ids = []
            key = ""
            if 'applied_vlan_trunks' in interface_facts and interface_facts['applied_vlan_trunks'] and (len(interface_facts['applied_vlan_trunks']) > 0):
                key = "applied_vlan_trunks"
            elif 'applied_vlan_tag' in interface_facts and interface_facts['applied_vlan_tag'] and (len(interface_facts['applied_vlan_tag']) > 0):
                key = "applied_vlan_tag"
            
            if key != "":
                vlan_ids = [int(key) for key in interface_facts[key]]
                for id in vlan_ids:
                    vlan_json[id]["interfaces"].append(interface)
        
        return vlan_json

    def get_interfaces(self):
        """
        Implementation of NAPALM method 'get_interfaces'.  This is used to retrieve all interface
        information.  If the interface is a logical interface that does not have hardware info, the
        value will be 'N/A'.
        Note: 'last_flapped' is not implemented and will always return a default value of -1.0
        :return: Returns a dictionary of dictionaries. The keys for the first dictionary will be the
        interfaces in the devices. The inner dictionary will containing the following data for
        each interface:
         * is_up (True/False)
         * is_enabled (True/False)
         * description (string)
         * speed (int in Mbit)
         * MTU (in Bytes)
         * mac_address (string)
        """
        interfaces_return = {}
        interface_list = Interface.get_facts(self.session)
        for interface in interface_list:
            interface_details = interface_list[interface]
            if 'description' not in interface_details or interface_details["description"] == None:
                interface_details["description"] = ""
            if 'max_speed' not in interface_details['hw_intf_info']:
                speed = 'N/A'
            else:
                speed = interface_details['hw_intf_info']['max_speed']
            if 'mtu' not in interface_details:
                mtu = 'N/A'
            else:
                mtu = interface_details['mtu']
            if 'mac_addr' not in interface_details['hw_intf_info']:
                mac_address = 'N/A'
            else:
                mac_address = interface_details['hw_intf_info']['mac_addr']
            interface_dictionary = {
                interface: {
                    'is_up': (interface_details['link_state'] == "up"),
                    'is_enabled': (interface_details['admin_state'] == "up"),
                    'description': interface_details['description'],
                    'last_flapped': -1.0,
                    'speed': speed,
                    'mtu': mtu,
                    'mac_address': mac_address
                }
            }
            interfaces_return.update(interface_dictionary)
        return interfaces_return


def get_interfaces_ip(self):
        """
        Implementation of NAPALM method get_interfaces_ip.  This retrieves all of the IP addresses
        on all interfaces.
        :return: Returns all configured IP addresses on all interfaces as a dictionary of
        dictionaries. Keys of the main dictionary represent the name of the interface.
        Values of the main dictionary represent are dictionaries that may consist of two keys
        'ipv4' and 'ipv6' (one, both or none) which are themselves dictionaries with the IP
        addresses as keys.
        Each IP Address dictionary has the following keys:
            * prefix_length (int)
        """
        interface_ip_dictionary = {}
        interface_details_dictionary = Interface.get_facts(self.session)
        for name, details in interface_details_dictionary.items():
            interface_ip_list = {}
            interface_obj = Interface(self.session, name)
            interface_obj.get()

            ip4_address = {}
            if (('ip4_address' in details) and (details['ip4_address'] is not None) and (len(details['ip4_address']) > 0)):
                ip4_address= {
                    details['ip4_address'][:details['ip4_address'].rfind('/')]: {
                        'prefix_length':
                            int(details['ip4_address']
                            [details['ip4_address'].rfind('/') + 1:])
                        }
                    }
                    
            ip6_address = {}
            ip6_keys = ['ip6_address_link_local']
            for key in ip6_keys:
                if (key in details and len(details[key]) > 0):
                    addresses = list(details[key].keys())
                    for address in addresses:
                        ip6_address[address[:address.rfind('/')]] = {
                            'prefix_length': int(address[address.rfind('/') + 1:])
                        }
            if hasattr(interface_obj, 'ip6_addresses') and len(interface_obj.ip6_addresses) > 0:
                for ip6_address_obj in interface_obj.ip6_addresses:
                    address = ip6_address_obj.address
                    ip6_address[address[:address.rfind('/')]] = {
                            'prefix_length': int(address[address.rfind('/') + 1:])
                    }
    
            if (len(ip4_address) > 0):
                interface_ip_list['ipv4'] = ip4_address

            if (len(ip6_address) > 0):
                interface_ip_list['ipv6'] = ip6_address

            if (len(interface_ip_list) > 0):
                interface_ip_dictionary[name] = interface_ip_list
        
        return interface_ip_dictionary

def get_mac_address_table(self):
        """
        Implementation of NAPALM method get_mac_address_table.  This retrieves information of all
        entries of the MAC address table.
        :return: Returns a lists of dictionaries. Each dictionary represents an entry in the
        MAC Address Table, having the following keys:
            * mac (string)
            * interface (string)
            * vlan (int)
            * active (boolean)
            * static (boolean)
            * moves (int)
            * last_move (float)
        NOTE: 'moves' and 'last_move' is not supported and will default to None
        """
        mac_list = []
        vlan_list = Vlan.get_all(self.session)
        for vlan in vlan_list:
            mac_list.append(Mac.get_all(self.session, vlan_list[vlan]))
        mac_list = list(filter(lambda mac_entry: (len(mac_entry) > 0), mac_list))
        mac_entries = []
        for mac in mac_list:
            mac_key = list(mac.keys())[0]
            mac_attributes = mac_key.split(',')
            mac_type = mac_attributes[0]
            mac_address = mac_attributes[1]

            mac_obj = mac[mac_key]
            mac_obj.get()
            vlan = int(mac_obj._parent_vlan.__dict__['id'])
            interface = list(mac_obj.__dict__['_original_attributes']['port'].keys())[0]

            mac_entries.append(
                {
                    'mac': mac_address,
                    'interface': interface,
                    'vlan': vlan,
                    'static': (mac_type == 'static'),
                    'active': True,
                    'moves': None,
                    'last_move': None
                }
            )
        return mac_entries


def get_config(self, retrieve="all", full=False, sanitized=False):
        """
        Return the configuration of a device. Currently this is limited to JSON format
        :param retrieve: String to determine which configuration type you want to retrieve, default is all of them.
                              The rest will be set to "".
        :param full: Boolean to retrieve all the configuration. (Not supported)
        :param sanitized: Boolean to remove secret data. (Not supported)
        
        :return: The object returned is a dictionary with a key for each configuration store:
            - running(string) - Representation of the native running configuration
            - candidate(string) - Representation of the candidate configuration. 
            - startup(string) - Representation of the native startup configuration.
        """
        if retrieve not in ["running", "candidate", "startup", "all"]:
            raise Exception("ERROR: Not a valid option to retrieve.\nPlease select from 'running', 'candidate', "
                            "'startup', or 'all'")
        else:
            config = Configuration(self.session)
            running_config = ""
            startup_config = ""

            if retrieve == "running":
                running_config = config.get_full_config()
            elif retrieve == "startup":
                startup_config = config.get_full_config(config_name="startup-config")
            elif retrieve == "all":
                running_config = config.get_full_config()
                startup_config = config.get_full_config(config_name="startup-config")
            config_dict = {
                        "running": running_config,
                        "startup": startup_config,
                        "candidate": ""
            }
            return config_dict
