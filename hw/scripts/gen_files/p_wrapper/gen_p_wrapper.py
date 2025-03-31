import argparse
import copy
import pathlib
import re
import subprocess
from collections import OrderedDict
from typing import Any, Dict, NoReturn, Tuple

import hjson
import pandas as pd
from mako import exceptions
from mako.lookup import TemplateLookup
from mako.template import Template


def _getRepoTop() -> str:
  """Retrieve the top level of the git repository."""
  return subprocess.run(['git', 'rev-parse', '--show-toplevel'],
                        check=True,
                        universal_newlines=True,
                        stdout=subprocess.PIPE).stdout.strip()

repo_root = _getRepoTop()

import sys

sys.path.insert(0, f"{repo_root}/hw/scripts/gen_files/")

from conn_info import conn_info
from inf_info import inf_info
from para_info import para_info
from protocol_info import protocol_info
from verible_syntax_mo import VeribleVerilogSyntax, convert_to_dictionary

vs = VeribleVerilogSyntax()


config_file_dict = {
    'ai_core'       : f'{repo_root}/hw/impl/europa/blocks/ai_core/data/ai_core_p.hjson',
    'aic_fabric'    : f'{repo_root}/hw/ip/aic_fabric/default/data/fabric_p.hjson',
    'aic_infra'     : f'{repo_root}/hw/impl/europa/blocks/aic_infra/data/aic_infra_p.hjson',
    'aic_ls'        : f'{repo_root}/hw/impl/europa/blocks/aic_ls/data/aic_ls_p.hjson',
    'aic_mid'       : f'{repo_root}/hw/impl/europa/blocks/aic_mid/data/aic_mid_p.hjson',
    'aic_did'       : f'{repo_root}/hw/impl/europa/blocks/aic_did/data/aic_did_p.hjson',
    'dcd'           : f'{repo_root}/hw/impl/europa/blocks/dcd/data/dcd_p.hjson',
    'l2_impl'       : f'{repo_root}/hw/impl/europa/blocks/l2/data/l2_p.hjson',
    'lpddr_subsys_wrapper'         : f'{repo_root}/hw/impl/europa/blocks/lpddr/data/lpddr_p.hjson',
    'pcie'          : f'{repo_root}/hw/impl/europa/blocks/pcie/data/pcie_p.hjson',
    'pve'           : f'{repo_root}/hw/impl/europa/blocks/pve/data/pve_p.hjson',
    'soc_periph'    : f'{repo_root}/hw/impl/europa/blocks/soc_periph/data/soc_periph_p.hjson',
    'sys_spm'       : f'{repo_root}/hw/impl/europa/blocks/sys_spm/data/sys_spm_p.hjson',
}

protocol_info_file       = f'{repo_root}/hw/scripts/gen_files/protocol'
axi_spill_register_sv    = f'{repo_root}/hw/impl/europa/rtl/axe_axi_multicut_flat.sv'
axis_spill_register_sv   = f'{repo_root}/hw/ip/common_cell_library/default/rtl/cc_stream_spill_reg.sv'
token_spill_register_sv  = f'{repo_root}/hw/ip/token_manager/default/rtl/token_cut.sv'
ocpl_spill_register_sv   = f'{repo_root}/hw/ip/open_core_protocol/default/rtl/ocp_lite_cut.sv'
def createInfoObjects(cfg: Dict[str, Any]) -> Tuple[Any, Any, Any]:
    # Create protocol_info object
    protocol_info_obj = protocol_info(protocol_info_file)
    
    # Create para_info object
    pkg_info = cfg.get('pkg_info', [])
    if pkg_info:
        pkg_info = [pkg.replace("{REPO_ROOT}", repo_root) for pkg in pkg_info]
    para_info_obj = para_info(pkg_info)
    
    # Create inf_info object
    ip_info = OrderedDict([(cfg['module'], cfg['design_file'])])
    if ip_info:
        ip_info = {key: value.replace("{REPO_ROOT}", repo_root) for key, value in ip_info.items()}
    inf_info_obj = inf_info(ip_info, para_info_obj, protocol_info_obj)
    
    return protocol_info_obj, para_info_obj, inf_info_obj

def read_hjson_file(hjson_path: str, key: str):
    """Utility function to read HJSON file and return data based on key."""
   # Adjust the file name by removing '_p' just before '.hjson'
    path            = pathlib.Path(hjson_path)
    hjson_path      = path.parent
    hjson_file_name = path.name
    ip_file_name    = hjson_file_name.replace('_p.hjson', '.hjson')
    ip_hjson_path   = hjson_path / ip_file_name
    
    try:
        with open(ip_hjson_path, 'r') as file:
            data = hjson.load(file)
            result = data.get(key, None)
            return result
    except FileNotFoundError:
        print(f"WARNING: Failed parsing {key}, File not found: {ip_hjson_path}")
    except Exception as e:
        print(f"WARNING: Failed parsing {key}, An unexpected error occurred: {e}")

    return None

def get_localparams(hjson_path: str):
    """Retrieve 'localparam' from HJSON file."""
    return read_hjson_file(hjson_path, 'localparam')

def get_params(hjson_path: str):
    """Retrieve 'param' from HJSON file."""
    return read_hjson_file(hjson_path, 'param')

def _getModuleInfo(filePath: pathlib.Path) -> str:
  """Generate module info using verible script"""
  subprocess.check_output(f"{repo_root}/hw/scripts/gen_files/verible_syntax_mo.py -c " + str(filePath), shell=True)
  return f'{filePath}.hjson'


# List of packages that need parsing to obtain parameter values instead of just their names
pkg_dict = {
  'ai_core_pkg' : f'{repo_root}/hw/impl/europa/blocks/ai_core/rtl/pkg/ai_core_pkg.sv',
#  'sys_ctrl_pkg' : f'{repo_root}/subip/sys_ctrl/rtl/sys_ctrl_pkg.sv',
}

parsed_pkg_dict = {}
for pkg in pkg_dict:
    data = _getModuleInfo(pkg_dict[pkg])
    with open(f'{data}', 'r') as file:
        parsed_pkg_dict[pkg] = hjson.load(file)

# Exception dict for specific interfaces.
with open(f'{repo_root}/hw/scripts/gen_files/templates/wrapper_templates/axi_exceptions.hjson', 'r') as file:
    except_dict = hjson.load(file)

'''
Function to get parameter values inside the mako templates.
It should be passed alone as a value to the template dict
'''
def get_param_value_from_parsed_dicts(param):
    try:
        int(param)
        return int(param)
    except ValueError:
        for pkg_dicts in parsed_pkg_dict.values():
            for pkg_dict in pkg_dicts.values():
                for pkg_param in pkg_dict['parameters']:
                    if param == pkg_param:
                        string_list = pkg_dict['parameters'][pkg_param]
                        if len(string_list) == 1:
                            return int(string_list[0])
                        elif len(string_list) == 2:
                            # Check base before converting to int
                            if 'd' in string_list[0]:
                                return int(string_list[1])
                            elif 'h' in string_list[0]:
                                return int(string_list[1],16)
                            elif 'b' in string_list[0]:
                                return int(string_list[1],2)
    raise ValueError(f'Parameter {param} not found in any of the parsed packages')

# Check if a given port name is in the protocol settings considering that the protocol keys can contain wildcards
def find_port_in_protocol_settings(protocol_settings, port_name):
    matching_keys = []
    for port in protocol_settings:
        # Check if port contains a wildcard, if so, check with a regex if the port name matches
        if '*' in port:
            if re.match(port.replace('*', '.*'), port_name):
                matching_keys.append(port)
        # If no wildcard, check if the port name equals the port exactly
        if port_name == port:
            matching_keys.append(port)
    return matching_keys

def translate_io_pads_to_ports(module_dict, io_csv_file):

    io_csv = pd.read_csv(io_csv_file)

    def find_ports_for_io_pad(io_pad_name):
        related_ports = {}
        for i, io_cell in io_csv.iterrows():
            if io_cell['pad_signal'] == io_pad_name:
                if io_cell['direction'] == 'input' or io_cell['direction'] == 'bidirectional':
                    related_ports[io_cell['core_side_output']] = {
                        'dir': 'input',
                        'width' : [],
                        'pad_side_name' : io_pad_name,
                        'is_io_pad' : True
                    }
                if io_cell['direction'] == 'output' or io_cell['direction'] == 'bidirectional':
                    if io_cell['core_side_input'] != "1'b0":
                        related_ports[io_cell['core_side_input']] = {
                            'dir': 'output',
                            'width' : [],
                            'pad_side_name' : io_pad_name,
                            'is_io_pad' : True
                        }

        if not related_ports:
            print(f"WARNING: could not find any ports for IO pad {io_pad_name}, this is expected when the pad is a placeholder")

        return related_ports

    for protocol, protocol_dict in module_dict['ports'].items():
        if protocol == 'misc':
            for port in list(protocol_dict.keys()):
                protocol_dict.pop(port)
                # If port has the pattern IO_<number>_PAD we have to link it to a more understandable port name
                # Else we do nothing as it is related to lpddr or pcie which have their own constraints.
                if re.match(r"IO_\d+_PAD", port):
                    protocol_dict.update(find_ports_for_io_pad(port))

def ports_preprocessing(module_dict, module_cfg):

    # Add protocol settings from the module cfg to the ports
    for protocol in module_dict['ports'].keys():
        if module_dict['ports'][protocol]:
            protocol_ = 'apb' if 'apb' in protocol else protocol
            protocol_settings = module_cfg['ports'][protocol_]
            for port_name, port_dict in module_dict['ports'][protocol].items():
                # Apply the default settings for this protocol if this is not a new port introduced by another setting
                if 'is_new' not in port_dict:
                    port_dict.update(protocol_settings['defaults'])
                # Overwrite defaults if port_name can be found in the protocol settings
                exception_port_keys = find_port_in_protocol_settings(protocol_settings, port_name)
                for exception_port_key in exception_port_keys:
                    port_dict.update(protocol_settings[exception_port_key])
                    # If this is a port that is not a misc port, we also want to apply the settings to the ports of the interface
                    if not protocol == 'misc':
                        for intf_port_dict in port_dict['ports']:
                            intf_port_dict.update(protocol_settings[exception_port_key])
                # Transform boolean pipe setting to interger
                if port_dict['pipe']:
                    if not isinstance(port_dict['pipe'], int):
                        port_dict['pipe'] = 1

                # For misc signals, we want some extra info
                if protocol == 'misc':
                    if 'is_new' not in port_dict:
                        port_dict['is_new'] = False
                    # Default settings do no apply for clocks
                    port_dict['is_clock'] = False
                    if port_name in module_dict['clocks']:
                        port_dict['pipe'] = False
                        port_dict['is_clock'] = True
                        port_dict['clock'] = port_name
                        # Link the reset field of the port to the first reset the relates to this clock
                        for rst, rst_dict in module_dict['resets'].items():
                            if port_name in rst_dict:
                                port_dict['reset'] = rst
                                break

                    # Default settings do not apply for resets
                    port_dict['is_reset'] = False
                    if port_name in module_dict['resets']:
                        port_dict['pipe'] = False
                        port_dict['is_reset'] = True
                        # Link the clock field of the port to the first clock described in the resets dict
                        # This will work for most ips (that only match one clock to one reset)
                        # However for ips where multiple clocks are linked to one reset, this requires giving the 'right' clock first.
                        if module_dict['resets'][port_name]:
                            port_dict['clock'] = list(module_dict['resets'][port_name].keys())[0]
                        else:
                            port_dict['clock'] = 'async'
                        port_dict['reset'] = port_name
                else:
                    if port_dict['rate_adapter'] and not port_dict['pipe']:
                        raise ValueError(f"The rate adapting on port {port_name} requires pipe/spill registers to be present for this port as well")

noc_replacement_patterns = [
    # change naming
    ('EUROPA_NOC_AI_CORE_[0-3]_INIT_HP_I.*_AXI_', 'AI_CORE_HP_AXI_'), # replace
    ('EUROPA_NOC_AI_CORE_[0-3]_INIT_LP_I_AXI_', 'AI_CORE_LP_AXI_'), # replace
    ('EUROPA_NOC_AI_CORE_[0-3]_TARG_LP_T_AXI_', 'AI_CORE_LP_AXI_'), # replace
    ('EUROPA_NOC_L2_[0-3]_TARG_HP_T_AXI_', 'L2_AXI_'), # replace
    ('EUROPA_NOC_DDRC_TARG_MP_T_AXI_', 'LPDDR_AXI_'), # replace
    ('EUROPA_NOC_PCIE_INIT_HP_I_AXI_', 'PCIE_LP_AXI_'), # replace
    ('EUROPA_NOC_PCIE_TARG_DBI_T_AXI_', 'PCIE_NOC_DBI_AXI_'), # replace
    ('EUROPA_NOC_PCIE_TARG_LP_T_AXI_', 'PCIE_LP_AXI_'), # replace
    ('EUROPA_NOC_SYS_CTRL_INIT_LP_I_AXI_', 'SYS_CTRL_LP_AXI_'), # replace
    ('EUROPA_NOC_SYS_CTRL_TARG_LP_T_AXI_', 'SYS_CTRL_LP_AXI_'), # replace
    ('EUROPA_NOC_SYS_DMA_[0-1]_INIT_HP_I_AXI_', 'SYS_DMA_HP_AXI_'), # replace
    ('EUROPA_NOC_DDRC_TARG_LP_V4_T_', 'LPDDR_NOC_DDRPHY_'), # replace
    ('EUROPA_NOC_DDRC_TARG_LP_', 'LPDDR_DDRCTL_'), # replace
    ('EUROPA_NOC_PCIE_TARG_CFG_T_', 'PCIE_NOC_'), # replace
    # patch
    ('LPDDR_DDRCTL_V3_T', 'LPDDR_DDRCTL'), # replace
]

def noc_preprocessing(ver_dict):

    # fuse axi ports if they are R/W only
    axi_ports = ver_dict['europa_noc']['ports']['axi']
    apb_v3_ports = ver_dict['europa_noc']['ports']['apb_v3']
    apb_v4_ports = ver_dict['europa_noc']['ports']['apb_v4']
    # ai core
    for i in range(0,4):
        if f'ai_core_{i}_init_hp_I1_axi_m' in axi_ports.keys():
            [axi_ports[f'ai_core_{i}_init_hp_I_axi_m']['ports'].append(port) for port in axi_ports[f'ai_core_{i}_init_hp_I1_axi_m']['ports']]
            axi_ports.pop(f'ai_core_{i}_init_hp_I1_axi_m')
    # pcie
    if f'pcie_init_hp_I1_axi_m' in axi_ports.keys():
        [axi_ports[f'pcie_init_hp_I_axi_m']['ports'].append(port) for port in axi_ports[f'pcie_init_hp_I1_axi_m']['ports']]
        axi_ports.pop(f'pcie_init_hp_I1_axi_m')

    # Replace some parameter names
    for protocol, protocol_dict in ver_dict['europa_noc']['ports'].items():
        for port, port_dict in protocol_dict.items():
            if 'param_pref' in port_dict:
                for pattern in noc_replacement_patterns:
                    if re.match(pattern[0],port_dict['param_pref']):
                        port_dict['param_pref'] = re.sub(pattern[0], pattern[1], port_dict['param_pref'])
                        print(f"INFO: replaced param_pref for {port}")
                        break

def ai_core_mvm_preprocessing(ver_dict, target_fpga):
    # AI_CORE_MVM
    if 'ai_core_mvm' in ver_dict.keys() and not target_fpga:
        # Remove ports that are used in the FPGA emulation
        # Filter out ports starting with 'hls_ap_'
        for port in list(ver_dict['ai_core_mvm']['ports']['misc'].keys()):
            if port.startswith('hls_ap_'):
                ver_dict['ai_core_mvm']['ports']['misc'].pop(port)

    # AI_CORE_MVM for fpga
    if 'ai_core_mvm' in ver_dict.keys() and target_fpga:
        # Don't pipe mvm_dp model clock and reset
        ver_dict['ai_core_mvm']['ports']['misc']['hls_ap_clk']['pipe'] = False
        ver_dict['ai_core_mvm']['ports']['misc']['hls_ap_rst_n']['pipe'] = False

def clocks_preprocessing(module_dict, module_cfg):
    module_dict['clocks'] = module_cfg['clocks']
    extra_clocks = {}
    for clk in list(module_dict['clocks'].keys()):
        clk_dict = module_dict['clocks'][clk]
        if clk not in module_dict['ports']['misc']:
            raise ValueError(f"Could not find {clk} specified in cfg file among misc ports")
        if clk_dict['gate'] and clk_dict['divider']:
            raise ValueError(f"Both a clock gate and divider are set for clock {clk} in the cfg file. This is not allowed")
        if clk_dict['gate']:
            #clk_dict['internal_signal'] = f"{clk}_gated"
            clk_dict['internal_signal'] = f"{clk}"
            if  clk_dict['gate']['enable'] not in module_dict['ports']['misc']:
                print(f"INFO: creating new misc port {clk_dict['gate']['enable']} as clock gate enable for {clk}")
                for rst, rst_dict in module_cfg['resets'].items():
                    if clk in rst_dict:
                        clk_gate_rst = rst
                        break
                module_dict['ports']['misc'][clk_dict['gate']['enable']] = {
                    'width' : [],
                    'dir' : 'input logic',
                    'unpacked_dim' : [],
                    'is_new' : True,
                    'pipe' : False,
                    'clock' : clk,
                    'reset' : clk_gate_rst,
                    'input_budget' : 0.5,
                    'output_budget' : 0.5,
                    'static' : False,
                    'multi_cycle' : False,
                    'clock_edge' : 'rising'
                }
        # commenting out clk divider for now - required later
        #elif clk_dict['divider']:
        #    clk_dict['internal_signal'] = add_clock_divider(module_dict, module_cfg, clk)
        else:
            clk_dict['internal_signal'] = clk

    # Add the extra clocks to the module_dict
    module_dict['clocks'].update(extra_clocks)

    # Translate the frequency in MHz to a period string in ns
    for clk, clk_dict in module_dict['clocks'].items():
        clk_dict['period'] = f"{1000/clk_dict['freq']:.3f}"

def add_clock_divider(module_dict, module_cfg, clk):
    clk_dict = module_dict['clocks'][clk]
    #internal_signal = f"{clk}_divided"
    internal_signal = f"{clk}"
    clk_dict['divider']['inst_name'] = f"i_{clk}_divider_{module_dict['module']}"
    # When the control clock for the divider is not passed along in the divider dict we have to make it.
    if 'ctrl_clk' not in clk_dict['divider']:
        clk_dict['divider']['ctrl_clk'] = f"{clk}_div_ctrl_clk"
        # Add the new clock to module_dict['clocks']
        module_dict['clocks'][clk_dict['divider']['ctrl_clk']] = {
                    'freq' : 20,
                    'divider' : False,
                    'gate' : False,
                    'internal_signal' : clk_dict['divider']['ctrl_clk'],
                    'uncertainty' : 0.1,
                    'comment' : 'Auto generated clock for the ctrl of the clock divider'
                }
        # Create a new misc port for the new clock
        module_dict['ports']['misc'][clk_dict['divider']['ctrl_clk']] = {
                    'width' : [],
                    'dir' : 'input logic',
                    'unpacked_dim' : [],
                    'is_new' : True,
                    'pipe' : False,
                    'clock' : clk_dict['divider']['ctrl_clk'],
                    'static' : False,
                    'multi_cycle' : False,
                    'clock_edge' : 'rising'
                }
    # Check that the passed along clock is defined in the module config
    else:
        if clk_dict['divider']['ctrl_clk'] not in module_cfg['clocks']:
            raise ValueError(f"Clock {clk_dict['divider']['ctrl_clk']} is not defined in the module config")

    if 'ctrl_incr' not in clk_dict['divider']:
        clk_dict['divider']['ctrl_incr'] = f"{clk}_div_ctrl_incr_i"
        module_dict['ports']['misc'][clk_dict['divider']['ctrl_incr']] = {
                    'width' : ['europa_pkg', 'PHASE_ACC_WIDTH', 1, 0],
                    'dir' : 'input logic',
                    'unpacked_dim' : [],
                    'is_new' : True,
                    'pipe' : False,
                    'clock' : clk_dict['divider']['ctrl_clk'],
                    'reset' : clk_dict['divider']['reset'],
                    'static' : False,
                    'multi_cycle' : False,
                    'clock_edge' : 'rising',
                    'dly_min' : {
                        'abs': f"{0.5*1000/clk_dict['freq']:.3f}"
                    },
                    'dly_max' : {
                        'abs': f"{0.5*1000/clk_dict['freq']:.3f}"
                    }
                }
    if 'ctrl_enable' not in clk_dict['divider']:
        clk_dict['divider']['ctrl_enable'] = f"{clk}_div_ctrl_enable_i"
        module_dict['ports']['misc'][clk_dict['divider']['ctrl_enable']] = {
                    'width' : [],
                    'dir' : 'input logic',
                    'unpacked_dim' : [],
                    'is_new' : True,
                    'pipe' : False,
                    'clock' : clk_dict['divider']['ctrl_clk'],
                    'reset' : clk_dict['divider']['reset'],
                    'static' : False,
                    'multi_cycle' : False,
                    'clock_edge' : 'rising',
                    'dly_min' : {
                        'abs': f"{0.5*1000/clk_dict['freq']:.3f}"
                    },
                    'dly_max' : {
                        'abs': f"{0.5*1000/clk_dict['freq']:.3f}"
                    }
                }
    if 'ctrl_clear' not in clk_dict['divider']:
        clk_dict['divider']['ctrl_clear'] = f"{clk}_div_ctrl_clear_i"
        module_dict['ports']['misc'][clk_dict['divider']['ctrl_clear']] = {
                    'width' : [],
                    'dir' : 'input logic',
                    'unpacked_dim' : [],
                    'is_new' : True,
                    'pipe' : False,
                    'clock' : clk_dict['divider']['ctrl_clk'],
                    'reset' : clk_dict['divider']['reset'],
                    'static' : False,
                    'multi_cycle' : False,
                    'clock_edge' : 'rising',
                    'dly_min' : {
                        'abs': f"{0.5*1000/clk_dict['freq']:.3f}"
                    },
                    'dly_max' : {
                        'abs': f"{0.5*1000/clk_dict['freq']:.3f}"
                    }
                }
    if 'ctrl_cg_en' not in clk_dict['divider']:
        clk_dict['divider']['ctrl_cg_en'] = f"{clk}_div_ctrl_cg_en_o"
        module_dict['ports']['misc'][clk_dict['divider']['ctrl_cg_en']] = {
                    'width' : [],
                    'dir' : 'output logic',
                    'unpacked_dim' : [],
                    'is_new' : True,
                    'pipe' : False,
                    'clock' : clk,
                    'reset' : clk_dict['divider']['reset'],
                    'static' : False,
                    'multi_cycle' : False,
                    'clock_edge' : 'rising',
                    'dly_min' : {
                        'abs': f"{0.5*1000/clk_dict['freq']:.3f}"
                    },
                    'dly_max' : {
                        'abs': f"{0.5*1000/clk_dict['freq']:.3f}"
                    }
                }
    if clk_dict['divider']['reset'] in module_cfg['resets']:
                # If the ctrl_rst is not specified, we have to make it. It will be a synced version of the divider reset towards the ctrl_clk
        if 'ctrl_rst' not in clk_dict['divider']:
            clk_dict['divider']['ctrl_rst'] = clk_dict['divider']['reset']
            module_cfg['resets'][clk_dict['divider']['ctrl_rst']][clk_dict['divider']['ctrl_clk']] = {
                        'synchronise' : True,
                        'internal_signal' : f"{clk_dict['divider']['reset']}"
#                        'internal_signal' : f"{clk_dict['divider']['reset']}_{clk_dict['divider']['ctrl_clk']}_synced"
                    }
        elif clk_dict['divider']['ctrl_rst'] not in module_cfg['resets']:
            raise ValueError(f"Reset {clk_dict['divider']['ctrl_rst']} specified as reset for divider on clock {clk}, does not exists in resets cfg.")
    else:
        raise ValueError(f"Reset {clk_dict['divider']['reset']} specified as reset for divider on clock {clk}, does not exists in resets cfg.")

    return internal_signal

def resets_preprocessing(module_dict, module_cfg):
    extra_resets = {}
    module_dict['resets'] = module_cfg['resets']
    for rst, rst_dict in module_dict['resets'].items():
        if rst not in module_dict['ports']['misc']:
            raise ValueError(f"Could not find {rst} specified in cfg file among misc ports")
        for clk in rst_dict:
            if clk not in module_dict['clocks']:
                raise ValueError(f"Could not find clock {clk}, linked to reset {rst} in cfg file among the clocks")
            if 'internal_signal' not in rst_dict[clk]:
                rst_dict[clk]['internal_signal'] = rst
#                rst_dict[clk]['internal_signal'] = f"{rst}_{clk}_synced" if rst_dict[clk]['synchronise'] else rst
    module_dict['resets'].update(extra_resets)
                      
def preprocess_dict(ver_dict, wrap_cfg_dict, target_fpga=False):

    # Custom preprocessing for some modules
    #if 'europa_noc' in ver_dict.keys():
    #    noc_preprocessing(ver_dict)
    #if 'ai_core_mvm' in ver_dict.keys():
    #    ai_core_mvm_preprocessing(ver_dict, target_fpga)

    # GENERAL
    # Add properties from wrap config to port_dicts
    for module in list(ver_dict):
        # If the module not in the wrap_cfg_dict then it is not a top-level partition module and should not be wrapped.
        # Remove it from the dict
        if not module in wrap_cfg_dict:
            ver_dict.pop(module)
        else:
            #ver_dict[module]['stub_insertion'] = wrap_cfg_dict[module]['stubbing']
            module_dict = ver_dict[module]
            module_cfg = copy.deepcopy(wrap_cfg_dict[module])
            module_dict['wrap_p'] = module_cfg['wrap_p']
            module_dict['localparam'] = module_cfg['localparam']
            module_dict['param'] = module_cfg['param']
            module_dict['wrapper_name'] = module_cfg['wrapper_name']
            module_dict['pkg_info'] = module_cfg['pkg_info']
            module_dict['design_file'] = module_cfg['design_file']
            module_dict['design_name'] = module_cfg['design_name']

            # Add optional extra imports to the wrapper file
            if 'imports' in module_cfg:
                module_dict['imports'] += module_cfg['imports']

            # Add clocks and resets
            if module_cfg['clocks']:
                clocks_preprocessing(module_dict, module_cfg)
            else:
                raise ValueError(f"wrap config does not specify clocks for {module}")

            if wrap_cfg_dict[module]['resets']:
                resets_preprocessing(module_dict, module_cfg)
            else:
                raise ValueError(f"wrap config does not specify resets for {module}")

            # Add dft settings
            if 'dft' in module_cfg:
                module_dict['dft'] = module_cfg['dft']
             
            if 'pctl' in module_cfg:
                module_dict['pctl'] = module_cfg['pctl']
                module_dict['pctl'].setdefault('override_con', {})
                module_dict['pctl']['override_con']['o_partition_rst_n'] = f"{module_dict['design_name']}_rst_n"
                
            if 'ip_con_file' in module_cfg:
                 module_dict['ip_con_file'] = module_cfg['ip_con_file']

            if 'pvt_sensor' in module_cfg:
                 module_dict['pvt_sensor'] = module_cfg['pvt_sensor']

            if 'ao_csr' in module_cfg:
                 module_dict['ao_csr'] = module_cfg['ao_csr']

            if 'ip_ignore_conn' in module_cfg:
                 module_dict['ip_ignore_conn'] = module_cfg['ip_ignore_conn']
            
            if 'ip_override_con' in  module_cfg:
                module_dict['ip_override_con'] = module_cfg['ip_override_con']

            # Add protocol settings from the module cfg to the ports
            ports_preprocessing(module_dict, module_cfg)

            # Do some sanity checks on the ports
            ports_sanity_checks(module_dict, module_cfg)

def ports_sanity_checks(module_dict, module_cfg):

    # Check that the clock and reset of each port is defined as a clock in the clocks dict
    for protocol in module_dict['ports'].keys():
        for port_name, port_dict in module_dict['ports'][protocol].items():
            if isinstance(port_dict['clock'], list):
                if len(port_dict['clock']) < 2:
                    raise ValueError(f"Clock list for port {port_name} contains only one clock. This is not allowed. If only one clock is needed, use a string instead of a list.")
                for clk in port_dict['clock']:
                    if clk not in module_dict['clocks'] and clk != 'async':
                        raise ValueError(f"Could not find clock {clk} for port {port_name} in the clocks dict for this module")
            #elif (port_dict['clock'] not in module_dict['clocks']) and ('generated_clocks' in module_cfg['internal_constraints'] and port_dict['clock'] not in module_cfg['internal_constraints']['generated_clocks']) and port_dict['clock'] != 'async':
            #    if 'allow_undefined_clock' in port_dict and port_dict['allow_undefined_clock'] == port_dict['clock']:
            #        print(f"WARNING: allowing {port_name} to be linked to a clock ({port_dict['clock']}) that is not defined in the hjson clocks, make sure this is intended!")
            #    else:
            #        raise ValueError(f"Could not find clock {port_dict['clock']} for port {port_name} in the clocks dict for this module")
            if port_dict['reset'] not in module_dict['resets']:
                raise ValueError(f"Could not find reset {port_dict['reset']} for port {port_name} in the resets dict for this module")

def updateWrapperInfo(cfg: Dict[str, Any], filePath: str, instance_name: str, key: str) -> None:
    filePath = pathlib.Path(filePath.replace("{REPO_ROOT}", repo_root))
    fileName = filePath.stem
    moduleJson = _getModuleInfo(filePath)

    # Load and parse the HJSON file containing module configurations
    with open(moduleJson) as file:
        moduleJsonCont = hjson.load(file)
        moduleInfo = moduleJsonCont[fileName]

    cfg[key] = {"sig": [], "info": {}}
    cfg[key]['instance_name'] = instance_name

    # Iterate through each signal in the module's "misc" port section
    for sig in moduleInfo["ports"]["misc"]:
        cfg[key]["sig"].append(sig)
        cfg[key]["info"][sig] = {}
        cfg[key]["info"][sig]["dir"]     = moduleInfo["ports"]["misc"][sig]["dir"]
        cfg[key]["info"][sig]["width"]   = moduleInfo["ports"]["misc"][sig]["width"]
        cfg[key]["info"][sig]["newName"] = sig

        # Set direction only info based on the presence of 'input' or 'output' in the signal's direction
        if "input" in moduleInfo["ports"]["misc"][sig]["dir"]:
            cfg[key]["info"][sig]["dir_only"] = "input"
        elif "output" in moduleInfo["ports"]["misc"][sig]["dir"]:
            cfg[key]["info"][sig]["dir_only"] = "output"
        else:
            cfg[key]["info"][sig]["dir_only"] = "inout"


def updatePartitionInfo(cfg: Dict[str, Any]) -> None:
    updateWrapperInfo(cfg, "{REPO_ROOT}/hw/ip/pctl/default/rtl/pctl.sv", "pctl", "partition")

def updateSpillInfo(cfg: Dict[str, Any], 
                    module_name: str, 
                    module_key: str, 
                    port_type: str, 
                    width_map: Dict[str, str], 
                    register_sv: str, 
                    protocol_info_obj: Any, 
                    para_info_obj: Any, 
                    inf_info_obj: Any) -> None:    
    # Get module info
    updateWrapperInfo(cfg, register_sv, module_name, module_key)
    
    # Populate parameter info
    cfg[module_key]['params'] = {}
    for bus_name, bus_info in cfg['ports'][port_type].items():
        for port in bus_info['ports']:
            width = inf_info_obj.ip_inf_info[cfg['module']]["ports"]["misc"][port['port']]['symbol_id']
            for key, label in width_map.items():
                if key in port['port']:
                    if bus_name not in cfg[module_key]['params']:
                        # Ignore direction when matching bus name
                        bus_name = bus_name[2:]
                        cfg[module_key]['params'][bus_name] = {}
                    
                    cfg[module_key]['params'][bus_name][label] = width
                    break

def updateAxiSpillInfo(cfg              : Dict[str, Any], 
                       protocol_info_obj: Any, 
                       para_info_obj    : Any, 
                       inf_info_obj     : Any) -> None:
    width_map = {
        '_awid'  : 'AxiIdWidth',
        '_wdata' : 'AxiDataWidth',
        '_awaddr': 'AxiAddrWidth'
    }
    updateSpillInfo(cfg, 'axe_axi_multicut_flat', 'axi_spill', 'axi', width_map, axi_spill_register_sv, protocol_info_obj, para_info_obj, inf_info_obj)

def updateTokenSpillInfo(cfg                : Dict[str, Any], 
                         protocol_info_obj  : Any, 
                         para_info_obj      : Any, 
                         inf_info_obj       : Any) -> None:
    width_map = {
        '_rdy'  : 'NumTokens'
    }
    updateSpillInfo(cfg, 'token_cut', 'token_spill', 'token', width_map, token_spill_register_sv, protocol_info_obj, para_info_obj, inf_info_obj)

def updateAxisSpillInfo(cfg                 : Dict[str, Any], 
                        protocol_info_obj   : Any, 
                        para_info_obj       : Any, 
                        inf_info_obj        : Any) -> None:
    width_map = {
        '_tdata'  : 'DataWidth'
    }
    updateSpillInfo(cfg, 'cc_stream_spill_reg', 'axis_spill', 'axis', width_map, axis_spill_register_sv, protocol_info_obj, para_info_obj, inf_info_obj)

def updateOCPLSpillInfo(cfg                : Dict[str, Any], 
                         protocol_info_obj  : Any, 
                         para_info_obj      : Any, 
                         inf_info_obj       : Any) -> None:
    width_map = {
        '_maddr'  : 'addr_t',
        '_mdata'  : 'data_t'
    }
    updateSpillInfo(cfg, 'ocp_lite_cut', 'ocpl_spill', 'ocpl', width_map, ocpl_spill_register_sv, protocol_info_obj, para_info_obj, inf_info_obj)

def wrap_module(module, module_dict, f, wrapper):

    cfg = copy.deepcopy(module_dict)
    cfg['module'] = module
    cfg['upper_module'] = module.upper()
    cfg['description'] = "Auto-Generated Physical Wrapper, generated by scripts/env/wrap_module.py"
    cfg['mail'] = "bert.moons@axelera.ai"
    cfg['print_header'] = True
    cfg['year'] = 2024
    cfg['except_dict'] = except_dict
    if 'dft_ports' not in cfg:
        cfg['dft_ports'] = {}
    cfg['recognize_dft_int'] = False
    cfg["dft"]          = module_dict.get("dft", "")  
    
    updatePartitionInfo(cfg)    

    protocol_info_obj, para_info_obj, inf_info_obj = createInfoObjects(cfg)
    updateAxiSpillInfo(cfg  , protocol_info_obj, para_info_obj, inf_info_obj)
    updateTokenSpillInfo(cfg, protocol_info_obj, para_info_obj, inf_info_obj)
    updateAxisSpillInfo(cfg , protocol_info_obj, para_info_obj, inf_info_obj)
    updateOCPLSpillInfo(cfg , protocol_info_obj, para_info_obj, inf_info_obj)
    
    with open(f"{cfg['module']}.wrap.debug.hjson", "w") as debugHjson:
       hjson.dump(cfg, debugHjson)

    render_file(f, wrapper, cfg)

def instertFilter(orig_str, filter_statement):
    i = orig_str.find('-filter "') + len('-filter "')
    if i != -1:
        return orig_str[:i] + filter_statement + " && " + orig_str[i:]
    else:
        return orig_str[:-1] + ' -filter "' + filter_statement + '"]'

templateLookup = TemplateLookup(directories=[f'{repo_root}/hw/scripts/gen_files/templates/'])

def render_file(f, wrapper, cfg):
    # Add functions to be used in the mako templates to the dict
    cfg['get_param_value_from_parsed_dicts'] = get_param_value_from_parsed_dicts
    cfg['instertFilter'] = instertFilter
    t = Template(f"<%include file='{wrapper}.mako'/>",lookup=templateLookup)
    try:
        rendered_output = t.render(**cfg)
    except:
        print(exceptions.text_error_template().render())
    f.write(rendered_output.encode())

def generate_verilog_file(ver_dict, filename, module_name, wrapper_name):
    print(f"INFO: generating '{pathlib.Path(filename).resolve()}' for module '{module_name}'")
    with open(filename, 'wb') as f:
        wrap_module(module_name, ver_dict[module_name], f, wrapper_name)

    return filename

def getSignals(self):
  """Get IP level signals and other ip info"""
  if self.ipConfig:
    filePath = self.ipConfig["design_file"].replace("{REPO_ROOT}", self.gitRepo)
    ipJson   = _getModuleInfo(filePath)
    
    with open(ipJson) as file:
      ipJsonCont = hjson.load(file)
      self.ipInfo = ipJsonCont[self.ipConfig["design_name"]]

def main():
    parser = argparse.ArgumentParser(
        description="(System)Verilog wrapper tool, creates a physical wrapper for a partion with either axi-cuts or split_cdcs"
    )
    parser.add_argument(
        "-t", '--target-ip', nargs='+', default='ai_core_mvm'
    )
    parser.add_argument(
        '--fpga', action='store_true', default=False, help='Generate sources for FPGA emulation'
    )
    parser.add_argument(
        '-debug', type=bool, default=False, help='Enable generation of debug hjson file'
    )

    args = parser.parse_args()
    generated_files = []
    # Look up all target ip rtl sources.
    verilog_files = []
    wrap_cfg_dict = {}
    target_ips = config_file_dict.keys() if 'all' in  args.target_ip else args.target_ip
    for target_ip in target_ips:
        # special handling for l2 as a special case
        wrapper_name = f"{target_ip}_p"
        if target_ip == 'l2':
            target_ip = 'l2_impl'
        elif target_ip == 'lpddr':
            target_ip = 'lpddr_subsys_wrapper'
        with open(config_file_dict[target_ip], 'r') as ip_cfg_file:
            wrap_cfg_dict.setdefault(target_ip, {})
            wrap_cfg_dict[target_ip].update(hjson.load(ip_cfg_file))
            wrap_cfg_dict[target_ip]['wrapper_name'] = wrapper_name
            wrap_cfg_dict[target_ip]['localparam'] = get_localparams(config_file_dict[target_ip])
            wrap_cfg_dict[target_ip]['param'] = get_params(config_file_dict[target_ip])
        try:
            if wrap_cfg_dict[target_ip]['design_file'] != '':
                target_file = wrap_cfg_dict[target_ip]['design_file'].replace("{REPO_ROOT}", repo_root)
            else:
                continue
        except KeyError:
            print(f"INFO: no top-level target found for {target_ip}, skipping")
        else:
            verilog_files.append(target_file)
            if "mbist_file" in wrap_cfg_dict[target_ip] and args.mbist:
                target_file = eval(wrap_cfg_dict[target_ip]['mbist_file'])
                verilog_files.append(target_file)

    target_fpga = args.fpga

    # Loop over all files that need wrapping
    for verilog_file in verilog_files:
        print(f"INFO: parsing file {verilog_file}")
        # Parse the file
        data = vs.parse_file(verilog_file)
        # Convert the parsed file to a dictionary
        # Use process_protocol_sig=True Flag to process specific protocol signals
        ver_dict = convert_to_dictionary(data, process_protocol_sig=True)

        #Check that ver_dict only has one key or that it has a europa_noc key
        if len(ver_dict.keys()) != 1:
            # Drop all other keys except europa_noc
            if 'europa_noc' in ver_dict:
                ver_dict = {k: v for k, v in ver_dict.items() if k == 'europa_noc'}
            else:
                raise ValueError(f"ERROR: verilog file {verilog_file} contains multiple modules, this is not supported")

        modulename = list(ver_dict.keys())[0]
        ip_path = "/".join(config_file_dict[modulename].split('/')[:-1])
        ver_dict[modulename]['ip_path'] = "subip" + "/subip".join(ip_path.split('/subip')[1:])
        ver_dict[modulename]['module'] = modulename
        if modulename == 'europa':
            ver_dict[modulename]['ip_path'] = "src"
            translate_io_pads_to_ports(ver_dict[modulename], eval(wrap_cfg_dict[modulename]['io_csv_file']))

        skipp_mbist_lines = [
            {'pattern':'set_clock_groups', 'excludes' : []} # Clock groups are defined in clock_definitions.sdc
        ]
        skipp_mbist_lines.append({'pattern' : 'set_case_analysis', 'excludes' : ['TEST1', 'TEST_RNM', 'RM', 'RME', 'WA', 'WPULSE', '/LS', '/DS', '/SD']}) # Case analysis are defined in io_case_analysis.sdc or exceptions.sdc (except for TEST1 and TEST_RMN and sys_ctrl)

        # Not used
        skipp_dis_arc_lines = []

        # preprocess module specific changes
        preprocess_dict(ver_dict, wrap_cfg_dict, target_fpga=target_fpga)

        # Dump debug hjson file when args.debug is set
        if args.debug:
            with open(f"{ip_path}/{modulename}_debug.hjson", 'w') as f:
                hjson.dump(ver_dict, f)

        # write out wrapped verilog files
        if wrap_cfg_dict[modulename]['wrap_p']:
            wrapper_file_name = ""
            if modulename == "europa_noc":
                wrapper_file_name = f"{ip_path}/rtl/noc/{modulename}_p.sv"
            elif modulename == "l2_impl":
                wrapper_file_name = f"{ip_path}/../rtl/l2_p.sv"
            elif modulename == "lpddr_subsys_wrapper":
                wrapper_file_name = f"{ip_path}/../rtl/lpddr_p.sv"
            else:
                wrapper_file_name = f"{ip_path}/../rtl/{modulename}_p.sv"
                
            wrapper_file_name = pathlib.Path(wrapper_file_name.replace("/rtl/", "/rtl/build_wrapper/"))
            wrapper_file_name.parent.mkdir(parents=True, exist_ok=True)
            generated_files.append(generate_verilog_file(ver_dict, wrapper_file_name, modulename, "wrapper_p.sv"))

if __name__ == "__main__":
  main()
