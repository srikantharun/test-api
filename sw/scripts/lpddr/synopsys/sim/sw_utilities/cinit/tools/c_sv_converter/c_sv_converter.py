#!/usr/bin/env python3

# -------------------------------------------------------------------------------
# 
# Copyright 2024 Synopsys, INC.
# 
# This Synopsys IP and all associated documentation are proprietary to
# Synopsys, Inc. and may only be used pursuant to the terms and conditions of a
# written license agreement with Synopsys, Inc. All other use, reproduction,
# modification, or distribution of the Synopsys IP or the associated
# documentation is strictly prohibited.
# Inclusivity & Diversity - Visit SolvNetPlus to read the "Synopsys Statement on
#            Inclusivity and Diversity" (Refer to article 000036315 at
#                        https://solvnetplus.synopsys.com)
# 
# Component Name   : DWC_ddrctl_lpddr54
# Component Version: 1.60a-lca00
# Release Type     : LCA
# Build ID         : 0.0.0.0.TreMctl_302.DwsDdrChip_8.26.6.DwsDdrctlTop_5.12.7
# -------------------------------------------------------------------------------


import os
import sys
import re
import argparse

C_HEADER = "/*****************************************************************************\n"       \
           " *\n"                                                                                   \
           " *\n"                                                                                   \
           " *                    (C) COPYRIGHT 2022 SYNOPSYS, INC.\n"                              \
           " *                            ALL RIGHTS RESERVED\n"                                    \
           " *\n"                                                                                   \
           " * This software and the associated  documentation are proprietary to \n"               \
           " * Synopsys, Inc. This software may only be used in accordance with the terms \n"       \
           " * and conditions of a written license agreement with Synopsys, Inc. All other\n"       \
           " * use, reproduction, or distribution of this software is strictly prohibited.\n"       \
           " *\n"                                                                                   \
           " * The entire notice above must be reproduced on all authorized copies.\n"              \
           " *\n"                                                                                   \
           " *****************************************************************************/\n\n"    \
           "#ifndef SNPSDDRDEFINES_{file_name}_H\n"                                                             \
           "#define SNPSDDRDEFINES_{file_name}_H\n\n"                                                           \
           "#ifdef	__cplusplus\n"                                                                  \
           "extern \"C\" {{\n"                                                                       \
           "#endif\n\n"                                                                             \
           "/*************************************************************************\n"           \
           " * T Y P E D E F S    &    D E F I N E S\n"                                             \
           " *************************************************************************/\n\n"

C_FOOTER = "\n\n/*************************************************************************\n"      \
           " * G L O B A L    V A R I A B L E S\n"                                                 \
           " *************************************************************************/\n\n"       \
           "/*************************************************************************\n"          \
           " * F U N C T I O N    P R O T O T Y P E S\n"                                           \
           " *************************************************************************/\n\n\n"     \
           "#ifdef	__cplusplus\n"                                                                 \
           "}}\n"                                                                                   \
           "#endif\n\n"                                                                            \
           "#endif	/* SNPSDDRDEFINES_{file_name}_H */\n"

# List of element that should be removed from when converting System Verilog files to C
SV_EXCLUDED_ELEMS_REGEX = [
    r'\/\/.*',
    r'^\s*\/\*.*\*\/',
    r'^\s*$\n',
    r'^\`define(\s+)log(\s*)(\()(\s*)([a-zA-Z0-9]+)(\s*)(\))(\s*).*(?<!\\)$\n',
    r'^\`define(\s+)UMCTL_LOG2(\s*)(\()(\s*)([a-zA-Z0-9]+)(\s*)(\))(\s*).*(?<!\\)$\n',
    r'([a-zA-Z0-9_]+)(\.)([a-zA-Z0-9_]+).*(?<!\\)$\n',
    r'\`define(\s*)(SYS)(\s+).*(?<!\\)$\n',
    r'\`define(\s*)UMCTL2_PORT_DW_TABLE(\s*).*(?<!\\)$\n',
    r'\`define(\s*)UMCTL2_NUM_VIR_CH_TABLE(\s*).*(?<!\\)$\n',
    r'\`define(\s*)MEMC_DCERRFIELD(\s*).*(?<!\\)$\n',
    r'\`define(\s*)MEMC_WRCMD_ENTRIES_ADDR(\s*).*(?<!\\)$\n',
    r'\`define(\s*)UMCTL2_REG_MSK_STAT_OPERATING_MODE(\s*).*(?<!\\)$\n',
    r'\`define(\s*)UMCTL2_REG_MSK_STAT(\s*).*(?<!\\)$\n',
    r'\`define(\s*)UMCTL2_REG_MSK_.*(?<!\\)$\n',
    r'\`define(\s*)UMCTL2_REG_SIZE_.*(?<!\\)$\n',
    r'\`define(\s*)UMCTL2_REG_OFFSET_.*(?<!\\)$\n',
    r'\SHIFTAPBADDR(\s*)(\().*(?<!\\)$\n',
    r'\`define(\s+)__INCLUDE_DDRC_PKG(\s*).*(?<!\\)$\n',
    r'\`define(\s+)TOP(\s*).*(?<!\\)$\n',
    r'\`define(\s+)TB_DUT(\s*).*(?<!\\)$\n',
    r'\`define(\s+)TB_DDR_CHIP(\s*).*(?<!\\)$\n',
    r'\`define(\s+)DDR_CHIP_TOP(\s*).*(?<!\\)$\n',
    r'\`define(\s+)UMCTL2_TOP(\s*).*(?<!\\)$\n',
    r'\`define(\s+)MIN(\s*).*(?<!\\)$\n',
    r'\`define(\s+)MAX(\s*).*(?<!\\)$\n',
    r'\`define(\s+)log(\s*).*(?<!\\)$\n',
    r'\`define.*\$clog2.*$\n',
    r'\`define(\s+)dut_error(\s*).*(?<!\\)$\n',
    r'\`define(\s+)dut_warning(\s*).*(?<!\\)$\n',
    r'\`define(\s+)APB_WRITE(\s*).*(?<!\\)$\n',
    r'\`define(\s+)APB_WRITE_B(\s*).*(?<!\\)$\n',
    r'\`define(\s+)WRITE_DDRCIF_B(\s*).*(?<!\\)$\n',
    r'\`define(\s+)WRITE_DDRCIF(\s*).*(?<!\\)$\n',
    r'\`define(\s+)DDRCIF_TO_DR(\s*).*(?<!\\)$\n',
    r'\`define(\s+)DDRCIF_TO_APB(\s*).*(?<!\\)$\n',
    r'\`define(\s+)APB_READ_DR(\s*).*(?<!\\)$\n',
    r'\`define(\s+)APB_READ_RD(\s*).*(?<!\\)$\n',
    r'\`define(\s+)ONE_PCLK(\s*).*(?<!\\)$\n',
    r'\`define(\s+)APB_POLLING_DR(\s*).*(?<!\\)$\n',
    r'\`define(\s+)APB_POLLING_NE_RD(\s*).*(?<!\\)$\n',
    r'\`define(\s+)APB_POLLING_NE_DR(\s*).*(?<!\\)$\n',
    r'\`define(\s+)APB_QUASI_DYN_G0_SLEEP(\s*).*(?<!\\)$\n',
    r'\`define(\s+)APB_READ_DR_EXT(\s*).*(?<!\\)$\n',
    r'\`define(\s+)APB_READ_RD_EXT(\s*).*(?<!\\)$\n',
    r'\`define(\s+)APB_POLLING_DR_EXT(\s*).*(?<!\\)$\n',
    r'\`define(\s+)MR_ACCESS(\s*).*(?<!\\)$\n',
    r'\`define(\s+)POLL_RANK_REFRESH_BUSY(\s*).*(?<!\\)$\n',
    r'\`define(\s+)SET_RANK_REFRESH(\s*).*(?<!\\)$\n',
    r'\`define(\s+)DDRC_TEST_END(\s*).*(?<!\\)$\n',
    r'\`define(\s+)DDRC_TEST_PASSED(\s*).*(?<!\\)$\n',
    r'\`define(\s+)PUB_([0-9a-zA-Z]+)_DEFAULT(\s*).*(?<!\\)$\n',
    r'\`define(\s+)DX_NUM(\s*).*(?<!\\)$\n',
    r'\`define(\s+)\w*assert(\s*).*(?<!\\)$\n',
    r'\`define(\s+)\w*ASSERT(\s*).*(?<!\\)$\n',
    r'`define\s+.*\.\w+.*(?<!\\)$\n',
    r'\`define(\s+).*\{.*\}.*(?<!\\)$\n',
    r'\`define(\s+)DWC_FIRMWARE_RID_.*(?<!\\)$\n',
    r'\`define(\s+)SNPS_SVA_MSG.*(?<!\\)$\n'
]

# List of expressions that translate C files to System Verilog
C_TO_SV_CONVERT_REGEX = {
    r'\[UMCTL2_FREQUENCY_NUM'                  : '[`UMCTL2_FREQUENCY_NUM',
    r'\[UMCTL2_A_NSAR'                         : '[`UMCTL2_A_NSAR',
    r'\[UMCTL2_A_NPORTS'                       : '[`UMCTL2_A_NPORTS',
    r'\[UMCTL2_NUM_DATA_CHANNEL'               : '[`UMCTL2_NUM_DATA_CHANNEL',
    r'\[DWC_DDRCTL_NUM_CHANNEL'                : '[`DWC_DDRCTL_NUM_CHANNEL',
    r'\[DDRCTL_CINIT_MAX_DEV_NUM'              : '[`DDRCTL_CINIT_MAX_DEV_NUM',
    r'\[IME_MAX_KEY_SLOTS'                     : '[`IME_MAX_KEY_SLOTS',
    r'\[IME_MAX_REGIONS'                       : '[`IME_MAX_REGIONS',
    r'uint32_rnd_t'                            : 'rand int unsigned',
    r'uint64_rnd_t'                            : 'rand longint unsigned',
    r'uint32_t'                                : 'int unsigned',
    r'uint64_t'                                : 'longint unsigned',
    r'uint16_rnd_t'                            : 'rand shortint unsigned',
    r'uint16_t'                                : 'shortint unsigned',
    r'uint8_rnd_t'                             : 'rand byte',
    r'uint8_t'                                 : 'byte',
    r'bool_rnd_t'                              : 'rand bit',
    r'bool'                                    : 'bit',
    r'#ifdef'                                  : '`ifdef',
    r'#ifndef'                                 : '`ifndef',
    r'#endif'                                  : '`endif',
    r'#define'                                 : '`define',
    r'struct tag_(\S+)'                        : 'struct',
    r'enum tag_(\S+)'                          : 'enum',
    r'}; \/\/ fwd SubsysHdlr_t'                : '} SubsysHdlr_t;',
    r'struct (\S+)_priv'                       : 'typedef struct',
    r'^\s+dwc_ddrctl_cinit_cfg_static_t'       : 'rand dwc_ddrctl_cinit_cfg_static_t',
    r'^\s+dwc_ddrctl_cinit_cfg_qdyn_t'         : 'rand dwc_ddrctl_cinit_cfg_qdyn_t',
    r'^\s+dwc_ddrctl_cinit_cfg_dyn_t'          : 'rand dwc_ddrctl_cinit_cfg_dyn_t',
    r'^\s+ddr5_interamble_tccd_offset_t'       : 'rand ddr5_interamble_tccd_offset_t',
    r'^\s+mctl_t\s+memCtrlr_m'                 : 'rand mctl_t memCtrlr_m',
    r'^\s+lpddr4_mode_registers_t lpddr4_mr'   : 'rand lpddr4_mode_registers_t lpddr4_mr',
    r'^\s+lpddr5_mode_registers_t lpddr5_mr'   : 'rand lpddr5_mode_registers_t lpddr5_mr',
    r'^\s+ddr4_mode_registers_t ddr4_mr'       : 'rand ddr4_mode_registers_t ddr4_mr',
    r'^\s+ddr5_mode_registers_t ddr5_mr'       : 'rand ddr5_mode_registers_t ddr5_mr',
    r'^\s+ddr4_control_words_t ddr4_cw'        : 'rand ddr4_control_words_t ddr4_cw',
    r'^\s+ddr5_control_words_t ddr5_cw'        : 'rand ddr5_control_words_t ddr5_cw',
    r'^\s+ddr5_db_control_words_t\s+ddr5_db_cw': 'rand ddr5_db_control_words_t ddr5_db_cw',
    r'^\s+ddr5_rw'                             : 'rand ddr5_rw',
    r'^\s+ddr4_mr'                             : 'rand ddr4_mr',
    r'^\s+ddr5_mr'                             : 'rand ddr5_mr',
    r'^\s+lpddr4_mr'                           : 'rand lpddr4_mr',
    r'^\s+lpddr5_mr'                           : 'rand lpddr5_mr',
    r'^\s+ddr4_rc'                             : 'rand ddr4_rc',
    r'^\s+ddrSpdData_t'                        : 'rand ddrSpdData_t',
    r'void \*'                                 : 'chandle ',
    r'\b0x'                                      : '\'h',
}

# List of expressions that translate System Verilog files to C
SV_TO_C_CONVERT_REGEX = {
    r'\`define(\s+)([a-zA-Z0-9_]+)(\s*)$\n'          : '#define \g<2>\n',
    r'\`define(\s+)([a-zA-Z0-9_]+)(\s*)(\/\/)(.*)$\n': '#define \g<2>\n',
    r'\`ifdef(\s+)([a-zA-Z0-9_]+)(\s*)$\n'           : '#ifdef \g<2>\n',
    r'\`ifndef(\s+)([a-zA-Z0-9_]+)(\s*)$\n'          : '#ifndef \g<2>\n',
    r'\`elsif(\s+)([a-zA-Z0-9_]+)(\s*)$\n'           : '#elif \g<2>\n',
    r'\`undef(\s+)([a-zA-Z0-9_]+)(\s*)$\n'           : '#undef \g<2>\n',
    r'\`else.*\n'                                    : '#else\n',
    r'\`endif.*'                                     : '#endif',
}

def remove_sv_unnedded(data):
    """ Remove all the matches defined in the sv exclude table """
    for regex in SV_EXCLUDED_ELEMS_REGEX:
        data = re.sub(regex, '', data, flags=re.MULTILINE)

    return data

def remove_empty_ifdefs(data):
    """ Remove ifdef, elifs empty lines """
    data = re.sub(r'(#elif\s+?defined\s*?\(\s*?\w+?\s*?\)\s*)#elif', '#elif', data, flags=re.MULTILINE)
    data = re.sub(r'(#elif\s+?defined\s*?\(\s*?\w+?\s*?\)\s*)#else', '#else', data, flags=re.MULTILINE)
    data = re.sub(r'(#else\s*?)#endif', '#endif', data, flags=re.MULTILINE)
    data = re.sub(r'(#ifdef\s+?\w+?\s*?#endif\s*)', '', data, flags=re.MULTILINE)
    data = re.sub(r'(#ifndef\s+?\w+?\s*?#endif\s*)', '', data, flags=re.MULTILINE)
    return data

def process_multilines(data):
    """ Check if the token \ is used to join lines, if so add the present line to the next one """
    out_line = ""
    out_data = []
    data = data.splitlines()
    for line in data:
        # search for the \ token
        if re.search(r'(\\)(\s*)$', line):
            line = re.sub(r'^(\s+)', ' ', line, flags=re.MULTILINE)
            line = re.sub(r'(\s*)(\\)(\s*)', '', line, flags=re.MULTILINE)
            out_line += line
            continue
        else:
            out_line += line

        out_data.append(out_line)
        out_line = ""
    return '\n'.join(out_data)


def get_line_define_value_pair(line):
    """ Get the define macro name and value """
    define_match = re.search(r'\`define(\s+)([a-zA-Z0-9_]+)(.*)', line)
    if define_match is None:
        return None, None
    macro_name = define_match.group(2)
    macro_value = define_match.group(3)
    macro_value = re.sub(r'\`', '', macro_value)
    macro_value = re.sub(r'([0-9]+)(\'h)', '0x', macro_value)
    macro_value = re.sub(r'([0-9]+)(\'d)([0-9]+)', '\g<3>', macro_value)
    bin_value = re.search(r'(\s*)([0-9]+)(\'b)([0-1]+)', macro_value)
    while bin_value is not None:
        hex_value = hex(int(bin_value.group(4), 2)).upper().replace('X', 'x')
        macro_value = re.sub(r'(\s*)([0-9]+)(\'b)([0-1]+)', hex_value, macro_value, 1)
        bin_value = re.search(r'(\s*)([0-9]+)(\'b)([0-1]+)', macro_value)

    macro_value = re.sub(r'(\s*)(\\)(\s*)', '', macro_value, flags=re.MULTILINE)
    return macro_name, macro_value


def get_name_translations(dictionary_file):
    """ Get dictionary with the prefix, un-prefix pairs to be used in the translation """
    translations = {}
    if dictionary_file is None:
        return translations
    with open(dictionary_file, "r") as translation_stream:
        translation_data = translation_stream.read()
        translation_data = process_multilines(translation_data)

        for regex in SV_TO_C_CONVERT_REGEX:
            translation_data = re.sub(regex, SV_TO_C_CONVERT_REGEX[regex], translation_data, flags=re.MULTILINE)
        translation_data = translation_data.splitlines()

        for line in translation_data:
            # Catch all define <token> <prefix token> to create translation dict
            macro_name, macro_value = get_line_define_value_pair(line)
            if macro_name is None:
                continue
            translations[macro_value.strip()] = macro_name.strip()
    return translations


def convert_sv_to_c(dictionary_file, in_file, out_file):
    """ Convert System Verilog files to C """
    translations = get_name_translations(dictionary_file)
    with open(out_file, "w") as output:
        output.write(C_HEADER.format(file_name=os.path.splitext(os.path.basename(out_file))[0].upper()))
        line_by_line_data = []
        with open(in_file, "r") as input:
            output_data = input.read()
            output_data = process_multilines(output_data)

            for key, value in translations.items():
                output_data = re.sub(key, value, output_data, flags=re.MULTILINE)

            output_data = remove_sv_unnedded(output_data)

            for regex in SV_TO_C_CONVERT_REGEX:
               output_data = re.sub(regex, SV_TO_C_CONVERT_REGEX[regex], output_data, flags=re.MULTILINE)

            output_data = output_data.splitlines()
            for line in output_data:
                macro_name, macro_value = get_line_define_value_pair(line)
                if macro_name is None:
                    line_by_line_data.append(line)
                    continue
                line = '#define ' + macro_name + ' ' + macro_value
                line_by_line_data.append(line)

            output_data = '\n'.join(line_by_line_data)
            output_data = remove_empty_ifdefs(output_data)

            output.write("\n//Autogenerated from %s\n" % in_file)
            output.write(output_data)
        output.write(C_FOOTER.format(file_name=os.path.splitext(os.path.basename(out_file))[0].upper()))


def convert_c_to_sv(in_file, out_file):
    """ Convert C file to System Verilog """
    output_data = ""
    with open(in_file, "r") as input:
        output_data = input.read()

    for sub_regex in C_TO_SV_CONVERT_REGEX:
        output_data = re.sub(sub_regex, C_TO_SV_CONVERT_REGEX[sub_regex], output_data, flags=re.MULTILINE)

    with open(out_file, "w") as output:
        output.write(output_data)



if __name__ == "__main__":
    dict_file_path = None
    arg_parser = argparse.ArgumentParser()
    arg_parser.add_argument("-m", "--mode",         dest='mode', required=True, action="store",
                                                    type=str, help="Operate mode: c_to_sv or sv_to_c")
    arg_parser.add_argument("-i", "--input",        required=True, help="Input file")
    arg_parser.add_argument("-o", "--output",       help="Output directory")
    arg_parser.add_argument("-d", "--dictionary",   help="System verilog file with unprefix prefix pairs (DWC_ddrctl_unprefix.svh)")
    parsed_args = arg_parser.parse_args()

    # check if input file exists
    input_file_path = os.path.abspath(parsed_args.input)
    if os.path.isfile(input_file_path) is not True:
        arg_parser.error('Input file \"%s\" not found' % input_file_path)

    if parsed_args.dictionary is not None:
        if parsed_args.mode == 'c_to_sv':
            arg_parser.error('dictionary option not supported in this mode')
        dict_file_path = os.path.abspath(parsed_args.dictionary)
        if os.path.isfile(dict_file_path) is not True:
            arg_parser.error('Dictionary file \"%s\" not found' % dict_file_path)

    file_extension = '.svh' if parsed_args.mode == 'c_to_sv' else '.h'

    if parsed_args.output is not None:
        # check if output is a directory
        if os.path.isdir(parsed_args.output) is True:
            output_folder = os.path.abspath(parsed_args.output)
            output_filename = os.path.splitext(os.path.basename(input_file_path))[0] + file_extension
        else:
            output_folder, output_filename = os.path.split(os.path.abspath(parsed_args.output))
    else:
        output_folder, output_filename = os.path.split(input_file_path)
        output_filename = os.path.splitext(output_filename)[0] + file_extension

    output_file_path = os.path.join(output_folder, output_filename)

    if (parsed_args.mode == 'c_to_sv'):
        convert_c_to_sv(input_file_path, output_file_path)
    elif (parsed_args.mode == 'sv_to_c'):
        convert_sv_to_c(dict_file_path, input_file_path, output_file_path)
    else:
        print ("Invalid operation mode received: %s. Valid modes: c_to_sv or sv_to_c" % parsed_args.mode)
