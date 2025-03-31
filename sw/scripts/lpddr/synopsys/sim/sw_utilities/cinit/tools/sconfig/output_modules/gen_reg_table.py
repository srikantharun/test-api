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


# System
import os

# Local
from libconfig.types.register_block import RegisterBlockType
from libconfig.types.register  import Security
from libconfig.types.register_field  import AccessMode, ProgMode
from libconfig.lib_config import LibConfig


class GenRegistersTable():
    COPYRIGHT_HEADER =("// ------------------------------------------------------------------------------\n"
        "//\n"
        "// Copyright 2023 Synopsys, INC.\n"
        "//\n"
        "// This Synopsys IP and all associated documentation are proprietary to\n"
        "// Synopsys, Inc. and may only be used pursuant to the terms and conditions of a\n"
        "// written license agreement with Synopsys, Inc. All other use, reproduction,\n"
        "// modification, or distribution of the Synopsys IP or the associated\n"
        "// documentation is strictly prohibited.\n"
        "// Inclusivity & Diversity - Visit SolvNetPlus to read the \"Synopsys Statement on\n"
        "//            Inclusivity and Diversity\" (Refer to article 000036315 at\n"
        "//                        https://solvnetplus.synopsys.com)\n"
        "//\n"
        "// ------------------------------------------------------------------------------\n" )
    FILE_NAME_PREFIX = "ddrctl_"
    REG_NAME_PREFIX  = "reg_"
    TYPES_INCLUDE    = "#include \"ddrctl_reg_types.h\"\n"

    def __init__(self, register_map):
        """ GenRegistersTable constructor, receives a RegisterMap object """
        self.register_map       = register_map
        self.memory_map_dict    = {}
        # create a dictionary for each block types
        for block_type in RegisterBlockType:
            self.memory_map_dict[block_type] = {}

    def _get_block_type_dict(self, block_type):
        """ Returns the block registers dictionary """
        return self.memory_map_dict[block_type]

    def _is_single_inst_dualch_cfg(self):
        single_inst_dualch_cfg = LibConfig().get_config_dict().get("DDRCTL_SINGLE_INST_DUALCH")
        if (single_inst_dualch_cfg is not None) and (int(single_inst_dualch_cfg.get_value()) == 1):
            return True
        return False

    def _gen_block_type_register_files(self, block_type, output_dir):
        """ Generates the C source and header files that include all
            registers and fields of that block type """
        block_dict = self._get_block_type_dict(block_type)
        if len(block_dict) == 0:
            # emply block, nothing to do
            return
        # Create the block file name
        block_file_name = self.FILE_NAME_PREFIX + str(block_type)

        block_dir = os.path.join(output_dir, str(block_type))
        block_header_path = os.path.join(block_dir,'%s.h' % block_file_name)
        block_src_path    = os.path.join(block_dir,'%s.c' % block_file_name)

        block_header_data = ""
        block_src_data    = ""

        # create the struture representing each register in register block
        for name in sorted(block_dict.keys()):
            register = block_dict.get(name)
            if register.is_visible() is not True:
                continue
            register_name      = self.REG_NAME_PREFIX + register.get_name().lower()
            fields_offset_dict = register.get_fields_offset_dict()
            max_field_name     = register.get_max_field_name_len() + 2
            fields_str = ""
            for offset in sorted(fields_offset_dict.keys()):
                field = fields_offset_dict.get(offset)
                if field.is_visible() is False:
                    continue
                field_name  = field.get_name().lower()
                fields_str += "\t{%-*s" % (max_field_name, "\"%s\"" % field_name)
                fields_str += ", %2d" % offset
                fields_str += ", %2d" % field.get_width()
                fields_str += ", %s" % field.get_access_type()
                fields_str += ", %s},\n" % field.get_prog_mode()

            # If the register as no fields, don't create register struture
            if len(fields_str) == 0:
                continue
            # Create register end line
            fields_str += "\t{%-*s, %2d, %2d, %s, %s},\n" % (max_field_name, "NULL",
                                                             32, 32,  AccessMode.UNKNOWN, ProgMode.UNKNOWN)
            block_src_data += "const ddrctl_field_t %s[] = {\n" % register_name
            block_src_data += fields_str
            block_src_data += "};\n\n"
            block_header_data += "extern const ddrctl_field_t %s[];\n" % register_name

        self._write_source_file(block_src_path, block_src_data)
        self._write_header_file(output_dir, block_header_path, block_header_data)


    def _create_header_guard(self, file_name):
        """ Returns the header guard name for c header files """
        file_name = file_name.replace("/", "_")
        file_name = file_name.replace(".", "_")
        file_name = file_name.upper()
        return file_name

    def _create_header_head(self, file_name):
        """ Returns the file start text for c header file """
        header_guard = self._create_header_guard(file_name)
        header_guard = "#ifndef " + header_guard + "\n" + "#define " + header_guard
        return self.COPYRIGHT_HEADER + "\n" + header_guard + "\n\n" + self.TYPES_INCLUDE + "\n"

    def _create_header_end(self, file_name):
        """ Returns the end of the c header file """
        header_guard = self._create_header_guard(file_name)
        header_guard = "\n#endif /* " + header_guard + " */\n"
        return header_guard

    def _write_source_file(self, file_name, body_text):
        """ Writes the source file data to a file """
        basename = os.path.splitext(os.path.basename(file_name))[0]
        text  = self.COPYRIGHT_HEADER + "\n" + "#include \"%s.h\"\n\n" % basename
        text += body_text.expandtabs(4)
        with open(file_name, 'w') as source_file_h:
            source_file_h.write(text)

    def _write_header_file(self, output_dir, file_name, body_text):
        """ Writes the header file data to a file """
        guard_name = os.path.relpath(file_name, output_dir)
        text  = self._create_header_head(guard_name)
        text += body_text.expandtabs(4)
        text += self._create_header_end(guard_name)
        with open(file_name, 'w') as header_file_h:
            header_file_h.write(text)

    def _gen_block_src_line(self, addr, name, name_align, default, security):
        """ return a string with the register entry for the block register table """
        if name is None:
            reg_name = reg_name_struct = "NULL"
        else:
            reg_name = "\"%s\"" % name
            reg_name_struct = "%s" % (self.REG_NAME_PREFIX + name)
        block_src = "\t{0x%08x" % addr
        block_src += ", %-*s"   % (name_align + 2, reg_name)
        block_src += ", 0x%08x" % default
        block_src += ", 0x%08x" % default
        block_src += ", %s"     % security
        block_src += ", %-*s},\n" % (name_align + len(self.REG_NAME_PREFIX), reg_name_struct)
        return block_src

    def gen_ctrl_reg_map(self, ctrl_instance, output_dir):
        # create main register map file that include a structure with all register blocks
        skip_ch1_blocks = self._is_single_inst_dualch_cfg()

        reg_map_c_head = ""
        reg_map_c_body = "const ddrctl_block_t g_ddrctl%d_regmap[] = {\n" % ctrl_instance
        # iterate by each register block, add it to the main register map and create the bock files
        for addr in sorted(self.register_map.reg_block_addr_dict.keys()):
            reg_block = self.register_map.get_register_block_by_addr(addr)
            if reg_block.get_num_visible_registers() == 0:
                continue
            if not reg_block.is_supported():
                continue
            block_type      = str(reg_block.get_type())
            block_dict      = self._get_block_type_dict(reg_block.get_type())
            block_name      = reg_block.get_name().lower()
            if skip_ch1_blocks and "ch1" in block_name:
                continue
            block_inst_name = "ctrl%d_%s" % (ctrl_instance, block_name)
            block_file_name = self.FILE_NAME_PREFIX + block_inst_name

            block_type_file_name = self.FILE_NAME_PREFIX + block_type

            reg_map_c_head += "#include \"%s/%s.h\"\n" % (block_type, block_file_name)
            reg_map_c_body +="\t{0x%08x, %-17s, %-15s},\n" % \
                             (addr, "\"%s\"" % block_name, "%s" % block_inst_name)

            block_dir = os.path.join(output_dir, block_type)
            os.makedirs(block_dir, exist_ok=True)

            block_file_h_path = os.path.join(block_dir, "%s.h" % block_file_name)
            block_file_c_path = os.path.join(block_dir, "%s.c" % block_file_name)

            block_header = "\n"
            block_header += "extern ddrctl_reg_t %s[];\n" % block_inst_name

            block_src    = "#include \"%s.h\"\n" % block_type_file_name
            block_src    += "\n"
            block_src    += "ddrctl_reg_t %s[] = {\n" % block_inst_name

            reg_addr_dict = reg_block.get_registers_addr_dict()
            max_reg_name  = reg_block.get_max_reg_name_len()

            for reg_addr in sorted(reg_addr_dict.keys()):
                register = reg_block.get_register_by_addr(reg_addr)
                if register.is_visible() is False:
                    continue
                if register.get_name() not in block_dict:
                    # add register to block dictionary
                    block_dict[register.get_name()] = register
                register_name = register.get_name().lower()
                block_src += self._gen_block_src_line(addr=reg_addr, name=register_name,
                                                      name_align=max_reg_name, default=register.default,
                                                      security=register.get_security())
            # Create block end line
            block_src += self._gen_block_src_line(addr=0, name=None, name_align=max_reg_name,
                                                  default=0, security=Security.NON_SECURE)
            block_src += "};\n"
            self._write_source_file(block_file_c_path, block_src)
            self._write_header_file(output_dir, block_file_h_path, block_header)
        # Create table end line
        reg_map_c_body +="\t{0x%08x, %-17s, %-15s},\n" % (0, "%s" % "NULL", "%s" %  "NULL")
        reg_map_c_body += "};\n"
        return [reg_map_c_head, reg_map_c_body]

    def gen_c_reg_map(self, output_dir):
        """ Generates the Register map in C code on the folder provided"""

        if self._is_single_inst_dualch_cfg():
            num_ctrls = 2
        else:
            num_ctrls = 1

        reg_map_h  = "extern const ddrctl_block_t g_ddrctl0_regmap[];\n"
        reg_map_h += "extern const ddrctl_block_t g_ddrctl1_regmap[];\n"

        reg_c_head = reg_c_body = ""
        reg_c_head, ctrl0_reg_c_body = self.gen_ctrl_reg_map(0, output_dir)

        for ctrl in range(num_ctrls):
            aux_reg_c_head, aux_reg_c_body = self.gen_ctrl_reg_map(ctrl, output_dir)
            reg_c_head += aux_reg_c_head
            reg_c_body += aux_reg_c_body
        
        if num_ctrls == 1:
            reg_c_body += "const ddrctl_block_t g_ddrctl1_regmap[] = \t{{0x%08x, %-17s, %-15s}};\n" % (0, "%s" % "NULL", "%s" %  "NULL")
    
        reg_map_c = reg_c_head + "\n\n" + reg_c_body

        self._write_source_file(os.path.join(output_dir, self.FILE_NAME_PREFIX + 'regmap_table.c'), reg_map_c)
        self._write_header_file(output_dir, os.path.join(output_dir, self.FILE_NAME_PREFIX + 'regmap_table.h'), reg_map_h)
        # Write the blocks registers
        for block in RegisterBlockType:
            self._gen_block_type_register_files(block, output_dir)

