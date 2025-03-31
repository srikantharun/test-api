// ------------------------------------------------------------------------------
// 
// Copyright 2024 Synopsys, INC.
// 
// This Synopsys IP and all associated documentation are proprietary to
// Synopsys, Inc. and may only be used pursuant to the terms and conditions of a
// written license agreement with Synopsys, Inc. All other use, reproduction,
// modification, or distribution of the Synopsys IP or the associated
// documentation is strictly prohibited.
// Inclusivity & Diversity - Visit SolvNetPlus to read the "Synopsys Statement on
//            Inclusivity and Diversity" (Refer to article 000036315 at
//                        https://solvnetplus.synopsys.com)
// 
// Component Name   : DWC_ddrctl_lpddr54
// Component Version: 1.60a-lca00
// Release Type     : LCA
// Build ID         : 0.0.0.0.TreMctl_302.DwsDdrChip_8.26.6.DwsDdrctlTop_5.12.7
// ------------------------------------------------------------------------------

#include "ddrctl_regmap.h"
#include "dwc_cinit_bsp.h"
#include "dwc_cinit_utils.h"
#include "regmap/ddrctl_regmap_table.h"
#include "dwc_cinit_log.h"

#define CTRL_INSTANCE_MAX       2
#define DDRCLT_MAX_ADDR_SPACE   0xFFFFFF

static uint64_t s_ddrctl_base_addr[CTRL_INSTANCE_MAX] = { 0, 0};

/**
 * @brief Struct to define the register operation
 */
typedef enum ddrctl_reg_op_e {
    DDRCLT_REG_OP_READ,
    DDRCLT_REG_OP_WRITE,
} ddrctl_reg_op_t;


/**
 * @brief Static inline function to calculate a field mask
 * 
 * @param width     field width
 * @param offset    field offset
 * @return uint32_t mask
 */
static inline uint32_t _get_mask(uint8_t width, uint8_t offset)
{
    if (width == 32) {
        return 0xFFFFFFFF;
    }
    return ((1 << width) - 1) << offset;
}

/**
 * @brief Static function to search a field on the register by name
 *
 * @param name                      field name string
 * @param fields                    table of fields in the register
 * @return const ddrctl_field_t*    return pointer to the field structure or NULL if not found
 */
static inline const ddrctl_field_t * _get_field_by_name(const char *name,
                                                        const ddrctl_field_t * fields)
{
    uint16_t index;
    uint16_t field_name_len;

    field_name_len = strlen(name);

    for (index = 0; fields[index].name != NULL; index++) {
        if (strlen(fields[index].name) != field_name_len) {
            continue;
        }

        if (strncasecmp(name, fields[index].name, field_name_len) == 0) {
            return &(fields[index]);
        }
    }
    return NULL;
}


/**
 * @brief Static function to search a register on the register block by name
 *
 * @param name                  register + field name string
 * @param regs                  table of register in the block
 * @return const ddrctl_reg_t*  return pointer to the register structure or NULL if not found
 */
static inline ddrctl_reg_t * _get_reg_by_name_from_block(const char *name, ddrctl_reg_t *regs)
{
    uint16_t index;
    uint16_t reg_name_len;
    uint16_t max_match_len;
    ddrctl_reg_t *best_match;

    best_match    = NULL;
    max_match_len = 0;
    index         = 0;

    while (regs[index].name != NULL) {
        reg_name_len = strlen(regs[index].name);
        if (strncasecmp(name, regs[index].name, reg_name_len) == 0) {
            if (max_match_len < reg_name_len) {
                max_match_len = reg_name_len;
                best_match = &(regs[index]);
            }
        }
        index++;
    }
    return best_match;
}


/**
 * @brief Static function to search for a field based on the full
 *        name and do a read or write operation
 *
 * @param full_name         Full name of the field, includes from register block to field name
 * @param op                Operation, Read/Write
 * @param in_out            data, return value in read, write value in write operation
 * @return ddrctl_error_t   DDRCTL_SUCCESS or DDRCTL_PARAM_ERROR
 */
static inline ddrctl_error_t _operation_on_field_by_name(const char *full_name, ddrctl_reg_op_t op,
                                                         uint32_t *in_out)
{
    uint32_t                mask;
    uint16_t                index;
    uint16_t                block_name_len;
    uint16_t                reg_name_len;
    const char              *reg_name;
    const char              *field_name;
    uint16_t                max_match_len;
    int16_t                 best_match;
    ddrctl_reg_t            *reg;
    const ddrctl_field_t    *field;
    char                    aux_full_name[250];
    char                    *block_ch_str;
    const ddrctl_block_t    *inst_reg_map;

    field         = NULL;
    best_match    = -1;
    max_match_len = 0;

    // Point the table to the first controller, expected case for must requests
    inst_reg_map = g_ddrctl0_regmap;
    strncpy(aux_full_name, full_name, sizeof(aux_full_name));

    if (g_ddrctl1_regmap[0].name != NULL) {
        block_ch_str = strstr(aux_full_name, "CH1");
        if (block_ch_str != NULL) {
            block_ch_str[2] = '0'; // replace the 1 to 0
            // Point the table to the second controller, for channel 1 register
            // on DDRCTL_SINGLE_INST_DUALCH configurations
            inst_reg_map = g_ddrctl1_regmap;
        }
    } 

    for (index = 0; inst_reg_map[index].name != NULL; index++) {
        block_name_len = strlen(inst_reg_map[index].name);
        if (strncasecmp(aux_full_name, inst_reg_map[index].name, block_name_len) != 0) {
            continue;
        }

        if (strlen(aux_full_name) <= block_name_len) {
            SNPS_ERROR("Invalid field name: %s\n", aux_full_name);
            break;
        }

        if (max_match_len < block_name_len) {
            max_match_len = block_name_len;
            best_match    = index;
        }
    }

    if (best_match < 0) {
        return DDRCTL_PARAM_ERROR;
    }

    reg_name = &(full_name[max_match_len + 1]);
    reg      = _get_reg_by_name_from_block(reg_name, inst_reg_map[best_match].reg_table);
    if (NULL == reg) {
        return DDRCTL_PARAM_ERROR;
    }

    reg_name_len = strlen(reg->name);
    field_name   = &(reg_name[reg_name_len + 1]);
    field        = _get_field_by_name(field_name, reg->field_table);
    if (NULL == field) {
        return DDRCTL_PARAM_ERROR;
    }

    mask = _get_mask(field->width, field->offset); 

    if (DDRCLT_REG_OP_READ == op) {
        *in_out = SNPS_READ_EXPLICIT_FIELD(reg->value, field->offset, mask);
    } else {
        SNPS_WRITE_EXPLICIT_FIELD(reg->value, field->offset, mask, *in_out);
    }

    return DDRCTL_SUCCESS;
}


/**
 * @brief Reads to a register field using the complete name.
 *        String with register block, register and field
 *
 * @deprecated Will be removed as soon all call from testbench are removed
 *
 * @param full_name         Full name of the field, includes from register block to field name
 * @param value             Read value
 * @return ddrctl_error_t   DDRCTL_SUCCESS or DDRCTL_PARAM_ERROR
 */
ddrctl_error_t ddrctl_regmap_read_field_by_fullname(const char *full_name, uint32_t *value)
{
    return _operation_on_field_by_name(full_name, DDRCLT_REG_OP_READ, value);
}


/**
 * @brief Writes to a register field using the complete name.
 *        String with register block, register and field
 *
 * @deprecated Will be removed as soon all call from testbench are removed
 *
 * @param full_name         Full name of the field, includes from register block to field name
 * @param value             Value to write
 * @return ddrctl_error_t   DDRCTL_SUCCESS or DDRCTL_PARAM_ERROR
 */
ddrctl_error_t ddrctl_regmap_write_field_by_fullname(const char *full_name, uint32_t value)
{
    return _operation_on_field_by_name(full_name, DDRCLT_REG_OP_WRITE, &value);
}


/**
 * @brief Static function to search a register on the register block by name
 *
 * @param name                  register name string
 * @param regs                  table of register in the block
 * @return const ddrctl_reg_t*  return pointer to the register structure or NULL if not found
 */
static inline ddrctl_reg_t * _get_reg_by_name(const char *reg_name, ddrctl_reg_t *regs)
{
    uint16_t index;
    uint16_t reg_name_len;

    reg_name_len = strlen(reg_name);

    for (index = 0; regs[index].name != NULL; index++) {
        if (strlen(regs[index].name) != reg_name_len) {
            continue;
        }
        if (strncasecmp(reg_name, regs[index].name, reg_name_len) == 0) {
            return &(regs[index]);
        }
    }

    return NULL;
}


/**
 * @brief Static function to search for a field based on the full
 *        name and do a read or write operation
 *
 * @param full_name         Full name of the field, includes from register block to field name
 * @param op                Operation, Read/Write
 * @param in_out            data, return value in read, write value in write operation
 * @return ddrctl_error_t   DDRCTL_SUCCESS or DDRCTL_PARAM_ERROR
 */
static inline ddrctl_error_t _operation_on_field(const char *block_name, const char *reg_name,
                                                 const char *field_name, ddrctl_reg_op_t op,
                                                 uint32_t *in_out)
{
    uint32_t                mask;
    uint16_t                index;
    uint16_t                block_name_len;
    ddrctl_reg_t            *reg;
    const ddrctl_field_t    *field;
    const ddrctl_block_t    *inst_reg_map;
    char                    *block_ch_str;
    char                    aux_block_name[50];

    // Point the table to the first controller, expected case for must requests
    inst_reg_map = g_ddrctl0_regmap;

    strncpy(aux_block_name, block_name, sizeof(aux_block_name));

    if (g_ddrctl1_regmap[0].name != NULL) {
        block_ch_str = strstr(aux_block_name, "CH1");
        if (block_ch_str != NULL) {
            block_ch_str[2] = '0'; // replace the 1 to 0
            // Point the table to the second controller, for channel 1 register
            // on DDRCTL_SINGLE_INST_DUALCH configurations
            inst_reg_map = g_ddrctl1_regmap;
        }
    } 

    block_name_len = strlen(aux_block_name);

    for (index = 0; inst_reg_map[index].name != NULL; index++) {
        if (strlen(inst_reg_map[index].name) != block_name_len) {
            continue;
        }

        if (strncasecmp(aux_block_name, inst_reg_map[index].name, block_name_len) == 0) {
            break;
        }
    }

    if (inst_reg_map[index].name == NULL) {
        return DDRCTL_PARAM_ERROR;
    }

    reg = _get_reg_by_name(reg_name, inst_reg_map[index].reg_table);
    if (NULL == reg) {
        return DDRCTL_PARAM_ERROR;
    }

    field = _get_field_by_name(field_name, reg->field_table);
    if (NULL == field) {
        return DDRCTL_PARAM_ERROR;
    }

    mask = _get_mask(field->width, field->offset); 

    if (DDRCLT_REG_OP_READ == op) {
        *in_out = SNPS_READ_EXPLICIT_FIELD(reg->value, field->offset, mask);
    } else {
        SNPS_WRITE_EXPLICIT_FIELD(reg->value, field->offset, mask, *in_out);
    }

    return DDRCTL_SUCCESS;
}


/**
 * @brief Reads the register field
 *
 * @param block_name        Block name
 * @param register_name     Register name
 * @param field_name        Field name
 * @param value             value readed
 * @return ddrctl_error_t   DDRCTL_SUCCESS or DDRCTL_PARAM_ERROR
 */
ddrctl_error_t ddrctl_regmap_read_field(const char *block, const char *reg,
                                 const char *field, uint32_t *value)
{
    return _operation_on_field(block, reg, field, DDRCLT_REG_OP_READ, value);
}


/**
 * @brief Writes the register field
 *
 * @param block_name        Block name
 * @param register_name     Register name
 * @param field_name        Field name
 * @param value             value to write
 * @return ddrctl_error_t   DDRCTL_SUCCESS or DDRCTL_PARAM_ERROR
 */
ddrctl_error_t ddrctl_regmap_write_field(const char *block, const char *reg,
                                  const char *field, uint32_t value)
{
    return _operation_on_field(block, reg, field, DDRCLT_REG_OP_WRITE, &value);
}


/**
 * @brief Static function to search the register by the address
 *
 * @param addr              register address
 * @return ddrctl_reg_t*    register sctucture or NULL is not register found
 */
static inline ddrctl_reg_t * _get_reg_by_addr(uint64_t addr)
{
    uint16_t              index;
    uint16_t              next_index;
    ddrctl_reg_t         *block_regs;
    const ddrctl_block_t *inst_reg_map;
    uint64_t              addr_offset;

    addr_offset = addr - s_ddrctl_base_addr[0];
    if (addr_offset < DDRCLT_MAX_ADDR_SPACE) {
        inst_reg_map = g_ddrctl0_regmap;
    } else {
        addr_offset = addr - s_ddrctl_base_addr[1];
        inst_reg_map = g_ddrctl1_regmap;
    }

    for (next_index = 1; inst_reg_map[next_index].name != NULL; next_index++) {
        if (addr_offset < inst_reg_map[next_index].addr) {
            break;
        }
    }

    index = next_index - 1;
    if (inst_reg_map[index].name == NULL) {
        return NULL;
    }

    block_regs = inst_reg_map[index].reg_table;

    for (index = 0; block_regs[index].name != NULL; index++) {
        if (addr_offset == block_regs[index].addr) {
            return &(block_regs[index]);
        }
    }
    return NULL;
}


/**
 * @brief Read register value
 *
 * @param addr              register address
 * @param value             variable that will store the read value
 * @return ddrctl_error_t   DDRCTL_SUCCESS or DDRCTL_ENTRY_NOT_FOUND if register not found
 */
ddrctl_error_t ddrctl_regmap_read(uint64_t addr, uint32_t *value)
{
    const ddrctl_reg_t  *reg;

    reg = _get_reg_by_addr(addr);
    if (NULL == reg) {
        return DDRCTL_ENTRY_NOT_FOUND;
    }
    *value = reg->value;
    return DDRCTL_SUCCESS;
}


/**
 * @brief Write register value
 *
 * @param addr              register address
 * @param value             value to write
 * @return ddrctl_error_t   DDRCTL_SUCCESS or DDRCTL_ENTRY_NOT_FOUND if register not found
 */
ddrctl_error_t ddrctl_regmap_write(uint64_t addr, uint32_t value)
{
    ddrctl_reg_t  *reg;

    reg = _get_reg_by_addr(addr);
    if (NULL == reg) {
        return DDRCTL_ENTRY_NOT_FOUND;
    }

    if (reg->value != value) {
        SNPS_INFO("Write IO address(0x%.8x) = 0x%.8x", addr, value);
        SNPS_LOG_REG_WRITE_SEQ(addr, value);
    }

    reg->value = value;
    return DDRCTL_SUCCESS;
}


/**
 * @brief static to set the register values to the reset value again
 * 
 * @param inst_reg_map 
 */
static inline void _regmap_reset(const ddrctl_block_t *inst_reg_map)
{
    uint16_t            block_id;
    uint16_t            reg_id;
    ddrctl_reg_t       *reg_block;

    for (block_id = 0; inst_reg_map[block_id].name != NULL; block_id++) {
        reg_block = inst_reg_map[block_id].reg_table;
        for (reg_id = 0; reg_block[reg_id].name != NULL; reg_id++) {
            reg_block[reg_id].value = reg_block[reg_id].reset_value;
        }
    }
}


/**
 * @brief Sets the register values to the reset value again
 * 
 */
void ddrctl_regmap_reset()
{
    SNPS_INFO("Regmap Reset");
    _regmap_reset(g_ddrctl0_regmap);

    if (g_ddrctl1_regmap[0].name != NULL) {
        _regmap_reset(g_ddrctl1_regmap);
    }
}


/**
 * @brief Returns the register secure access mode
 *
 * @param addr              register address
 * @param mode              secure access mode
 * @return ddrctl_error_t   DDRCTL_SUCCESS or DDRCTL_ENTRY_NOT_FOUND if register not found
 */
ddrctl_error_t ddrctl_regmap_get_register_security(uint64_t addr, ddrctl_security_t *mode)
{
    const ddrctl_reg_t  *reg;

    reg = _get_reg_by_addr(addr);
    if (NULL == reg) {
        return DDRCTL_ENTRY_NOT_FOUND;
    }
    *mode = reg->security;
    return DDRCTL_SUCCESS;
}


/**
 * @brief static function to print a register fields
 *
 * @param fields        pointer to the register fields table
 * @param reg_value     register value
 */
static void _print_register(const ddrctl_field_t * fields, uint32_t reg_value)
{
    uint16_t index;
    uint16_t name_len;
    uint32_t mask;
    uint32_t field_value;

    for (index = 0; fields[index].name != NULL; index++) {
        mask = _get_mask(fields[index].width, fields[index].offset); 
        field_value = SNPS_READ_EXPLICIT_FIELD(reg_value, fields[index].offset, mask);
        SNPS_REGMAP_INFO("\t\t%s = 0x%x", fields[index].name, field_value);
    }
}


/**
 * @brief static function to print the register block registers
 *
 * @param reg_block     pointer to the registers table
 * @param show_fields   DDRCTL_TRUE prints the fields also, DDRCTL_FALSE only prints registers
 */
static void _print_register_block(const char *block_name, const ddrctl_reg_t *reg_block,
                                  ddrctl_bool_t show_fields)
{
    uint16_t index;

    for (index = 0; reg_block[index].name != NULL; index++) {
        SNPS_REGMAP_INFO("%s.%-30s| 0x%08x = 0x%08x", block_name, reg_block[index].name,
                         reg_block[index].addr, reg_block[index].value);
        if (DDRCTL_TRUE == show_fields) {
            _print_register(reg_block[index].field_table, reg_block[index].value);
        }
    }
}



static inline void _sw_print_ctrl_regmap(const ddrctl_block_t *inst_reg_map, ddrctl_bool_t show_fields)
{
    uint16_t            index;

    for (index = 0; inst_reg_map[index].name != NULL; index++) {
        _print_register_block(inst_reg_map[index].name,
                              inst_reg_map[index].reg_table, show_fields);
    }
}

/**
 * @brief Function to print the memory map
 *
 * @param show_fields   DDRCTL_TRUE prints registers and fields
 *                      DDRCTL_FALSE only prints registers
 */
void ddrctl_regmap_print_regmap(ddrctl_bool_t show_fields)
{
    if (g_ddrctl1_regmap[0].name != NULL) {
        SNPS_REGMAP_INFO("Controller 0");
    }
    _sw_print_ctrl_regmap(g_ddrctl0_regmap, show_fields);

    if (g_ddrctl1_regmap[0].name != NULL) {
        SNPS_REGMAP_INFO("Controller 1");
        _sw_print_ctrl_regmap(g_ddrctl1_regmap, show_fields);
    }
}


/**
 * @brief Function to update the controller instance base address
 * 
 * @param ctrl_inst_id      controller instance ID
 * @param base_addr         base address
 */
void ddrctl_set_base_addr(uint8_t ctrl_inst_id, uint64_t base_addr)
{
    s_ddrctl_base_addr[ctrl_inst_id] = base_addr;
}
