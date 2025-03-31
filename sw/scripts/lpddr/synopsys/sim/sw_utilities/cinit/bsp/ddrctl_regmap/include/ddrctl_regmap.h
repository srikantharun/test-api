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


#ifndef CINIT_BSP_DDRCTRL_INCLUDE_DDRCTRL_REG_MAP_H_
#define CINIT_BSP_DDRCTRL_INCLUDE_DDRCTRL_REG_MAP_H_

#include "ddrctl_reg_types.h"
#include "dwc_cinit_log.h"


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
ddrctl_error_t ddrctl_regmap_read_field_by_fullname(const char *full_name, uint32_t *value);


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
ddrctl_error_t ddrctl_regmap_write_field_by_fullname(const char *full_name, uint32_t value);


/**
 * @brief Reads the register field
 *
 * @param block_name        Block name
 * @param register_name     Register name
 * @param field_name        Field name
 * @param value             value readed
 * @return ddrctl_error_t   DDRCTL_SUCCESS or DDRCTL_PARAM_ERROR
 */
ddrctl_error_t ddrctl_regmap_read_field(const char *block_name, const char *register_name,
                                    const char *field_name, uint32_t *value);


/**
 * @brief Writes the register field
 *
 * @param block_name        Block name
 * @param register_name     Register name
 * @param field_name        Field name
 * @param value             value to write
 * @return ddrctl_error_t   DDRCTL_SUCCESS or DDRCTL_PARAM_ERROR
 */
ddrctl_error_t ddrctl_regmap_write_field(const char *block_name, const char *register_name,
                                     const char *field_name, uint32_t value);


/**
 * @brief Read register value
 *
 * @param addr              register address
 * @param value             variable that will store the read value
 * @return ddrctl_error_t   DDRCTL_SUCCESS or DDRCTL_ENTRY_NOT_FOUND if register not found
 */
ddrctl_error_t ddrctl_regmap_read(uint64_t addr, uint32_t *value);


/**
 * @brief Write register value
 *
 * @param addr              register address
 * @param value             value to write
 * @return ddrctl_error_t   DDRCTL_SUCCESS or DDRCTL_ENTRY_NOT_FOUND if register not found
 */
ddrctl_error_t ddrctl_regmap_write(uint64_t addr, uint32_t value);


/**
 * @brief Sets the register values to the reset value again
 * 
 */
void ddrctl_regmap_reset();


/**
 * @brief Returns the register secure access mode
 *
 * @param addr              register address
 * @param mode              secure access mode
 * @return ddrctl_error_t   DDRCTL_SUCCESS or DDRCTL_ENTRY_NOT_FOUND if register not found
 */
ddrctl_error_t ddrctl_regmap_get_register_security(uint64_t addr, ddrctl_security_t *mode);


/**
 * @brief Function to print the memory map
 *
 * @param show_fields   DDRCTL_TRUE prints registers and fields
 *                      DDRCTL_FALSE only prints registers
 */
void ddrctl_regmap_print_regmap(ddrctl_bool_t show_fields);


/**
 * @brief Function to update the controller instance base address
 * 
 * @param ctrl_inst_id      controller instance ID
 * @param base_addr         base address
 */
void ddrctl_set_base_addr(uint8_t ctrl_inst_id, uint64_t base_addr);

#endif /* CINIT_BSP_DDRCTRL_INCLUDE_DDRCTRL_REG_MAP_H_ */
