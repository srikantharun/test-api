### AIC

### APU

|Interface Name|Width|dir|connected to|comment|
|--------------|-----|---|------------|-------|
|i_core_nmi| 8 | I |  | Core NMI IRQs |
|i_apu_irq | 128 | I | | External IRQs to APU |
|o_apu_irq | 64 | O | | |
|o_reset_vector_ai_core_0| 40 | O | | Reset Vector Address going to AIC-0 RISC-V, indicates boot address after reset |
|o_reset_vector_ai_core_1| 40 | O | | Reset Vector Address going to AIC-1 RISC-V, indicates boot address after reset |
|o_reset_vector_ai_core_2| 40 | O | | Reset Vector Address going to AIC-2 RISC-V, indicates boot address after reset |
|o_reset_vector_ai_core_3| 40 | O | | Reset Vector Address going to AIC-3 RISC-V, indicates boot address after reset |
|o_reset_vector_ai_core_4| 40 | O | | Reset Vector Address going to AIC-4 RISC-V, indicates boot address after reset |
|o_reset_vector_ai_core_5| 40 | O | | Reset Vector Address going to AIC-5 RISC-V, indicates boot address after reset |
|o_reset_vector_ai_core_6| 40 | O | | Reset Vector Address going to AIC-6 RISC-V, indicates boot address after reset |
|o_reset_vector_ai_core_7| 40 | O | | Reset Vector Address going to AIC-7 RISC-V, indicates boot address after reset |
|o_noc_ctrl_bus| 32 | O | | NoC Configruation control signals |


### DECODER

|Interface Name|Width|dir|connected to|comment|
|--------------|-----|---|------------|-------|
|o_mcu_int_next | 1 | O | |  |
|i_mcu_ack_next | 1 | I | |  |
|i_mcu_int_prev | 1 | I | | |
|o_mcu_ack_prev | 1 | O | | |
|o_pintreq | 1 | O | | |
|o_pintbus | 32 | O | | |

### L2 module

|Interface Name|Width|dir|connected to|comment|
|--------------|-----|---|------------|-------|
| i_ret | 1 | I ||  Memory PG Enable signals |
| i_pde | 1 | I ||  Memory PG Enable signals |
| o_prn | 1 | O ||  Memory PG Enable signals |
| i_mcs | 2 | I |||
| i_mcsw | 1 | I |||
| i_adme | 3 | I |||
| i_cg_bypass | 1 | I | | |

### LPDDR

### NOC

### PCIE

### PVE

|Interface Name|Width|dir|connected to|comment|
|--------------|-----|---|------------|-------|
| i_timer_irq | 8 | I ||  timer IRQs |
| i_hart_base | 10 | I ||   |


### SOC MGMT

|Interface Name|Width|dir|connected to|comment|
|--------------|-----|---|------------|-------|
| o_soc_mgmt_irq | 8 | O ||  Memory PG Enable signals |


### SOC PERIPH

|Interface Name|Width|dir|connected to|comment|
|--------------|-----|---|------------|-------|
|  |  |  ||   |


### SOC SPM



