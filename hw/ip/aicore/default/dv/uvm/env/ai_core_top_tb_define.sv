//Defines///////////////////////////
`define AXI_LP_ADDR_WIDTH 40
`define AXI_LP_DATA_WIDTH 64
`define AXI_STREAM_IFDW_DATA_WIDTH 512
`define AXI_STREAM_IFD0_DATA_WIDTH 512
`define AXI_STREAM_IAU_DATA_WIDTH 1664
`define AXI_TRANSACTION_BURST_SIZE_8 0
`define AXI_TRANSACTION_BURST_SIZE_16 1
`define AXI_TRANSACTION_BURST_SIZE_32 2
`define AXI_TRANSACTION_BURST_SIZE_64 3
`define AXI_TRANSACTION_BURST_FIXED 0
`define AXI_TRANSACTION_BURST_INCR 1
`define AXI_TRANSACTION_BURST_WRAP 2
`define AXI_OKAY_RESPONSE 0
`define AXI_EXOKAY_RESPONSE 1
`define AXI_SLVERR_RESPONSE 2
`define AXI_DECERR_RESPONSE 3
`define MVM_CSR_START_ADDR 28'h009_0000
`define MVM_EXE_CMDB_START_ADDR 28'h009_1000
`define MVM_EXE_SWDP_CMDB_START_ADDR 28'h009_2000
`define MVM_EXE_QCMD_START_ADDR 28'h009_8000
`define MVM_PRG_CMDB_START_ADDR 28'h00A_1000
`define MVM_PRG_SWDP_CMDB_START_ADDR 28'h00A_2000
`define MVM_CSR_END_ADDR 28'h009_0FFF
`define MVM_EXE_CMDB_END_ADDR 28'h009_1FFF
`define MVM_EXE_SWDP_CMDB_END_ADDR 28'h009_7FFF
`define MVM_EXE_QCMD_END_ADDR 28'h009_8FFF
`define MVM_PRG_CMDB_END_ADDR 28'h00A_1FFF
`define MVM_PRG_SWDP_CMDB_END_ADDR 28'h00A_7FFF
`define QCMD_DEPTH 256
`define PWORD_SIZE 512
`define WEIGHT_SETS 4
`define IMC_ROWS 512
`define IMC_COLUMN 512
`define MATRIX 64

 `define AI_CORE_DMA_NUM_CHANNELS 1

// Triton memory map start addresses
// Based on https://git.axelera.ai/ai-hw-team/triton/-/blob/main/src/data/triton_memory_map.csv

//`define AI_CORE_BASE_ADDR       ('h1000_0000 * m_env_cfg.ai_core_cid) 
`define AI_CORE_BASE_ADDR       ('h1000_0000)

`define AI_CORE_0_BASE_ADDR     ('h1000_0000)
`define AI_CORE_1_BASE_ADDR     ('h2000_0000)
`define AI_CORE_2_BASE_ADDR     ('h3000_0000)
`define AI_CORE_3_BASE_ADDR     ('h4000_0000)

//SYSTEM CTRL
`define SYSTEM_CTRL_BOOT_ROM_START_ADDR              36'h001_0000
`define SYSTEM_CTRL_BOOT_ROM_END_ADDR                36'h001_FFFF
`define SYSTEM_CTRL_PVT_START_ADDR                   36'h002_0000
`define SYSTEM_CTRL_PVT_END_ADDR                     36'h002_FFFF
`define SYSTEM_CTRL_PAD_CTRL_START_ADDR              36'h003_0000
`define SYSTEM_CTRL_PAD_CTRL_END_ADDR                36'h003_FFFF
`define SYSTEM_CTRL_SMU_START_ADDR                   36'h004_0000
`define SYSTEM_CTRL_SMU_END_ADDR                     36'h004_FFFF
`define SYSTEM_CTRL_CLK_GEN_START_ADDR               36'h005_0000
`define SYSTEM_CTRL_CLK_GEN_END_ADDR                 36'h005_FFFF
`define SYSTEM_CTRL_RESET_CTRL_START_ADDR            36'h006_0000
`define SYSTEM_CTRL_RESET_CTRL_END_ADDR              36'h006_FFFF
`define SYSTEM_CTRL_GPIO_START_ADDR                  36'h007_0000
`define SYSTEM_CTRL_GPIO_END_ADDR                    36'h007_FFFF
`define SYSTEM_CTRL_UART_START_ADDR                  36'h008_0000
`define SYSTEM_CTRL_UART_END_ADDR                    36'h008_FFFF
`define SYSTEM_CTRL_I2C0_START_ADDR                  36'h009_0000
`define SYSTEM_CTRL_I2C0_END_ADDR                    36'h009_FFFF
`define SYSTEM_CTRL_I2C1_START_ADDR                  36'h00A_8000
`define SYSTEM_CTRL_I2C1_END_ADDR                    36'h00A_FFFF
`define SYSTEM_CTRL_MBIST_START_ADDR                 36'h00B_0000
`define SYSTEM_CTRL_MBIST_END_ADDR                   36'h00B_FFFF
`define SYSTEM_CTRL_TIMER_START_ADDR                 36'h00C_0000
`define SYSTEM_CTRL_TIMER_END_ADDR                   36'h00C_FFFF
`define SYSTEM_CTRL_SPI_M_START_ADDR                 36'h00D_0000
`define SYSTEM_CTRL_SPI_M_END_ADDR                   36'h00D_FFFF
`define SYSTEM_CTRL_WATCHDOG_TIMER_START_ADDR        36'h00E_0000
`define SYSTEM_CTRL_WATCHDOG_TIMER_END_ADDR          36'h00E_FFFF
`define SYSTEM_CTRL_RTC_START_ADDR                   36'h00F_0000
`define SYSTEM_CTRL_RTC_END_ADDR                     36'h00F_FFFF
`define SYSTEM_CTRL_CRYPTOMASTER_START_ADDR          36'h010_0000
`define SYSTEM_CTRL_CRYPTOMASTER_END_ADDR            36'h010_FFFF
`define SYSTEM_CTRL_AHB_ARBITER1_START_ADDR          36'h020_0000
`define SYSTEM_CTRL_AHB_ARBITER1_END_ADDR            36'h020_FFFF
`define SYSTEM_CTRL_ESECURE_START_ADDR               36'h021_0000
`define SYSTEM_CTRL_ESECURE_END_ADDR                 36'h021_FFFF
`define SYSTEM_CTRL_CLINT_START_ADDR                 36'h022_0000
`define SYSTEM_CTRL_CLINT_END_ADDR                   36'h022_FFFF
`define SYSTEM_CTRL_AHB_ARBITER2_START_ADDR          36'h030_0000
`define SYSTEM_CTRL_AHB_ARBITER2_END_ADDR            36'h031_FFFF
`define SYSTEM_CTRL_DMA_START_ADDR                   36'h032_0000
`define SYSTEM_CTRL_DMA_END_ADDR                     36'h032_FFFF
`define SYSTEM_CTRL_ARBITER_START_ADDR               36'h033_0000
`define SYSTEM_CTRL_ARBITER_END_ADDR                 36'h033_FFFF
`define SYSTEM_SPM_MEM_START_ADDR                    40'h700_0000
`define SYSTEM_SPM_MEM_END_ADDR                      40'h77F_FFFF
`define SYSTEM_CTRL_ILM_MEM_START_ADDR               36'h090_0000
`define SYSTEM_CTRL_ILM_MEM_END_ADDR                 36'h090_7FFF
`define SYSTEM_CTRL_DLM_MEM_START_ADDR               36'h0A0_0000
`define SYSTEM_CTRL_DLM_MEM_END_ADDR                 36'h0A0_FFFF
`define SYSTEM_CTRL_MAILBOX0_START_ADDR              36'h101_0000
`define SYSTEM_CTRL_MAILBOX0_END_ADDR                36'h101_FFFF
`define SYSTEM_CTRL_DEBUG_START_ADDR                 36'h102_0000
`define SYSTEM_CTRL_DEBUG_END_ADDR                   36'h102_FFFF
`define SYSTEM_CTRL_PLIC_START_ADDR                  36'h200_0000
`define SYSTEM_CTRL_PLIC_END_ADDR                    36'h23F_FFFF
`define SYSTEM_CTRL_SW_PLIC_START_ADDR               36'h240_0000
`define SYSTEM_CTRL_SW_PLIC_END_ADDR                 36'h27F_FFFF
`define SYSTEM_CTRL_PCIE_DBI_SLAVE_START_ADDR        36'h400_0000
`define SYSTEM_CTRL_PCIE_DBI_SLAVE_END_ADDR          36'h43F_FFFF
`define SYSTEM_CTRL_PCIE_PHY_CFG_START_ADDR          36'h440_0000
`define SYSTEM_CTRL_PCIE_PHY_CFG_END_ADDR            36'h443_FFFF
`define SYSTEM_CTRL_FIREWALL_SERVICE_NW_START_ADDR   36'h444_0000
`define SYSTEM_CTRL_FIREWALL_SERVICE_NW_END_ADDR     36'h444_FFFF
`define SYSTEM_CTRL_OBSERVER_SERVICE_START_ADDR      36'h445_0000
`define SYSTEM_CTRL_OBSERVER_SERVICE_END_ADDR        36'h445_FFFF
`define SYSTEM_CTRL_RESERVED_SOC_PERIPH_START_ADDR   36'h446_0000
`define SYSTEM_CTRL_RESERVED_SOC_PERIPH_END_ADDR     36'h7FF_FFFF

// L2 memory modules
`define L2_MODULE0_MEM_START_ADDR                    40'h0800_0000
`define L2_MODULE0_MEM_END_ADDR                      40'h08FF_FFFF
`define L2_MODULE1_MEM_START_ADDR                    40'h0900_0000
`define L2_MODULE1_MEM_END_ADDR                      40'h09FF_FFFF
`define L2_MODULE2_MEM_START_ADDR                    40'h0A00_0000
`define L2_MODULE2_MEM_END_ADDR                      40'h0AFF_FFFF
`define L2_MODULE3_MEM_START_ADDR                    40'h0B00_0000
`define L2_MODULE3_MEM_END_ADDR                      40'h0BFF_FFFF
`define L2_MODULE4_MEM_START_ADDR                    40'h0C00_0000
`define L2_MODULE4_MEM_END_ADDR                      40'h0CFF_FFFF
`define L2_MODULE5_MEM_START_ADDR                    40'h0D00_0000
`define L2_MODULE5_MEM_END_ADDR                      40'h0DFF_FFFF
`define L2_MODULE6_MEM_START_ADDR                    40'h0E00_0000
`define L2_MODULE6_MEM_END_ADDR                      40'h0EFF_FFFF
`define L2_MODULE7_MEM_START_ADDR                    40'h0F00_0000
`define L2_MODULE7_MEM_END_ADDR                      40'h0FFF_FFFF


//AI CORE
`define AI_CORE_MAILBOX_START_ADDR              (`AI_CORE_BASE_ADDR + 28'h000_0000)
`define AI_CORE_MAILBOX_END_ADDR                (`AI_CORE_BASE_ADDR + 28'h000_FFFF)
`define AI_CORE_M_IFD0_START_ADDR               (`AI_CORE_BASE_ADDR + 28'h001_0000)
`define AI_CORE_M_IFD0_END_ADDR                 (`AI_CORE_BASE_ADDR + 28'h001_FFFF)
`define AI_CORE_M_IFD1_START_ADDR               (`AI_CORE_BASE_ADDR + 28'h002_0000)
`define AI_CORE_M_IFD1_END_ADDR                 (`AI_CORE_BASE_ADDR + 28'h002_FFFF)
`define AI_CORE_M_IFDW_START_ADDR               (`AI_CORE_BASE_ADDR + 28'h003_0000)
`define AI_CORE_M_IFDW_END_ADDR                 (`AI_CORE_BASE_ADDR + 28'h003_FFFF)
`define AI_CORE_M_ODR_START_ADDR                (`AI_CORE_BASE_ADDR + 28'h004_0000)
`define AI_CORE_M_ODR_END_ADDR                  (`AI_CORE_BASE_ADDR + 28'h004_FFFF)
`define AI_CORE_D_IFD0_START_ADDR               (`AI_CORE_BASE_ADDR + 28'h005_0000)
`define AI_CORE_D_IFD0_END_ADDR                 (`AI_CORE_BASE_ADDR + 28'h005_FFFF)
`define AI_CORE_D_IFD1_START_ADDR               (`AI_CORE_BASE_ADDR + 28'h006_0000)
`define AI_CORE_D_IFD1_END_ADDR                 (`AI_CORE_BASE_ADDR + 28'h006_FFFF)
`define AI_CORE_D_ODR_START_ADDR                (`AI_CORE_BASE_ADDR + 28'h007_0000)
`define AI_CORE_D_ODR_END_ADDR                  (`AI_CORE_BASE_ADDR + 28'h007_FFFF)
`define AI_CORE_TOKEN_START_ADDR                (`AI_CORE_BASE_ADDR + 28'h008_0000)
`define AI_CORE_TOKEN_END_ADDR                  (`AI_CORE_BASE_ADDR + 28'h008_7FFF)
`define AI_CORE_TRACE_START_ADDR                (`AI_CORE_BASE_ADDR + 28'h008_8000)
`define AI_CORE_TRACE_END_ADDR                  (`AI_CORE_BASE_ADDR + 28'h008_FFFF)
`define AI_CORE_M_MVMEXE_START_ADDR             (`AI_CORE_BASE_ADDR + 28'h009_0000)
`define AI_CORE_M_MVMEXE_END_ADDR               (`AI_CORE_BASE_ADDR + 28'h009_FFFF)
`define AI_CORE_M_MVMPRG_START_ADDR             (`AI_CORE_BASE_ADDR + 28'h00A_0000)
`define AI_CORE_M_MVMPRG_END_ADDR               (`AI_CORE_BASE_ADDR + 28'h00A_FFFF)
`define AI_CORE_M_IAU_START_ADDR                (`AI_CORE_BASE_ADDR + 28'h00B_0000)
`define AI_CORE_M_IAU_END_ADDR                  (`AI_CORE_BASE_ADDR + 28'h00B_FFFF)
`define AI_CORE_M_DPU_START_ADDR                (`AI_CORE_BASE_ADDR + 28'h00C_0000)
`define AI_CORE_M_DPU_END_ADDR                  (`AI_CORE_BASE_ADDR + 28'h00C_FFFF)
`define AI_CORE_D_DWPU_START_ADDR               (`AI_CORE_BASE_ADDR + 28'h00D_0000)
`define AI_CORE_D_DWPU_END_ADDR                 (`AI_CORE_BASE_ADDR + 28'h00D_FFFF)
`define AI_CORE_D_IAU_START_ADDR                (`AI_CORE_BASE_ADDR + 28'h00E_0000)
`define AI_CORE_D_IAU_END_ADDR                  (`AI_CORE_BASE_ADDR + 28'h00E_FFFF)
`define AI_CORE_D_DPU_START_ADDR                (`AI_CORE_BASE_ADDR + 28'h00F_0000)
`define AI_CORE_D_DPU_END_ADDR                  (`AI_CORE_BASE_ADDR + 28'h00F_FFFF)
`define AI_CORE_CSR_START_ADDR                  (`AI_CORE_BASE_ADDR + 28'h010_0000)
`define AI_CORE_CSR_END_ADDR                    (`AI_CORE_BASE_ADDR + 28'h010_FFFF)
`define AI_CORE_RESERVED1_START_ADDR            (`AI_CORE_BASE_ADDR + 28'h012_0000)
`define AI_CORE_RESERVED1_END_ADDR              (`AI_CORE_BASE_ADDR + 28'h021_FFFF)
`define AI_CORE_PVT_START_ADDR                  (`AI_CORE_BASE_ADDR + 28'h022_0000)
`define AI_CORE_PVT_END_ADDR                    (`AI_CORE_BASE_ADDR + 28'h022_FFFF)
`define AI_CORE_PMU_START_ADDR                  (`AI_CORE_BASE_ADDR + 28'h023_0000)
`define AI_CORE_PMU_END_ADDR                    (`AI_CORE_BASE_ADDR + 28'h023_FFFF)
`define AI_CORE_RESERVED2_START_ADDR            (`AI_CORE_BASE_ADDR + 28'h024_0000)
`define AI_CORE_RESERVED2_END_ADDR              (`AI_CORE_BASE_ADDR + 28'h03F_FFFF)
`define AI_CORE_PLIC_START_ADDR                 (`AI_CORE_BASE_ADDR + 28'h040_0000)
`define AI_CORE_PLIC_END_ADDR                   (`AI_CORE_BASE_ADDR + 28'h07F_FFFF)


//updated as per europa
`define AI_CORE_CONFIG_PERIPH_PMU_START_ADDR    (`AI_CORE_BASE_ADDR + 28'h008_0000)
`define AI_CORE_CONFIG_PERIPH_PMU_END_ADDR      (`AI_CORE_BASE_ADDR + 28'h008_FFFF)
`define AI_CORE_CONTROL_LP_DMA_START_ADDR       (`AI_CORE_BASE_ADDR + 28'h102_0000)
`define AI_CORE_CONTROL_LP_DMA_END_ADDR         (`AI_CORE_BASE_ADDR + 28'h102_FFFF)

`define AI_CORE_SPM_MEM_START_ADDR              (`AI_CORE_BASE_ADDR + 28'h400_0000)
`define AI_CORE_SPM_MEM_END_ADDR                (`AI_CORE_BASE_ADDR + 28'h407_FFFF)
`define AI_CORE_RESERVED_SPM_MEM_START_ADDR     (`AI_CORE_BASE_ADDR + 28'h408_0000)
`define AI_CORE_RESERVED_SPM_MEM_END_ADDR       (`AI_CORE_BASE_ADDR + 28'h7FF_FFFF)
`define AI_CORE_L1_MEM_START_ADDR               (`AI_CORE_BASE_ADDR + 28'h800_0000)
`define AI_CORE_L1_MEM_END_ADDR                 (`AI_CORE_BASE_ADDR + 28'h83F_FFFF)
`define AI_CORE_RESERVED_AI_CORE_MEM_START_ADDR (`AI_CORE_BASE_ADDR + 28'h840_0000)
`define AI_CORE_RESERVED_AI_CORE_MEM_END_ADDR   (`AI_CORE_BASE_ADDR + 28'hFFF_FFFF)

//Command descr starting address
`define AI_CORE_MID_MVM_EXE_COMMAND_DESC            (`AI_CORE_BASE_ADDR + 28'h2A0_0000)
`define AI_CORE_MID_MVM_PRG_COMMAND_DESC            (`AI_CORE_BASE_ADDR + 28'h2A1_0000)
`define AI_CORE_MID_IAU_COMMAND_DESC                (`AI_CORE_BASE_ADDR + 28'h2A2_1000)
`define AI_CORE_MID_DPU_COMMAND_DESC                (`AI_CORE_BASE_ADDR + 28'h2A3_1000)
`define AI_CORE_DID_DWPU_COMMAND_DESC               (`AI_CORE_BASE_ADDR + 28'h2C0_0000)
`define AI_CORE_DID_IAU_COMMAND_DESC                (`AI_CORE_BASE_ADDR + 28'h2C1_0000)
`define AI_CORE_DID_DPU_COMMAND_DESC                (`AI_CORE_BASE_ADDR + 28'h2C2_0000)



//descriptor memories https://git.axelera.ai/ai-hw-team/triton/-/blob/main/subip/ai_core/auto_doc/addr_offset_map_detailed.md
//  	      | Instr Count	| Instr Width	| Size [B]	| Size [B]	| Alignment [B]
// MVM	    | 256	        | 14	        | 512	      | 0x200	    | 2
// DWPU	    | 1024	      | 128	        | 16384	    | 0x4000	  | 8
// IAU	    | 256	        | 16	        | 512	      | 0x200	    | 2
// DPU	    | 1024	      | 32	        | 4096	    | 0x1000	  | 4
// IFD/ODR  |	128	        | 64	        | 1024	    | 0x400	    | 8
// Descriptor memories end address is based on this table
`define AI_CORE_M_IFD0_INSTR_MEM_START_ADDR    (`AI_CORE_BASE_ADDR + 28'h300_0000)
`define AI_CORE_M_IFD0_INSTR_MEM_END_ADDR      (`AI_CORE_BASE_ADDR + 28'h300_FFFF)
`define AI_CORE_M_IFD1_INSTR_MEM_START_ADDR    (`AI_CORE_BASE_ADDR + 28'h301_0000)
`define AI_CORE_M_IFD1_INSTR_MEM_END_ADDR      (`AI_CORE_BASE_ADDR + 28'h301_FFFF)
`define AI_CORE_M_IFD2_INSTR_MEM_START_ADDR    (`AI_CORE_BASE_ADDR + 28'h302_0000)
`define AI_CORE_M_IFD2_INSTR_MEM_END_ADDR      (`AI_CORE_BASE_ADDR + 28'h302_FFFF)
`define AI_CORE_M_IFDW_INSTR_MEM_START_ADDR    (`AI_CORE_BASE_ADDR + 28'h303_0000)
`define AI_CORE_M_IFDW_INSTR_MEM_END_ADDR      (`AI_CORE_BASE_ADDR + 28'h303_FFFF)
`define AI_CORE_M_ODR_INSTR_MEM_START_ADDR     (`AI_CORE_BASE_ADDR + 28'h304_0000)
`define AI_CORE_M_ODR_INSTR_MEM_END_ADDR       (`AI_CORE_BASE_ADDR + 28'h304_FFFF)
`define AI_CORE_D_IFD0_INSTR_MEM_START_ADDR    (`AI_CORE_BASE_ADDR + 28'h305_0000)
`define AI_CORE_D_IFD0_INSTR_MEM_END_ADDR      (`AI_CORE_BASE_ADDR + 28'h305_FFFF)
`define AI_CORE_D_IFD1_INSTR_MEM_START_ADDR    (`AI_CORE_BASE_ADDR + 28'h306_0000)
`define AI_CORE_D_IFD1_INSTR_MEM_END_ADDR      (`AI_CORE_BASE_ADDR + 28'h306_FFFF)
`define AI_CORE_D_ODR_INSTR_MEM_START_ADDR     (`AI_CORE_BASE_ADDR + 28'h307_0000)
`define AI_CORE_D_ODR_INSTR_MEM_END_ADDR       (`AI_CORE_BASE_ADDR + 28'h307_FFFF)
`define AI_CORE_M_MVMEXE_INSTR_MEM_START_ADDR  (`AI_CORE_BASE_ADDR + 28'h320_0000)
`define AI_CORE_M_MVMEXE_INSTR_MEM_END_ADDR    (`AI_CORE_BASE_ADDR + 28'h320_FFFF)
`define AI_CORE_M_IAU_INSTR_MEM_START_ADDR     (`AI_CORE_BASE_ADDR + 28'h00b_8000)
`define AI_CORE_M_IAU_INSTR_MEM_END_ADDR       (`AI_CORE_BASE_ADDR + 28'h00b_81FF)
`define AI_CORE_M_DPU_INSTR_MEM_START_ADDR     (`AI_CORE_BASE_ADDR + 28'h00c_8000)
`define AI_CORE_M_DPU_INSTR_MEM_END_ADDR       (`AI_CORE_BASE_ADDR + 28'h00c_8FFF)
`define AI_CORE_D_DWPU_INSTR_MEM_START_ADDR    (`AI_CORE_BASE_ADDR + 28'h00d_8000)
`define AI_CORE_D_DWPU_INSTR_MEM_END_ADDR      (`AI_CORE_BASE_ADDR + 28'h00d_BFFF)
`define AI_CORE_D_IAU_INSTR_MEM_START_ADDR     (`AI_CORE_BASE_ADDR + 28'h00e_8000)
`define AI_CORE_D_IAU_INSTR_MEM_END_ADDR       (`AI_CORE_BASE_ADDR + 28'h00e_81FF)
`define AI_CORE_D_DPU_INSTR_MEM_START_ADDR     (`AI_CORE_BASE_ADDR + 28'h00f_8000)
`define AI_CORE_D_DPU_INSTR_MEM_END_ADDR       (`AI_CORE_BASE_ADDR + 28'h00f_8FFF)


`define DDR0_MEM_START_ADDR            40'h20_0000_0000
`define DDR0_MEM_END_ADDR              40'h27_FFFF_FFFF

`define DDR1_MEM_START_ADDR            40'h28_0000_0000
`define DDR1_MEM_END_ADDR              40'h2F_FFFF_FFFF



//Struct
/******************************************************************************************************************************
Op_code	0	// CMDB descriptor operation codes0=MVM_PRG_CMDB_WR_WB_OPC (MVM-DP write weights)
A_s	0..IMC_NB_WEIGHT_SETS-1	IMC weights set to be programmed
A_u_pw	0..7	Programming row offset
A_t_pw	0..7	Programming column offset
Wb_u_pw	0..7	Programming row size, a value 0 maps to 1x64(PW gran) rows, a value of 7 maps to 8x64(PW gran) rows
Wb_t_pw	0..7	Programming column size, a value 0 maps to 1x64(PW gran) cols, a value of 7 maps to 8x64(PW gran) cols
*******************************************************************************************************************************/
typedef struct packed{
  bit [7:0] wb_t_pw;
  bit [7:0] wb_u_pw;
  bit [7:0] a_t_pw;
  bit [7:0] a_u_pw;
  bit [7:0] a_s;
  bit [7:0] op_code;
} mvm_prg_cmd_struct;
/******************************************************************************************************************************
A_s	0..IMC_NB_WEIGHT_SETS-1	IMC weights to be used for compute
A_u_pw	0..7	Compute row offset (input offset)
A_t_pw	0..7	Compute column offset (output offset)
Wb_u_pw	0..7	Compute row size (input size) A value of 0 maps to an operation on 1 PW, a value of 7 maps to an operation on 8 PWs
Wb_t_pw	0..7	Compute column size (output size) A value of 0 maps to an operation on 1PW, a value of 7 maps to an operation on 8PWs
*******************************************************************************************************************************/
typedef struct packed{
  bit [2:0] wb_t_pw;
  bit [2:0] wb_u_pw;
  bit [2:0] a_t_pw;
  bit [2:0] a_u_pw;
  bit [1:0] a_s;
} mvm_qcmd_struct;
/******************************************************************************************************************************
Op_code	0, 1	//CMDB descriptor operation codes 0=MVM_EXE_CMDB_CMP_OPC (MVM-DP compute operation), 1=MVM_EXE_CMDB_BYP_OPC (MVM-DP bypass operation)
Qcmd_len	1..MVM_EXE_QCMD_MEM_DEPTH-1 //Length of the qcmd section that is repeated by a qcmd iteration
Qcmd_ptr	0.. MVM_EXE_QCMD_MEM_DEPTH-1	Start pointer for the used qcmd section
Qcmd_iter	1..2**32-1	Number of iterations to run

*******************************************************************************************************************************/
typedef struct packed{
  bit [31:0] qcmd_iter;
  bit [15:0] qcmd_ptr;
  bit [7:0]  qcmd_len;
  bit [7:0]  op_code;
} mvm_exe_cmd_struct;
//`define  3

// ****************************************************************************
// Enumerated Types
// ****************************************************************************
/**
  * Enum to represent transfer sizes
  */
typedef enum bit [3:0] {
  BURST_SIZE_8BIT    = `AXI_TRANSACTION_BURST_SIZE_8,
  BURST_SIZE_16BIT   = `AXI_TRANSACTION_BURST_SIZE_16,
  BURST_SIZE_32BIT   = `AXI_TRANSACTION_BURST_SIZE_32,
  BURST_SIZE_64BIT   = `AXI_TRANSACTION_BURST_SIZE_64
} burst_size_enum;

/**
  * Enum to represent burst type in a transaction
  */
typedef enum bit[1:0]{
  FIXED = `AXI_TRANSACTION_BURST_FIXED,
  INCR =  `AXI_TRANSACTION_BURST_INCR,
  WRAP =  `AXI_TRANSACTION_BURST_WRAP
} burst_type_enum;

/**
  * Enum to represent burst lenght in a transaction
  */
typedef enum bit[5:0]{
  BURST_LENGTH_1 = 1,
  BURST_LENGTH_2 = 2,
  BURST_LENGTH_3 = 3,
  BURST_LENGTH_4 = 4,
  BURST_LENGTH_5 = 5,
  BURST_LENGTH_6 = 6,
  BURST_LENGTH_7 = 7,
  BURST_LENGTH_8 = 8,
  BURST_LENGTH_9 = 9,
  BURST_LENGTH_10 = 10,
  BURST_LENGTH_16 = 16
} burst_lenght_enum;

/**
  * Enum to represent responses in a transaction
  */
typedef enum bit [1:0] {
  OKAY    = `AXI_OKAY_RESPONSE,
  EXOKAY  = `AXI_EXOKAY_RESPONSE,
  SLVERR =  `AXI_SLVERR_RESPONSE,
  DECERR  = `AXI_DECERR_RESPONSE
} resp_type_enum;

typedef enum int {
  M_IFD0_REGMOD     = 'd0,
  M_IFD1_REGMOD     = 'd1,
  M_IFD2_REGMOD     = 'd2,
  M_IFDW_REGMOD     = 'd3,
  D_IFD0_REGMOD     = 'd4,
  D_IFD1_REGMOD     = 'd5,
  M_ODR_REGMOD      = 'd6,
  D_ODR_REGMOD      = 'd7,
  M_MVMEXE_REGMOD   = 'd8,
  M_MVMPRG_REGMOD   = 'd9,
  M_IAU_REGMOD      = 'd10,
  D_IAU_REGMOD      = 'd11,
  M_DPU_REGMOD      = 'd12,
  D_DPU_REGMOD      = 'd13,
  D_DWPU_REGMOD     = 'd14,
  MAIL_REGMOD       = 'd15,
  TKN_REGMOD        = 'd16,
  MID_PERIPH_REGMOD          = 'd17,
  INFRA_PERIPH_REGMOD        = 'd18,
  TIMESTAMP_REGMOD           = 'd19,
  LP_DMA_REGMOD              = 'd20,
  HP_DMA_REGMOD              = 'd21,
  RV_PLIC_REGMOD             = 'd22
} regmod_number_enum;

/**
  * Enum to represent each of the DMA masters (two in total)
  */
typedef enum bit {
  DMA_MASTER_1 = 'b0,
  DMA_MASTER_2 = 'b1
} dma_master_enum;

/**
  * Enum to represent each of the DMA channels (six in total)
  */
typedef enum int {
  DMA_CHANNEL_1 = 'd1,
  DMA_CHANNEL_2 = 'd2,
  DMA_CHANNEL_3 = 'd3,
  DMA_CHANNEL_4 = 'd4,
  DMA_CHANNEL_5 = 'd5,
  DMA_CHANNEL_6 = 'd6
} dma_channel_enum;
