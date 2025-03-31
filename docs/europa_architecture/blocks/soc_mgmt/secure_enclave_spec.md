---
title: Secure Enclave Architecture Spec
doc:
  status: draft
  version: [0, 0, 0]
  confidentiality: internal
---

# Secure Enclave Architecture Spec

## Top-level architecture

The secure enclave includes all the glue logic for the KSE3 IP.

KSE3 AHB mailbox can be accessed in two ways:

*   Via the bus fabric by the APU (SW HOST)

*   Via KSE3 JTAG TAP, this path can be used by the JTAG user when the APU is not available


The KSE3 JTAG TAP can be used for:

*   Programming the OTP public reserved, early in the lifecycle of the device chip_wafer_test, see OTP

*   Sending commands to the KSE3 to initialize the secure OTP

*   Sending commands to the KSE3 to transition to the next lifecycle state

*   Open debug TAPs via the KSE3 Challenge/Response commands

KSE3 interrupt is connected to the APU only.

The 3 bus initiators (managers) in the Secure Enclave are:

*   APU (via AXI and bus fabric)

*   KSE3 (via APB 8-bit data width)

*   KSE3 JTAG TAP (via Command FSM and AHB2APB)

Each manager has different access rights to those OTP and Always-On Registers (AOR), as described in [OTP](#otp-one-time-programmable-memory) and [AOR](#aor-always-on-registers).

Additionally, the OTP DFT TAP, when unlocked (i.e. when LifeCycle State is chip_wafer_test or chip_field_return), has full access to the OTP. This TAP is used by DFT.

![secu_encl_top.drawio.svg](./img/secu_encl_top.drawio.svg)

## Clocks and resets

|     |     |     |
| --- | --- | --- |
| **Clock** | **Typical frequency** | **Comment** |
| i_clk | 100MHz | Default clock, connected to periph_clk_int. |
| i_otp_wrapper_clk | 50MHz | Connected to reference clock i_ref_clk.  <br>Used by OTP wrapper and APB async bridge (destination clock). |
| otp_wrapper_analog_clk | 3.125MHz | Internal, OTP analog only, derived as i_otp_wrapper_clk/16 |

|     |     |
| --- | --- |
| **Reset** | **Comment** |
| i_rst_n | Default reset, synchronized to periph_clk_int.  <br>Used by all modules except AOR and OTP. |
| i_otp_wrapper_rst_n | Always-on reset from POR, synchronized to i_ref_clk.  <br>Used by OTP wrapper and APB async bridge. |
| i_ao_rst_n | Always-on reset from POR, synchronized to periph_clk_int.  <br>Used by AOR. |

## Interrupts

|     |     |
| --- | --- |
| **Interrupt** | **Comment** |
| o_kse3_interrupt | Interrupt line driven by the KSE3 IP. This interrupt shall be connected to the APU. It is used to notify the APU that KSE3 has finished executing a command, as an alternative to polling the KSE3 CSR. An interrupt will also be always triggered anytime the KSE3 is out of reset.  <br>Note that interrupts may be triggered even by commands sent via KSE3 JTAG interface, for this reason APU should ignore this interrupt when `TDR_JTAG_DBG=1`. |

## OTP (One Time Programmable memory)

The OTP size is 16kbits. OTP macro is sf_otp_cp_a100_ln05lpe by Samsung.
The OTP memory map is split in 3 sections that have different access rights.

*   OTP secure: 256 bytes only accessible by the KSE APB interface. This is the only OTP section accessible by the KSE3. Note that even if the OTP DFT TAP has full access to the OTP in chip_wafer_test, the OTP secure section won’t be programmed by it.

*   OTP public reserved: Can be accessed by APU and JTAG KSE3 TAP for read. The idea is that this section is programmed for the first time by DFT via the OTP DFT TAP at chip_wafer_test lifecycle state. In chip_wafer_test, the OTP DFT TAP is unlocked and has full access to the OTP pins (bypassing the APB interface), in this way DFT/ATE team can write OTP fields such as SoC ID, calibration/trimming data etc. These fields are required later on by KSE3.
    This section can also be accessed by the JTAG KSE3 TAP for write during chip_wafer_test, this is to ease bring-up by giving the JTAG KSE3 TAP the ability to program those fields that are programmed by DFT via OTP DFT TAP in production.

*   OTP public unprotected: Can always be accessed by APU for read and write, and by JTAG KSE3 TAP for read and write at chip_wafer_test, read only otherwise, see [Access rights to OTP](#access-rights-to-otp) .


Note: When in end_of_life, OTP cannot be accessed by any device.
Access rights to OTP are enforced by the APB address decoder.

The OTP memory map, with focus on the OTP public reserved section, is shown below.

|     |     |     |     |     |
| --- | --- | --- | --- | --- |
| **Address offset** | **Name** | **Section** | **Size (bytes)** | **Size (bytes, HEX)** |
| 0x000 |     | OTP secure | 256 | 0x100 |
| 0x100 | Anchor value length | OTP public reserved | 4   | 0x4 |
| 0x104 | CA1 anchor value || 64  | 0x40 |
| 0x144 | TRNG configuration || 8   | 0x8 |
| 0x14C | Personalization string length || 4   | 0x4 |
| 0x150 | Personalization string || 64  | 0x40 |
| 0x190 | DBG counter || 4   | 0x4 |
| 0x194 | SoC class || 4   | 0x4 |
| 0x198 | Chip ID || 16  | 0x10 |
| 0x1A8 | BL 1.2 HMAC || 48  | 0x30 |
| 0x1D8 | Trimming data || 640 | 0x280 |
| 0x458 | CA2 anchor value | OTP public unprotected | 64  | 0x40 |
| 0x498 |     || 872 | 0x568 |

## AOR (Always-On Registers)

Europa instantiates 8-bit AORs as required by KSE3 integration manual, refer to table in [APB interconnect](#apb-interconnect) section.

## APB interconnect

The APB interconnect handles transactions towards OTP/AOR from 3 managers:

*   KSE3

*   KSE3 JTAG TAP

*   APU


The APB address decoder enforces the access rights towards OTP and AON. If an access is not allowed, it selects the APB Error response subordinate to return an error response to the corresponding manager.

Address conversion is performed to map KSE3 APB address to Secure Enclave address:

|     |     |     |     |
| --- | --- | --- | --- |
| **Component** |     | **KSE3 Address** | **APU Address** |
| KSE3 OTP | OTP secure (start) | 0x000 | 0x0205_0000 |
|| OTP secure (end) | 0x0FF | 0x0205_00FF |
| KSE3 AOR | SoC_Config0 | 0x100 | 0x0204_0000 |
|| SoC_Config0_Inv | 0x101 | 0x0204_0004 |
|| SoC_Config1 | 0x102 | 0x0204_0008 |
|| SoC_Config1_Inv | 0x103 | 0x0204_000C |
|| Plt_Config | 0x104 | 0x0204_0010 |
|| Plt_Config_Inv | 0x105 | 0x0204_0014 |
|| KSE3_State | 0x106 | 0x0204_0018 |
|| KSE3_State_Inv | 0x107 | 0x0204_001C |
|| KSE3_FR0 | 0x108 | 0x0204_0020 |
|| KSE3_FR1 | 0x109 | 0x0204_0024 |
|| KSE3_FR2 | 0x10A | 0x0204_0028 |
|| KSE3_FR3 | 0x10B | 0x0204_002C |
|| KSE3_FR4 | 0x10C | 0x0204_0030 |
|| KSE3_FR5 | 0x10D | 0x0204_0034 |
|| KSE3_FR6 | 0x10E | 0x0204_0048 |
|| KSE3_FR7 | 0x10F | 0x0204_004C |

#### **Access rights to OTP**:

|     |     |     |     |     |
| --- | --- | --- | --- | --- |
|     | **KSE3** | **KSE3 JTAG TAP** | **APU** | **OTP DFT TAP** |
| **OTP secure** | RW  | No access | No access | Has full OTP access anytime it is unlocked i.e. chip_wafer_test or chip field return.<br><br>Use case: DFT can populate OTP public unprotected in chip wafer test. |
| **OTP public unprotected** | No access | *   RW at chip_wafer_test<br>*   RO otherwise | RW  |
| **OTP public reserved** | No access | *   RW at chip_wafer_test<br>*   RO otherwise | RO  |

#### **Access rights to AOR**:

|     |     |     |     |     |
| --- | --- | --- | --- | --- |
| **Register** | **Description** | **KSE3 access** | **APU and KSE3 JTAG TAP access** | **Cold reset value** |
| SoC_Config0 | SoC Config (DAP/TAP) <br>These are used to generate debug TAP enable signals, see [TAPs status on each LCS](#taps-status-on-each-lcs) | RW  | RO  | 0x00 (TAPs closed) |
| SoC_Config0_Inv | Inverse values | RW  | RO  | 0xFF |
| SoC_Config1 | SoC Config (DAP/TAP) <br>These are used to generate debug TAP enable signals, see [TAPs status on each LCS](#taps-status-on-each-lcs) | RW  | RO  | 0x00 (TAPs closed) |
| SoC_Config1_Inv | Inverse values | RW  | RO  | 0xFF |
| Plt_Config | Platform Config | RW  | RO  | 0x00 |
| Plt_Config_Inv | Inverse values | RW  | RO  | 0xFF |
| KSE3_State | Internal Security State | RW  | \-  | 0x00 |
| KSE3_State_Inv | Inverse value | RW  | \-  | 0x00 |
| KSE3_FR0 | Fast Resume (optional) | RW  | \-  | 0x00 |
| KSE3_FR1 |     | RW  | \-  | 0x00 |
| KSE3_FR2 |     | RW  | \-  | 0x00 |
| KSE3_FR3 |     | RW  | \-  | 0x00 |
| KSE3_FR4 |     | RW  | \-  | 0x00 |
| KSE3_FR5 |     | RW  | \-  | 0x00 |
| KSE3_FR6 |     | RW  | \-  | 0x00 |
| KSE3_FR7 |     | RW  | \-  | 0x00 |

## AHB interconnect

The AHB interconnect allows the APU and KSE3 JTAG TAP to access the KSE3 mailbox. It also allows the KSE3 JTAG TAP to access OTP and AOR subordinates.

## KSE3 JTAG TAP

This TAP is used to access the KSE3 AHB mailbox, the OTP and AOR blocks. All JTAG commands go through the Command FSM block first.

The possible commands that can be sent via this TAP are:

*   AHB sequence requests. These are JTAG commands that will trigger a sequence of AHB transactions:

    *   enter_jtag_access_mode

    *   init_kse3_adac_itf

*   Single AHB requests:

    *   AHB reads to KSE3, OTP, AOR

    *   AHB write to KSE3, OTP, AOR


The order in which these commands can be sent is defined in [Command FSM](#command-fsm) **JTAG CMD FSM** section.
The Test Data Registers (TDRs) associated with this TAP are the following.

| **Signal name** | **Direction** | **Size (bits)** | **Comment** |
| --- | --- | --- | --- |
| ahb_addr | OUT | 20  | AHB transaction address |
| ahb_wdata | OUT | 32  | AHB data to be written (for write transactions) |
| ahb_wr | OUT | 1   | 1: AHB write <br>0: AHB read |
| ahb_valid | OUT | 1   | **Command** = AHB request |
| ahb_rdata | IN  | 32  | AHB read data |
| enter_jtag_access_mode | OUT | 1   | **Command** \= request to perform KSE3 initialization |
| init_kse3_adac_itf | OUT | 1   | **Command** \= request to perform KSE3 ADAC interface initialization |
| transaction_id | OUT | 1   | Toggles after each new command, used for handshaking |
| jtag_dbg | OUT | 1   | This register must be set to 1 before starting any JTAG command from this TAP. Its transitions trigger an automatic warm reset of Command FSM, KSE3 and APU. See [APU vs KSE3 JTAG TAP: Exclusive access to KSE3](#apu-vs-kse3-jtag-tap-exclusive-access-to-kse3). for more information. |
| jtag_status | IN  | 4   | *   bit 0 (READY): indicates if the [Command FSM](#command-fsm) is ready to accept a new transaction, and that the last transaction’s response is valid.<br>    <br>*   bit 1 (KSE3_ERROR): indicates that the [Command FSM](#command-fsm) is in JTAG_CMD_ERROR state due to an error occurred during the INIT_KSE3 or INIT_KSE_ADAC sequences. If bit 2 (AHB_ERROR) is also set, the error is a non-successful AHB transaction, otherwise the error is due to KSE3 CMD_STATUS != SECIP_SUCCESS.<br>    <br>*   bit 2 (AHB_ERROR): indicates that the command resulted in an AHB error response. This could be due to an access to a protected or out-of-range OTP or AOR section. Refer to [Access rights to OTP](#access-rights-to-otp) and [Access rights to AOR](#access-rights-to-aor). Refer to KSE3 datasheet for errors related to a KSE3 access.<br>    <br>*   bit 3 (CMD_IGNORED): indicates that the previous command was ignored by the [Command FSM](#command-fsm) as not allowed in the current state. Refer to [Allowed commands via JTAG](#allowed-commands-via-jtag). |

### KSE3 JTAG TAP address mappings

The ahb_addr TDR is extended with the Secure Enclave base address before being sent to the AHB demux. Address conversion for each resource is shown below.

|     |     |     |
| --- | --- | --- |
| **KSE3 JTAG TAP ahb_addr** | **APU address** | **Resource** |
| 0x0_0000 | 0x0200_0000 | KSE3 |
| 0x4_0000 | 0x0204_0000 | AOR |
| 0x5_0000 | 0x0205_0000 | OTP |

### Command FSM

This Command FSM takes inputs from the KSE3 JTAG TAP Test Data Registers (TDRs) and converts them to AHB accesses to the KSE3. It’s in charge of:

*   Preventing the JTAG user from sending not allowed commands to the KSE3

*   Generating a sequence of AHB commands to the KSE3 upon specific JTAG commands (namely enter_jtag_access_mode and init_kse3_adac_itf)


The Command FSM includes an AHB manager that can perform accesses to KSE3, OTP and AOR only.
Note that KSE3 JTAG TAP accesses to OTP and AOR are subjected to a further restriction by the [APB interconnect](#apb-interconnect).

The architecture of the command FSM is the following:

![secu_encl_command_fsm_arch.drawio.svg](./img/secu_encl_command_fsm_arch.drawio.svg)

*   **JTAG CMD FSM**: This is the main FSM which controls the KSE CDM FSM and OTP to KSE FSM. It interprets incoming JTAG commands, filters the allowed AHB accesses to the KSE3 and contains the command sequences for enter_jtag_access_mode and init_kse3_adac_itf.
    If an error occurs during the INIT_KSE3 or INIT_KSE3_ADAC, the FSM moves to the JTAG_CMD_ERROR state. The only exception is for the SetObject CA2 AnchorValue, where an error from the KSE3 is ignored. This is because the CA2 AnchorValue might be written by the User at User Perso lifecycle state and might not be available at earlier lifecycle states. This won’t prevent enabling debug via KSE3 JTAG TAP for CA1 and won’t affect subsequent KSE3 commands.


![secu_encl_command_fsm.drawio.svg](./img/secu_encl_command_fsm.drawio.svg)

*   **KSE CMD FSM**: This FSM is in charge of sending a single command to the KSE3 mailbox using the KSE3 CMD_CTRL register, it also performs the required polling and error checking.

    *   `KSE_CMD_POLL0`: Poll KSE_CMD_CTRL until the start bit is 0 (meaning KSE3 is ready)

    *   `KSE_CMD_SEND`: Write the requested command to the KSE_CMD_CTRL register. Commands are sent with CMD_CTRL.IRQ_DIS bit set to 1, this way the APU will not receive an IRQ from the KSE3 completing the command. Note that at reset the APU will have this IRQ masked anyway.

         Should this be enforced by HW for every AHB command sent by the JTAG user to the KSE3?

    *   `KSE_CMD_POLL1`: Poll KSE_CMD_CTRL until the start bit is 0 (meaning KSE3 is ready)

    *   `KSE_CMD_ERR_CHECK`: Read KSE_CMD_STATUS and set the kse_cmd_error output if different than SECIP_SUCCESS. It’s up to the JTAG CMD FSM to decide if the error should be ignored or if it should move to the JTAG_CMD_ERROR state.


![uarch-kse_cmd_fsm.drawio.svg](./img/secu_encl_kse_cmd_fsm.drawio.svg)

*   **OTP to KSE FSM**: This FSM is in charge of moving data from the OTP to the KSE3 DRAM. Data is read 32 bits at a time and then written to the KSE3 DRAM before moving to the next address. It can optionally invert the data read from OTP before writing it to the KSE3 DRAM, this is used to populate SOC_ID_INV and DBG_CNT_INV fields required by the SetSocConfig KSE3 commands.


![secu_encl_otp_to_kse_fsm.drawio.svg](./img/secu_encl_otp_to_kse_fsm.drawio.svg)

### Allowed commands via JTAG

AHB commands and sequences that can be sent to the KSE3 via JTAG are filtered depending on the JTAG CMD FSM state. This is shown in the JTAG CMD FSM state diagram and in the table below.
This table contains the list of allowed JTAG AHB commands to the KSE3 (allowed_kse_cmds), OTP/AOR (allowed_ahb_cmds), JTAG AHB sequences (allowed_jtag_cmds) depending on JTAG CMD FSM state:

|     |     |     |     |
| --- | --- | --- | --- |
| **JTAG CMD FSM state** | **allowed_kse_cmds** | **allowed_jtag_cmds** | **allowed_ahb_cmds** |
| JTAG_CMD_IDLE | NONE | *   if (LCS != end_of_life and TDR_JTAG_DBG == 1):  <br>    enter_jtag_access_mode<br>    <br>*   Otherwise: NONE. | *   if LCS != end_of_life and TDR_JTAG_DBG == 1:  <br>    OTP and AOR accesses, with restrictions from APB address decoder.<br>    <br>*   Otherwise: NONE. |
| INIT_CMD_INITROT | NONE (JTAG BUSY) | NONE (JTAG BUSY) | NONE (JTAG BUSY) |
| INIT_DRAM_PERSO_LEN | NONE (JTAG BUSY) | NONE (JTAG BUSY) | NONE (JTAG BUSY) |
| INIT_DRAM_TRNG_CONFIG | NONE (JTAG BUSY) | NONE (JTAG BUSY) | NONE (JTAG BUSY) |
| INIT_DRAM_PERSO_STRING | NONE (JTAG BUSY) | NONE (JTAG BUSY) | NONE (JTAG BUSY) |
| INIT_CMD_INITCRYPTO | NONE (JTAG BUSY) | NONE (JTAG BUSY) | NONE (JTAG BUSY) |
| JTAG_CMD_FULLY_OPEN | ALL | NONE | ALL, with restrictions from APB address decoder. |
| JTAG_CMD_KEEP_CLOSED | NONE | init_kse3_adac_itf | OTP and AOR accesses, with restrictions from APB address decoder. |
| INIT_ADAC_DRAM_CA_ANCHOR_LEN | NONE (JTAG BUSY) | NONE (JTAG BUSY) | NONE (JTAG BUSY) |
| INIT_ADAC_DRAM_CA_ANCHOR_VAL | NONE (JTAG BUSY) | NONE (JTAG BUSY) | NONE (JTAG BUSY) |
| INIT_ADAC_DRAM_CA_TYPE_ID | NONE (JTAG BUSY) | NONE (JTAG BUSY) | NONE (JTAG BUSY) |
| INIT_ADAC_CMD_SETOBJECT | NONE (JTAG BUSY) | NONE (JTAG BUSY) | NONE (JTAG BUSY) |
| INIT_ADAC_DRAM_SOC_ID | NONE (JTAG BUSY) | NONE (JTAG BUSY) | NONE (JTAG BUSY) |
| INIT_ADAC_DRAM_SOC_ID_INV | NONE (JTAG BUSY) | NONE (JTAG BUSY) | NONE (JTAG BUSY) |
| INIT_ADAC_DRAM_DBG_CNT | NONE (JTAG BUSY) | NONE (JTAG BUSY) | NONE (JTAG BUSY) |
| INIT_ADAC_DRAM_DBG_CNT_INV | NONE (JTAG BUSY) | NONE (JTAG BUSY) | NONE (JTAG BUSY) |
| INIT_ADAC_DRAM_SOC_CLASS | NONE (JTAG BUSY) | NONE (JTAG BUSY) | NONE (JTAG BUSY) |
| INIT_ADAC_CMD_SETSOCCONFIG | NONE (JTAG BUSY) | NONE (JTAG BUSY) | NONE (JTAG BUSY) |
| JTAG_CMD_ADAC_ONLY | GetChallnge, UnlockAccess | NONE | OTP and AOR accesses, with restrictions from APB address decoder. |
| JTAG_CMD_ERROR_REPORT | NONE (JTAG BUSY) | NONE (JTAG BUSY) | NONE (JTAG BUSY) |
| JTAG_CMD_ERROR | CMD_CTRL is RO, everything else is accessible. | NONE | OTP and AOR accesses, with restrictions from APB address decoder. |

### KSE3 DRAM, OTP and AOR access rights via JTAG

While commands to the KSE3 are filtered depending on Command FSM status, access to KSE3 DRAM, OTP and AOR depends on the life-cycle state (LCS) only. The filtering is still performed in the Command FSM block according to the following table.

|     |     |     |     |     |
| --- | --- | --- | --- | --- |
|     | **KSE3 TAP access rights** |     |     |     |
| **LCS** | **OTP** | **AON** | **DRAM** | **KSE3 commands** |
| Chip wafer test | Restricted by APB address decoder: [Access rights to OTP](#access-rights-to-otp).  <br>OTP secure: No access  <br>OTP public reserved: RW  <br>OTP public unpotected: RO.<br><br>Note: OTP DFT TAP has full access to the OTP in this LCS. | Restricted by APB address decoder: [Access rights to AOR](#access-rights-to-aor). | ALL  <br>(must perform enter_jtag_access_mode first) | ALL  <br>(must perform enter_jtag_access_mode first) |
| Chip perso | Restricted by APB address decoder: [Access rights to OTP](#access-rights-to-otp).  <br>OTP secure: No access  <br>OTP public reserved: RO  <br>OTP public unpotected: RO | Restricted by APB address decoder: [Access rights to AOR](#access-rights-to-aor). | ALL  <br>(must perform enter_jtag_access_mode first) | ALL  <br>(must perform enter_jtag_access_mode first) |
| User delivery (User perso)  <br>(customer) | Restricted by APB address decoder: [Access rights to OTP](#access-rights-to-otp).  <br>OTP secure: No access  <br>OTP public reserved: RO  <br>OTP public unpotected: RO | Restricted by APB address decoder: [Access rights to AOR](#access-rights-to-aor). | ALL  <br>(must perform enter_jtag_access_mode first) | Getchallenge,  <br>Unlockaccess  <br>(must perform enter_jtag_access_mode and init_kse3_adac_itf first) |
| User secured  <br>(customer) | Restricted by APB address decoder: [Access rights to OTP](#access-rights-to-otp).  <br>OTP secure: No access  <br>OTP public reserved: RO  <br>OTP public unpotected: RO | Restricted by APB address decoder: [Access rights to AOR](#access-rights-to-aor). | ALL  <br>(must perform enter_jtag_access_mode first) | Getchallenge,  <br>Unlockaccess  <br>(must perform enter_jtag_access_mode and init_kse3_adac_itf first) |
| User decommissioned  <br>(customer) | Restricted by APB address decoder: [Access rights to OTP](#access-rights-to-otp).  <br>OTP secure: No access  <br>OTP public reserved: RO  <br>OTP public unpotected: RO | Restricted by APB address decoder: [Access rights to AOR](#access-rights-to-aor). | ALL  <br>(must perform enter_jtag_access_mode first) | Getchallenge,  <br>Unlockaccess  <br>(must perform enter_jtag_access_mode and init_kse3_adac_itf first) |
| Chip field return | Restricted by APB address decoder: [Access rights to OTP](#access-rights-to-otp).  <br>OTP secure: No access  <br>OTP public reserved: RO  <br>OTP public unprotected: RO.<br><br>Note: OTP DFT TAP has full access to the OTP in this LCS. | Restricted by APB address decoder: [Access rights to AOR](#access-rights-to-aor). | ALL  <br>(must perform enter_jtag_access_mode first) | ALL  <br>(must perform enter_jtag_access_mode first).  <br>Getchallenge and Unlockaccess will not work due to erased master key. |
| Terminated | NONE | NONE | NONE | NONE |

## APU vs KSE3 JTAG TAP: Exclusive access to KSE3

Kudelski requirements: Whenever the AHB manager of the KSE3 mailbox changes, the following must occur:

1.  KSE3 is reset (warm reset)

2.  The new mailbox manager has exclusive access to the KSE3 mailbox until the next warm reset


In Europa, the KSE3 mailbox can be accessed by either the APU or the KSE3 JTAG TAP via command FSM.

To ensure that Kudelski requirements are satisfied, the following is required:

*   One TDR bit of the KSE3 JTAG called `TDR_JTAG_DBG`, set to 0 at cold reset and memory mapped to `AOR_JTAG_DBG` for APU to read

*   soc_mgmt to automatically trigger a warm reset upon `TDR_JTAG_DBG` being toggled by the JTAG user, this resets the APU, KSE3 and Command FSM

*   APU to check `AOR_JTAG_DBG` at boot, and go to sleep if == 1


Note that both `TDR_JTAG_DBG` and `AOR_JTAG_DBG` are in always-on reset domain.

The main scenario where both APU and KSE3 JTAG TAP contend the KSE3 mailbox is when the User wants to enter debug mode via KSE3 JTAG TAP. This scenario will be handled as follows:

1.  Cold reset → `TDR_JTAG_DBG=0`

2.  APU reads `AOR_JTAG_DBG==0` and starts to boot normally

3.  KSE3 JTAG HW FSM reads `TDR_JTAG_DBG==0` → JTAG commands to KSE3 are blocked (default behaviour)

4.  JTAG user sets `TDR_JTAG_DBG=1` → soc_mgmt automatically triggers a warm reset: APU and KSE3 JTAG HW FSM are reset

5.  APU restarts and reads `AOR_JTAG_DBG==1` → APU goes to sleep mode

6.  KSE3 JTAG HW FSM restarts and reads `TDR_JTAG_DBG==1` → JTAG commands to KSE3 are allowed

7.  User sends JTAG commands to the KSE3 to unlock the debug TAPs → debug TAPs configuration is written into secure enclave always-on registers (SECU_AOR SOC_CONFIG)

8.  JTAG user sets `TDR_JTAG_DBG=0` → soc_mgmt automatically triggers a warm reset: APU and KSE3 JTAG HW FSM are reset

9.  Same as 2. and 3. but with debug TAPs OPEN.


The following diagram shows the interactions between the various components for this scenario:

![secu_encl_debug_via_jtag.drawio.svg](./img/secu_encl_debug_via_jtag.drawio.svg)

Note that KSE3 interrupt requests towards the APU may be triggered by commands sent via KSE3 JTAG interface, APU should ignore this interrupt when `TDR_JTAG_DBG=1`.

## TAPs status on each LCS

JTAG TAPs are divided into 3 categories:

1.  Always unlocked: This is the case of the **KSE3 JTAG TAP** only. The JTAG Command FSM in the secure enclave is in charge of filtering out unallowed commands towards the KSE3 issued from this TAP.

2.  Controlled via OTP LCS: This is the case of the **OTP DFT TAP** only, enabled by the `o_otp_tap_en` output. This TAP is open in chip_wafer_test or chip_field_return only. The OTP wrapper itself reads the LCS at cold reset and CLOSES or OPENS this tap accordingly.

3.  Controlled via AOR: This the case of the remaining TAPs, which we call **Debug TAPs** below. These TAPs are controlled by the KSE3 depending on OTP configurations set via KSE3 SetSocConfig command, and LCS. Refer to KSE3 documentation for more details. These TAPs are enabled via `o_dbg_taps_en[14:0]`.


### TAP state definitions:

*   **Open**: The TAP is accessible via JTAG interface

*   **Locked**: The TAP is not accessible via JTAG interface, but it can be unlocked via the KSE3 using the challenge/response interface (Getchallenge and Unlockaccess commands sent by either the APU or KSE3 JTAG TAP)

*   **Closed**: The tap is not accessible via the JTAG interface and cannot be open.

*   **Forced**: The TAP state is forced (either Open or Closed) due to the specific LCS. The forcing can be done by the Secure Enclave HW (see OTP DFT TAP column) or KSE3 itself (See Debug TAPs column)


|     |     |     |     |     |
| --- | --- | --- | --- | --- |
| **LCS** | **KSE3 JTAG TAP allowed commands** | **OTP DFT TAP status** | **Debug TAPs (AIPU) status** | **Transition to the next state** |
| Chip wafer test | ALL | Open - forced by Secure Enclave HW | Open - forced by KSE3 and Secure Enclave HW due to LCS == chip_wafer_test * | Via KSE3 mailbox (APU or KSE3 JTAG TAP): send SetLifeCycle to Chip perso |
| Chip perso | ALL | Closed - forced by Secure Enclave HW | Open - forced by Secure Enclave HW due to LCS == chip_perso * | Via KSE3 mailbox (APU or KSE3 JTAG TAP): send SetLifeCycle to User delivery |
| User delivery (User perso)  <br>(customer) | Getchallenge,  <br>Unlockaccess | Closed - forced by Secure Enclave HW | Open/Locked. This is not forced due to LCS, but programmed by AXE via the KSE3 (SocSecurityConfig) in previous lifecycle states. | Via KSE3 mailbox (APU only): send SetLifeCycle to User secured |
| User secured  <br>(customer) | Getchallenge,  <br>Unlockaccess | Closed - forced by Secure Enclave HW | Locked. This is not forced due to LCS, but programmed by AXE via the KSE3 (SocSecurityConfig) in previous lifecycle states. | Via KSE3 mailbox (APU only): send SetLifeCycle to User decommissioned |
| User decommissioned  <br>(customer) | Getchallenge,  <br>Unlockaccess | Closed - forced by Secure Enclave HW | Locked. This is not forced due to LCS, but programmed by AXE via the KSE3 (SocSecurityConfig) in previous lifecycle states. | Via KSE3 mailbox (APU or KSE3 JTAG TAP), using UnlockAccess command only.<br><br>This specific UnlockAccess command requires a token from CA1, i.e. AXE to move to chip field return.  <br>Master key is erased before the LCS transition to chip field return effectively occurs.  <br>Note: there is no need to 1-ize (erase) the OTP because the OTP DFT TAP is still locked in this LCS and the transition to Chip field return must be performed by CA1 (AXE). Hence CA2 cannot read CA1 (AXE) secrets via OTP DFT TAP. |
| Chip field return | ALL, but Getchallenge and Unlockaccess will not work due to erased master key | Open - forced by Secure Enclave HW | Open - forced by KSE3 and Secure Enclave HW due to LCS == chip_field_return * | Via KSE3 mailbox (APU or KSE3 JTAG TAP) operation to change LCS to Terminated using SetLifeCycle.<br><br>This command is still working even if KSE3 master key has been erased.  <br>Note: In this state the bootloader 1.2 could read the AOR Plt_Config bits to check that LCS=chip_field_return to not perform boot. |
| Terminated  <br>(End of life) | NONE | Closed - forced by Secure Enclave HW | Closed - forced by KSE3 and Secure Enclave HW due to LCS == end_of_life * | N/A |

\* _forced by KSE3 and Secure Enclave HW:_ To speed up forcing the TAP status, the Secure Enclave overrides the TAP enable bits even if they match the value from KSE3. This is because the OTP wrapper reads the LCS out of reset and this is quicker than waiting for KSE to boot and populate AOR values.

**Note**: **Debug TAPs** are controlled by KSE3 AOR called soc_config, there are 16 independent bits in total, however bit 0 has fixed permissions that cannot be programmed but depend uniquely on the current LCS. This bit is not used in Europa, hence the effective granularity to independently control Debug TAPs is 15.
