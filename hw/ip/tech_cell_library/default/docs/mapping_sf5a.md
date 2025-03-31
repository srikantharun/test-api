---
title: "Mappings SF5A"
doc:
  status: draft
  version: [0, 0, 0]
  confidentiality: internal
rtl:
  sv:
    tech_cell_library:
      bender:
        hw/ip/tech_cell_library/default/rtl/Bender.yml
---

This is the implemented mapping between the `tc_*` wrappers and the `sf5a` technology mode.

!!! info "Bender targets"

    To use these mappings the following targets need to be specified in the bender command:

    * `asic`
    * `sf5a`


!!! tip "Naming convention on library cell instances"

    Module instances of the underlying `sf5a` instantiation follow the convention:

    ```
    u_tc_lib_<category>_<primitive>
    ```

    For the categories:
    * `clk`
    * `seq`
    * `std`

    This convention might be used for example to force a size-only setting on these cells.


## axe_tcl_clk

Used  `svt` library `ln05lpe_sc_s6t_flk_lvt_c54_a00_V3.10`.

| Name                 | Note          | Cells                                              |
|:-------------------- |:------------- |:-------------------------------------------------- |
| axe_tcl_clk_buffer   | INV -> INV    | CLKINV_D4_N_S6TL_C54L08 -> CLKINV_D8_N_S6TL_C54L08 |
| axe_tcl_clk_inverter | INV           | CLKINV_D8_N_S6TL_C54L08                            |
| axe_tcl_clk_and2     | NAND -> INV   | NAND2_D4_N_S6TL_C54L08  -> CLKINV_D8_N_S6TL_C54L08 |
| axe_tcl_clk_or2      | NOR -> INV    | NOR2_D4_N_S6TL_C54L08   -> CLKINV_D8_N_S6TL_C54L08 |
| axe_tcl_clk_xor2     | XNOR -> INV   | XNOR2_D4_N_S6TL_C54L08  -> CLKINV_D8_N_S6TL_C54L08 |
| axe_tcl_clk_mux2     | tristate-like | MXT2_D6_N_S6TL_C54L08                              |
| axe_tcl_clk_gating   | GATE          | PREICG_D8_N_S6TL_C54L08                            |
||||


## axe_tcl_pad

TODO(@wolfgang.roenninger): Implement pad mappings

| Name            | Description | Cells |
|:--------------- |:----------- |:----- |
||||

## axe_tcl_seq

Used `svt` library `ln05lpe_sc_s6t_flk_lvt_c54_a00_V3.10` and for the reset inverter `rvt` library
`ln05lpe_sc_s6t_flk_rvt_c54_a00_V3.10`.

| Name             | SyncStages | ResetValue | Note     | Cells                                                        |
|:---------------- |:---------- |:---------- |:-------- |:------------------------------------------------------------ |
| axe_tcl_seq_sync | 2          | 0          | RST HIGH | SDFFYRPQ2DRLV_D1_N_S6TL_C54L08 <--RST-- INV_D1_N_S6TR_C54L08 |
| axe_tcl_seq_sync | 2          | 1          | SET LOW  | SDFFYSQ2DRLV_D1_N_S6TL_C54L08                                |
| axe_tcl_seq_sync | 3          | 0          | RST HIGH | SDFFYRPQ3DRLV_D1_N_S6TL_C54L08 <--RST-- INV_D1_N_S6TR_C54L08 |
| axe_tcl_seq_sync | 3          | 1          | SET LOW  | SDFFYSQ3DRLV_D1_N_S6TL_C54L08                                |
| axe_tcl_seq_sync | 4          | 0          | RST HIGH | SDFFYRPQ4DRLV_D1_N_S6TL_C54L08 <--RST-- INV_D1_N_S6TR_C54L08 |
| axe_tcl_seq_sync | 4          | 1          | SET LOW  | SDFFYSQ4DRLV_D1_N_S6TL_C54L08                                |
||||||

## axe_tcl_sram

TODO(@wolfgang.roenninger): Add table for the used macros

| Name            | Description | Cells |
|:--------------- |:----------- |:----- |
||||

## axe_tcl_std

Used `rvt` library `ln05lpe_sc_s6t_flk_rvt_c54_a00_V3.10`.

| Name                 | Note          | Cells                                          |
|:-------------------- |:------------- |:---------------------------------------------- |
| axe_tcl_std_buffer   | BUF           | BUF_D4_N_S6TR_C54L08                           |
| axe_tcl_std_inverter | INV           | INV_D4_N_S6TR_C54L08                           |
| axe_tcl_std_and2     | NAND -> INV   | NAND2_D2_N_S6TR_C54L08 -> INV_D4_N_S6TR_C54L08 |
| axe_tcl_std_and3     | NAND -> INV   | NAND3_D2_N_S6TR_C54L08 -> INV_D4_N_S6TR_C54L08 |
| axe_tcl_std_nand2    | NAND          | NAND2_D2_N_S6TR_C54L08                         |
| axe_tcl_std_nand3    | NAND          | NAND3_D2_N_S6TR_C54L08                         |
| axe_tcl_std_or2      | NOR -> INV    | NOR2_D2_N_S6TR_C54L08  -> INV_D4_N_S6TR_C54L08 |
| axe_tcl_std_or3      | NOR -> INV    | NOR3_D2_N_S6TR_C54L08  -> INV_D4_N_S6TR_C54L08 |
| axe_tcl_std_nor2     | NOR           | NOR3_D2_N_S6TR_C54L08                          |
| axe_tcl_std_nor3     | NOR           | NOR3_D2_N_S6TR_C54L08                          |
| axe_tcl_std_xor2     | XOR           | XOR2_D2_N_S6TR_C54L08                          |
| axe_tcl_std_xor3     | XOR           | XOR3_D2_N_S6TR_C54L08                          |
| axe_tcl_std_xnor2    | XNOR          | XNOR2_D2_N_S6TR_C54L08                         |
| axe_tcl_std_xnor3    | XNOR          | XNOR3_D2_N_S6TR_C54L08                         |
| axe_tcl_std_mux2     | tristate-like | MXT2_D2_N_S6TR_C54L08                          |
||||
