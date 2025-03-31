/*
 * Copyright 2020 Google LLC
 * Copyright 2020 Andes Technology Co., Ltd.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

// 6. Configuration-Setting Instructions
`DEFINE_V_INSTR(VSETVLI,  VSET_FORMAT, CSR, RVV)
`DEFINE_V_INSTR(VSETIVLI, VSET_FORMAT, CSR, RVV, {}, UIMM)
`DEFINE_V_INSTR(VSETVL,   VSET_FORMAT, CSR, RVV)

// 7. Vector Loads and Stores
`DEFINE_V_INSTR(VLE_V,       VL_FORMAT,  LOAD,  RVV)
`DEFINE_V_INSTR(VSE_V,       VS_FORMAT,  STORE, RVV)
`DEFINE_V_INSTR(VLM_V,       VL_FORMAT,  LOAD,  RVV)
`DEFINE_V_INSTR(VSM_V,       VS_FORMAT,  STORE, RVV)
`DEFINE_V_INSTR(VLSE_V,      VLS_FORMAT, LOAD,  RVV)
`DEFINE_V_INSTR(VSSE_V,      VSS_FORMAT, STORE, RVV)
`DEFINE_V_INSTR(VLUXEI_V,    VLX_FORMAT, LOAD,  RVV)
`DEFINE_V_INSTR(VLOXEI_V,    VLX_FORMAT, LOAD,  RVV)
`DEFINE_V_INSTR(VSUXEI_V,    VSX_FORMAT, STORE, RVV)
`DEFINE_V_INSTR(VSOXEI_V,    VSX_FORMAT, STORE, RVV)
`DEFINE_V_INSTR(VLEFF_V,     VL_FORMAT,  LOAD,  RVV)
`DEFINE_V_INSTR(VLSEGE_V,    VL_FORMAT,  LOAD,  RVV)
`DEFINE_V_INSTR(VSSEGE_V,    VS_FORMAT,  STORE, RVV)
`DEFINE_V_INSTR(VLSEGEFF_V,  VL_FORMAT,  LOAD,  RVV)
`DEFINE_V_INSTR(VLSSEGE_V,   VLS_FORMAT, LOAD,  RVV)
`DEFINE_V_INSTR(VSSSEGE_V,   VSS_FORMAT, STORE, RVV)
`DEFINE_V_INSTR(VLUXSEGEI_V, VLX_FORMAT, LOAD,  RVV)
`DEFINE_V_INSTR(VLOXSEGEI_V, VLX_FORMAT, LOAD,  RVV)
`DEFINE_V_INSTR(VSUXSEGEI_V, VSX_FORMAT, STORE, RVV)
`DEFINE_V_INSTR(VSOXSEGEI_V, VSX_FORMAT, STORE, RVV)
`DEFINE_V_INSTR(VLRE_V,      VLR_FORMAT, LOAD,  RVV)
`DEFINE_V_INSTR(VSR_V,       VSR_FORMAT, STORE, RVV)

// 11. Vector Integer Arithmetic Instructions
`DEFINE_V_INSTR(VADD,      VA_FORMAT,  ARITHMETIC, RVV, {VV, VX, VI})
`DEFINE_V_INSTR(VSUB,      VA_FORMAT,  ARITHMETIC, RVV, {VV, VX})
`DEFINE_V_INSTR(VRSUB,     VA_FORMAT,  ARITHMETIC, RVV, {VX, VI})
`DEFINE_V_INSTR(VWADDU,    VA_FORMAT,  ARITHMETIC, RVV, {VV, VX, WV, WX})
`DEFINE_V_INSTR(VWSUBU,    VA_FORMAT,  ARITHMETIC, RVV, {VV, VX, WV, WX})
`DEFINE_V_INSTR(VWADD,     VA_FORMAT,  ARITHMETIC, RVV, {VV, VX, WV, WX})
`DEFINE_V_INSTR(VWSUB,     VA_FORMAT,  ARITHMETIC, RVV, {VV, VX, WV, WX})
`DEFINE_V_INSTR(VZEXT_VF2, VS2_FORMAT, ARITHMETIC, RVV)
`DEFINE_V_INSTR(VZEXT_VF4, VS2_FORMAT, ARITHMETIC, RVV)
`DEFINE_V_INSTR(VZEXT_VF8, VS2_FORMAT, ARITHMETIC, RVV)
`DEFINE_V_INSTR(VSEXT_VF2, VS2_FORMAT, ARITHMETIC, RVV)
`DEFINE_V_INSTR(VSEXT_VF4, VS2_FORMAT, ARITHMETIC, RVV)
`DEFINE_V_INSTR(VSEXT_VF8, VS2_FORMAT, ARITHMETIC, RVV)
`DEFINE_V_INSTR(VADC,      VA_FORMAT,  ARITHMETIC, RVV, {VVM, VXM, VIM})
`DEFINE_V_INSTR(VMADC,     VA_FORMAT,  ARITHMETIC, RVV, {VVM, VXM, VIM, VV, VX, VI})
`DEFINE_V_INSTR(VSBC,      VA_FORMAT,  ARITHMETIC, RVV, {VVM, VXM})
`DEFINE_V_INSTR(VMSBC,     VA_FORMAT,  ARITHMETIC, RVV, {VVM, VXM, VV, VX})
`DEFINE_V_INSTR(VAND,      VA_FORMAT,  LOGICAL,    RVV, {VV, VX, VI})
`DEFINE_V_INSTR(VOR,       VA_FORMAT,  LOGICAL,    RVV, {VV, VX, VI})
`DEFINE_V_INSTR(VXOR,      VA_FORMAT,  LOGICAL,    RVV, {VV, VX, VI})
`DEFINE_V_INSTR(VSLL,      VA_FORMAT,  SHIFT,      RVV, {VV, VX, VI}, UIMM)
`DEFINE_V_INSTR(VSRL,      VA_FORMAT,  SHIFT,      RVV, {VV, VX, VI}, UIMM)
`DEFINE_V_INSTR(VSRA,      VA_FORMAT,  SHIFT,      RVV, {VV, VX, VI}, UIMM)
`DEFINE_V_INSTR(VNSRL,     VA_FORMAT,  SHIFT,      RVV, {WV, WX, WI}, UIMM)
`DEFINE_V_INSTR(VNSRA,     VA_FORMAT,  SHIFT,      RVV, {WV, WX, WI}, UIMM)
`DEFINE_V_INSTR(VMSEQ,     VA_FORMAT,  COMPARE,    RVV, {VV, VX, VI})
`DEFINE_V_INSTR(VMSNE,     VA_FORMAT,  COMPARE,    RVV, {VV, VX, VI})
`DEFINE_V_INSTR(VMSLTU,    VA_FORMAT,  COMPARE,    RVV, {VV, VX})
`DEFINE_V_INSTR(VMSLT,     VA_FORMAT,  COMPARE,    RVV, {VV, VX})
`DEFINE_V_INSTR(VMSLEU,    VA_FORMAT,  COMPARE,    RVV, {VV, VX, VI})
`DEFINE_V_INSTR(VMSLE,     VA_FORMAT,  COMPARE,    RVV, {VV, VX, VI})
`DEFINE_V_INSTR(VMSGTU,    VA_FORMAT,  COMPARE,    RVV, {VX, VI})
`DEFINE_V_INSTR(VMSGT,     VA_FORMAT,  COMPARE,    RVV, {VX, VI})
`DEFINE_V_INSTR(VMINU,     VA_FORMAT,  ARITHMETIC, RVV, {VV, VX})
`DEFINE_V_INSTR(VMIN,      VA_FORMAT,  ARITHMETIC, RVV, {VV, VX})
`DEFINE_V_INSTR(VMAXU,     VA_FORMAT,  ARITHMETIC, RVV, {VV, VX})
`DEFINE_V_INSTR(VMAX,      VA_FORMAT,  ARITHMETIC, RVV, {VV, VX})
`DEFINE_V_INSTR(VMUL,      VA_FORMAT,  ARITHMETIC, RVV, {VV, VX})
`DEFINE_V_INSTR(VMULH,     VA_FORMAT,  ARITHMETIC, RVV, {VV, VX})
`DEFINE_V_INSTR(VMULHU,    VA_FORMAT,  ARITHMETIC, RVV, {VV, VX})
`DEFINE_V_INSTR(VMULHSU,   VA_FORMAT,  ARITHMETIC, RVV, {VV, VX})
`DEFINE_V_INSTR(VDIVU,     VA_FORMAT,  ARITHMETIC, RVV, {VV, VX})
`DEFINE_V_INSTR(VDIV,      VA_FORMAT,  ARITHMETIC, RVV, {VV, VX})
`DEFINE_V_INSTR(VREMU,     VA_FORMAT,  ARITHMETIC, RVV, {VV, VX})
`DEFINE_V_INSTR(VREM,      VA_FORMAT,  ARITHMETIC, RVV, {VV, VX})
`DEFINE_V_INSTR(VWMUL,     VA_FORMAT,  ARITHMETIC, RVV, {VV, VX})
`DEFINE_V_INSTR(VWMULU,    VA_FORMAT,  ARITHMETIC, RVV, {VV, VX})
`DEFINE_V_INSTR(VWMULSU,   VA_FORMAT,  ARITHMETIC, RVV, {VV, VX})
`DEFINE_V_INSTR(VMACC,     VA_FORMAT,  ARITHMETIC, RVV, {VV, VX})
`DEFINE_V_INSTR(VNMSAC,    VA_FORMAT,  ARITHMETIC, RVV, {VV, VX})
`DEFINE_V_INSTR(VMADD,     VA_FORMAT,  ARITHMETIC, RVV, {VV, VX})
`DEFINE_V_INSTR(VNMSUB,    VA_FORMAT,  ARITHMETIC, RVV, {VV, VX})
`DEFINE_V_INSTR(VWMACCU,   VA_FORMAT,  ARITHMETIC, RVV, {VV, VX})
`DEFINE_V_INSTR(VWMACC,    VA_FORMAT,  ARITHMETIC, RVV, {VV, VX})
`DEFINE_V_INSTR(VWMACCSU,  VA_FORMAT,  ARITHMETIC, RVV, {VV, VX})
`DEFINE_V_INSTR(VWMACCUS,  VA_FORMAT,  ARITHMETIC, RVV, {VX})
`DEFINE_V_INSTR(VMERGE,    VA_FORMAT,  ARITHMETIC, RVV, {VVM, VXM, VIM})
`DEFINE_V_INSTR(VMV_V_V,   VA_FORMAT,  ARITHMETIC, RVV)
`DEFINE_V_INSTR(VMV_V_X,   VA_FORMAT,  ARITHMETIC, RVV)
`DEFINE_V_INSTR(VMV_V_I,   VA_FORMAT,  ARITHMETIC, RVV)

// 12. Vector Fixed-Point Arithmetic Instructions
`DEFINE_V_INSTR(VSADDU,  VA_FORMAT, ARITHMETIC, RVV, {VV, VX, VI})
`DEFINE_V_INSTR(VSADD,   VA_FORMAT, ARITHMETIC, RVV, {VV, VX, VI})
`DEFINE_V_INSTR(VSSUBU,  VA_FORMAT, ARITHMETIC, RVV, {VV, VX})
`DEFINE_V_INSTR(VSSUB,   VA_FORMAT, ARITHMETIC, RVV, {VV, VX})
`DEFINE_V_INSTR(VAADDU,  VA_FORMAT, ARITHMETIC, RVV, {VV, VX})
`DEFINE_V_INSTR(VAADD,   VA_FORMAT, ARITHMETIC, RVV, {VV, VX})
`DEFINE_V_INSTR(VASUBU,  VA_FORMAT, ARITHMETIC, RVV, {VV, VX})
`DEFINE_V_INSTR(VASUB,   VA_FORMAT, ARITHMETIC, RVV, {VV, VX})
`DEFINE_V_INSTR(VSMUL,   VA_FORMAT, ARITHMETIC, RVV, {VV, VX})
`DEFINE_V_INSTR(VSSRL,   VA_FORMAT, SHIFT,      RVV, {VV, VX, VI}, UIMM)
`DEFINE_V_INSTR(VSSRA,   VA_FORMAT, SHIFT,      RVV, {VV, VX, VI}, UIMM)
`DEFINE_V_INSTR(VNCLIPU, VA_FORMAT, ARITHMETIC, RVV, {WV, WX, WI}, UIMM)
`DEFINE_V_INSTR(VNCLIP,  VA_FORMAT, ARITHMETIC, RVV, {WV, WX, WI}, UIMM)

// 13. Vector Floating-Point Instructions
`DEFINE_V_INSTR(VFADD,             VA_FORMAT,  ARITHMETIC, RVV, {VV, VF})
`DEFINE_V_INSTR(VFSUB,             VA_FORMAT,  ARITHMETIC, RVV, {VV, VF})
`DEFINE_V_INSTR(VFRSUB,            VA_FORMAT,  ARITHMETIC, RVV, {VF})
`DEFINE_V_INSTR(VFWADD,            VA_FORMAT,  ARITHMETIC, RVV, {VV, VF, WV, WF})
`DEFINE_V_INSTR(VFWSUB,            VA_FORMAT,  ARITHMETIC, RVV, {VV, VF, WV, WF})
`DEFINE_V_INSTR(VFMUL,             VA_FORMAT,  ARITHMETIC, RVV, {VV, VF})
`DEFINE_V_INSTR(VFDIV,             VA_FORMAT,  ARITHMETIC, RVV, {VV, VF})
`DEFINE_V_INSTR(VFRDIV,            VA_FORMAT,  ARITHMETIC, RVV, {VF})
`DEFINE_V_INSTR(VFWMUL,            VA_FORMAT,  ARITHMETIC, RVV, {VV, VF})
`DEFINE_V_INSTR(VFMACC,            VA_FORMAT,  ARITHMETIC, RVV, {VV, VF})
`DEFINE_V_INSTR(VFNMACC,           VA_FORMAT,  ARITHMETIC, RVV, {VV, VF})
`DEFINE_V_INSTR(VFMSAC,            VA_FORMAT,  ARITHMETIC, RVV, {VV, VF})
`DEFINE_V_INSTR(VFNMSAC,           VA_FORMAT,  ARITHMETIC, RVV, {VV, VF})
`DEFINE_V_INSTR(VFMADD,            VA_FORMAT,  ARITHMETIC, RVV, {VV, VF})
`DEFINE_V_INSTR(VFNMADD,           VA_FORMAT,  ARITHMETIC, RVV, {VV, VF})
`DEFINE_V_INSTR(VFMSUB,            VA_FORMAT,  ARITHMETIC, RVV, {VV, VF})
`DEFINE_V_INSTR(VFNMSUB,           VA_FORMAT,  ARITHMETIC, RVV, {VV, VF})
`DEFINE_V_INSTR(VFWMACC,           VA_FORMAT,  ARITHMETIC, RVV, {VV, VF})
`DEFINE_V_INSTR(VFWNMACC,          VA_FORMAT,  ARITHMETIC, RVV, {VV, VF})
`DEFINE_V_INSTR(VFWMSAC,           VA_FORMAT,  ARITHMETIC, RVV, {VV, VF})
`DEFINE_V_INSTR(VFWNMSAC,          VA_FORMAT,  ARITHMETIC, RVV, {VV, VF})
`DEFINE_V_INSTR(VFSQRT_V,          VS2_FORMAT, ARITHMETIC, RVV)
`DEFINE_V_INSTR(VFRSQRT7_V,        VS2_FORMAT, ARITHMETIC, RVV)
`DEFINE_V_INSTR(VFREC7_V,          VS2_FORMAT, ARITHMETIC, RVV)
`DEFINE_V_INSTR(VFMIN,             VA_FORMAT,  ARITHMETIC, RVV, {VV, VF})
`DEFINE_V_INSTR(VFMAX,             VA_FORMAT,  ARITHMETIC, RVV, {VV, VF})
`DEFINE_V_INSTR(VFSGNJ,            VA_FORMAT,  ARITHMETIC, RVV, {VV, VF})
`DEFINE_V_INSTR(VFSGNJN,           VA_FORMAT,  ARITHMETIC, RVV, {VV, VF})
`DEFINE_V_INSTR(VFSGNJX,           VA_FORMAT,  ARITHMETIC, RVV, {VV, VF})
`DEFINE_V_INSTR(VMFEQ,             VA_FORMAT,  COMPARE,    RVV, {VV, VF})
`DEFINE_V_INSTR(VMFNE,             VA_FORMAT,  COMPARE,    RVV, {VV, VF})
`DEFINE_V_INSTR(VMFLT,             VA_FORMAT,  COMPARE,    RVV, {VV, VF})
`DEFINE_V_INSTR(VMFLE,             VA_FORMAT,  COMPARE,    RVV, {VV, VF})
`DEFINE_V_INSTR(VMFGT,             VA_FORMAT,  COMPARE,    RVV, {VF})
`DEFINE_V_INSTR(VMFGE,             VA_FORMAT,  COMPARE,    RVV, {VF})
`DEFINE_V_INSTR(VFCLASS_V,         VS2_FORMAT, ARITHMETIC, RVV)
`DEFINE_V_INSTR(VFMERGE,           VA_FORMAT,  ARITHMETIC, RVV, {VFM})
`DEFINE_V_INSTR(VFMV_V_F,          VA_FORMAT,  ARITHMETIC, RVV)
`DEFINE_V_INSTR(VFCVT_XU_F_V,      VS2_FORMAT, ARITHMETIC, RVV)
`DEFINE_V_INSTR(VFCVT_X_F_V,       VS2_FORMAT, ARITHMETIC, RVV)
`DEFINE_V_INSTR(VFCVT_RTZ_XU_F_V,  VS2_FORMAT, ARITHMETIC, RVV)
`DEFINE_V_INSTR(VFCVT_RTZ_X_F_V,   VS2_FORMAT, ARITHMETIC, RVV)
`DEFINE_V_INSTR(VFCVT_F_XU_V,      VS2_FORMAT, ARITHMETIC, RVV)
`DEFINE_V_INSTR(VFCVT_F_X_V,       VS2_FORMAT, ARITHMETIC, RVV)
`DEFINE_V_INSTR(VFWCVT_XU_F_V,     VS2_FORMAT, ARITHMETIC, RVV)
`DEFINE_V_INSTR(VFWCVT_X_F_V,      VS2_FORMAT, ARITHMETIC, RVV)
`DEFINE_V_INSTR(VFWCVT_RTZ_XU_F_V, VS2_FORMAT, ARITHMETIC, RVV)
`DEFINE_V_INSTR(VFWCVT_RTZ_X_F_V,  VS2_FORMAT, ARITHMETIC, RVV)
`DEFINE_V_INSTR(VFWCVT_F_XU_V,     VS2_FORMAT, ARITHMETIC, RVV)
`DEFINE_V_INSTR(VFWCVT_F_X_V,      VS2_FORMAT, ARITHMETIC, RVV)
`DEFINE_V_INSTR(VFWCVT_F_F_V,      VS2_FORMAT, ARITHMETIC, RVV)
`DEFINE_V_INSTR(VFNCVT_XU_F_W,     VS2_FORMAT, ARITHMETIC, RVV)
`DEFINE_V_INSTR(VFNCVT_X_F_W,      VS2_FORMAT, ARITHMETIC, RVV)
`DEFINE_V_INSTR(VFNCVT_RTZ_XU_F_W, VS2_FORMAT, ARITHMETIC, RVV)
`DEFINE_V_INSTR(VFNCVT_RTZ_X_F_W,  VS2_FORMAT, ARITHMETIC, RVV)
`DEFINE_V_INSTR(VFNCVT_F_XU_W,     VS2_FORMAT, ARITHMETIC, RVV)
`DEFINE_V_INSTR(VFNCVT_F_X_W,      VS2_FORMAT, ARITHMETIC, RVV)
`DEFINE_V_INSTR(VFNCVT_F_F_W,      VS2_FORMAT, ARITHMETIC, RVV)
`DEFINE_V_INSTR(VFNCVT_ROD_F_F_W,  VS2_FORMAT, ARITHMETIC, RVV)

// 14. Vector Reduction Instructions
`DEFINE_V_INSTR(VREDSUM_VS,    VA_FORMAT, ARITHMETIC, RVV)
`DEFINE_V_INSTR(VREDMAXU_VS,   VA_FORMAT, ARITHMETIC, RVV)
`DEFINE_V_INSTR(VREDMAX_VS,    VA_FORMAT, ARITHMETIC, RVV)
`DEFINE_V_INSTR(VREDMINU_VS,   VA_FORMAT, ARITHMETIC, RVV)
`DEFINE_V_INSTR(VREDMIN_VS,    VA_FORMAT, ARITHMETIC, RVV)
`DEFINE_V_INSTR(VREDAND_VS,    VA_FORMAT, ARITHMETIC, RVV)
`DEFINE_V_INSTR(VREDOR_VS,     VA_FORMAT, ARITHMETIC, RVV)
`DEFINE_V_INSTR(VREDXOR_VS,    VA_FORMAT, ARITHMETIC, RVV)
`DEFINE_V_INSTR(VWREDSUMU_VS,  VA_FORMAT, ARITHMETIC, RVV)
`DEFINE_V_INSTR(VWREDSUM_VS,   VA_FORMAT, ARITHMETIC, RVV)
`DEFINE_V_INSTR(VFREDOSUM_VS,  VA_FORMAT, ARITHMETIC, RVV)
`DEFINE_V_INSTR(VFREDUSUM_VS,  VA_FORMAT, ARITHMETIC, RVV)
`DEFINE_V_INSTR(VFREDMAX_VS,   VA_FORMAT, ARITHMETIC, RVV)
`DEFINE_V_INSTR(VFREDMIN_VS,   VA_FORMAT, ARITHMETIC, RVV)
`DEFINE_V_INSTR(VFWREDOSUM_VS, VA_FORMAT, ARITHMETIC, RVV)
`DEFINE_V_INSTR(VFWREDUSUM_VS, VA_FORMAT, ARITHMETIC, RVV)

// 15. Vector Mask Instructions
`DEFINE_V_INSTR(VMAND_MM,  VA_FORMAT,  LOGICAL,    RVV)
`DEFINE_V_INSTR(VMNAND_MM, VA_FORMAT,  LOGICAL,    RVV)
`DEFINE_V_INSTR(VMANDN_MM, VA_FORMAT,  LOGICAL,    RVV)
`DEFINE_V_INSTR(VMXOR_MM,  VA_FORMAT,  LOGICAL,    RVV)
`DEFINE_V_INSTR(VMOR_MM,   VA_FORMAT,  LOGICAL,    RVV)
`DEFINE_V_INSTR(VMNOR_MM,  VA_FORMAT,  LOGICAL,    RVV)
`DEFINE_V_INSTR(VMORN_MM,  VA_FORMAT,  LOGICAL,    RVV)
`DEFINE_V_INSTR(VMXNOR_MM, VA_FORMAT,  LOGICAL,    RVV)
`DEFINE_V_INSTR(VCPOP_M,   VS2_FORMAT, ARITHMETIC, RVV)
`DEFINE_V_INSTR(VFIRST_M,  VS2_FORMAT, ARITHMETIC, RVV)
`DEFINE_V_INSTR(VMSBF_M,   VS2_FORMAT, ARITHMETIC, RVV)
`DEFINE_V_INSTR(VMSIF_M,   VS2_FORMAT, ARITHMETIC, RVV)
`DEFINE_V_INSTR(VMSOF_M,   VS2_FORMAT, ARITHMETIC, RVV)
`DEFINE_V_INSTR(VIOTA_M,   VS2_FORMAT, ARITHMETIC, RVV)
`DEFINE_V_INSTR(VID_V,     VS2_FORMAT, ARITHMETIC, RVV)

// 16. Vector Permutation Instructions
`DEFINE_V_INSTR(VMV_X_S,      VA_FORMAT,  ARITHMETIC, RVV)
`DEFINE_V_INSTR(VMV_S_X,      VA_FORMAT,  ARITHMETIC, RVV)
`DEFINE_V_INSTR(VFMV_F_S,     VA_FORMAT,  ARITHMETIC, RVV)
`DEFINE_V_INSTR(VFMV_S_F,     VA_FORMAT,  ARITHMETIC, RVV)
`DEFINE_V_INSTR(VSLIDEUP,     VA_FORMAT,  ARITHMETIC, RVV, {VX, VI}, UIMM)
`DEFINE_V_INSTR(VSLIDEDOWN,   VA_FORMAT,  ARITHMETIC, RVV, {VX, VI}, UIMM)
`DEFINE_V_INSTR(VSLIDE1UP,    VA_FORMAT,  ARITHMETIC, RVV, {VX})
`DEFINE_V_INSTR(VSLIDE1DOWN,  VA_FORMAT,  ARITHMETIC, RVV, {VX})
`DEFINE_V_INSTR(VFSLIDE1UP,   VA_FORMAT,  ARITHMETIC, RVV, {VF})
`DEFINE_V_INSTR(VFSLIDE1DOWN, VA_FORMAT,  ARITHMETIC, RVV, {VF})
`DEFINE_V_INSTR(VRGATHER,     VA_FORMAT,  ARITHMETIC, RVV, {VV, VX, VI}, UIMM)
`DEFINE_V_INSTR(VRGATHEREI16, VA_FORMAT,  ARITHMETIC, RVV, {VV})
`DEFINE_V_INSTR(VCOMPRESS,    VA_FORMAT,  ARITHMETIC, RVV, {VM})
`DEFINE_V_INSTR(VMV1R_V,      VS2_FORMAT, ARITHMETIC, RVV)
`DEFINE_V_INSTR(VMV2R_V,      VS2_FORMAT, ARITHMETIC, RVV)
`DEFINE_V_INSTR(VMV4R_V,      VS2_FORMAT, ARITHMETIC, RVV)
`DEFINE_V_INSTR(VMV8R_V,      VS2_FORMAT, ARITHMETIC, RVV)
