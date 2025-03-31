// (C) Copyright Axelera AI 2024
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: package, it contains the maps
// Owner: Vito Luca Guglielmi <vito.guglielmi@axelera.ai>
package tkn_mng_aic_agent_pkg;

    `include "uvm_macros.svh"
    import uvm_pkg::*;
    import token_manager_pkg::*;
    import token_mgr_mapping_aic_pkg::*;
    import token_agent_uvm_pkg::*;
    import tkn_mng_aic_ref_model_pkg::*;

    parameter int NR_LOC_DEVS = 18;
    parameter int MAX_NUM_PROD = 10;

    typedef string qstring[$];

    typedef enum {
        SWEP_OR_ACD,    //0
        M_IFD_0,        //1
        M_IFD_1,        //2
        M_IFD_2,        //3
        M_IFD_W,        //4
        M_ODR,          //5
        D_IFD_0,        //6
        D_IFD_1,        //7
        D_ODR,          //8
        M_MVMEXE,       //9
        M_MVMPRG,       //10
        M_IAU,          //11
        M_DPU,          //12
        D_DWPU,         //13
        D_IAU,          //14
        D_DPU,          //15
        HP_DMA_0,       //16
        HP_DMA_1,       //17
        NO_CONN         //18
    } TB_TKN_MNG_AIC_DEV_ENUM;



    //map dev to dev
    parameter TB_TKN_MNG_AIC_DEV_ENUM TKN_MNG_AIC_PROD_MAP[MAX_NUM_PROD][NR_LOC_DEVS] = '{
        '{SWEP_OR_ACD,  SWEP_OR_ACD,  SWEP_OR_ACD,    SWEP_OR_ACD,  SWEP_OR_ACD,  SWEP_OR_ACD,    SWEP_OR_ACD,    SWEP_OR_ACD,    SWEP_OR_ACD,    SWEP_OR_ACD,    SWEP_OR_ACD,    SWEP_OR_ACD,    SWEP_OR_ACD,    SWEP_OR_ACD,    SWEP_OR_ACD,    SWEP_OR_ACD,    SWEP_OR_ACD,    SWEP_OR_ACD},
        '{NO_CONN,      M_IFD_1,      M_IFD_0,        M_IFD_0,      M_IFD_0,      M_IFD_0,        M_IFD_0,        M_IFD_0,        M_IFD_0,        M_MVMPRG,       M_MVMEXE,       NO_CONN,        NO_CONN,        NO_CONN,        NO_CONN,        NO_CONN,        M_IFD_0,        M_IFD_0},
        '{NO_CONN,      M_IFD_2,      M_IFD_2,        M_IFD_1,      M_IFD_1,      M_IFD_1,        M_IFD_1,        M_IFD_1,        M_IFD_1,        NO_CONN,        NO_CONN,        NO_CONN,        NO_CONN,        NO_CONN,        NO_CONN,        NO_CONN,        M_IFD_1,        M_IFD_1},
        '{NO_CONN,      M_IFD_W,      M_IFD_W,        M_IFD_W,      M_IFD_2,      M_IFD_2,        M_IFD_2,        M_IFD_2,        M_IFD_2,        NO_CONN,        NO_CONN,        NO_CONN,        NO_CONN,        NO_CONN,        NO_CONN,        NO_CONN,        M_IFD_2,        M_IFD_2},
        '{NO_CONN,      M_ODR,        M_ODR,          M_ODR,        M_ODR,        M_IFD_W,        M_IFD_W,        M_IFD_W,        M_IFD_W,        NO_CONN,        NO_CONN,        NO_CONN,        NO_CONN,        NO_CONN,        NO_CONN,        NO_CONN,        M_IFD_W,        M_IFD_W},
        '{NO_CONN,      D_IFD_0,      D_IFD_0,        D_IFD_0,      D_IFD_0,      D_IFD_0,        M_ODR,          M_ODR,          M_ODR,          NO_CONN,        NO_CONN,        NO_CONN,        NO_CONN,        NO_CONN,        NO_CONN,        NO_CONN,        M_ODR,          M_ODR},
        '{NO_CONN,      D_IFD_1,      D_IFD_1,        D_IFD_1,      D_IFD_1,      D_IFD_1,        D_IFD_1,        D_IFD_0,        D_IFD_0,        NO_CONN,        NO_CONN,        NO_CONN,        NO_CONN,        NO_CONN,        NO_CONN,        NO_CONN,        D_IFD_0,        D_IFD_0},
        '{NO_CONN,      D_ODR,        D_ODR,          D_ODR,        D_ODR,        D_ODR,          D_ODR,          D_ODR,          D_IFD_1,        NO_CONN,        NO_CONN,        NO_CONN,        NO_CONN,        NO_CONN,        NO_CONN,        NO_CONN,        D_IFD_1,        D_IFD_1},
        '{NO_CONN,      HP_DMA_0,     HP_DMA_0,       HP_DMA_0,     HP_DMA_0,     HP_DMA_0,       HP_DMA_0,       HP_DMA_0,       HP_DMA_0,       NO_CONN,        NO_CONN,        NO_CONN,        NO_CONN,        NO_CONN,        NO_CONN,        NO_CONN,        D_ODR,          D_ODR},
        '{NO_CONN,      HP_DMA_1,     HP_DMA_1,       HP_DMA_1,     HP_DMA_1,     HP_DMA_1,       HP_DMA_1,       HP_DMA_1,       HP_DMA_1,       NO_CONN,        NO_CONN,        NO_CONN,        NO_CONN,        NO_CONN,        NO_CONN,        NO_CONN,        HP_DMA_1,       HP_DMA_0}
    };

parameter int unsigned DV_TKN_MNG_AIC_CONN_NUM [NR_LOC_DEVS] = '{
    1,  //SWEP_OR_ACD
    10, //M_IFD_0
    10, //M_IFD_1
    10, //M_IFD_2
    10, //M_IFD_W
    10, //M_ODR
    10, //D_IFD_0
    10, //D_IFD_1
    10, //D_ODR
    2,  //M_MVMEXE
    2,  //M_MVMPRG
    1,  //M_IAU
    1,  //M_DPU
    1,  //D_DWPU
    1,  //D_IAU
    1,  //D_DPU
    10, //HP_DMA_0
    10  //HP_DMA_1
};

parameter int unsigned DV_TKN_MNG_AIC_ACD_CONN_NUM = 18; //ACD devs



    // AIC Components
    `include "tkn_mng_aic_sequencer.svh"
    `include "tkn_mng_aic_agent.svh"

endpackage : tkn_mng_aic_agent_pkg

