/** @file
 *  @brief Header file for dwc_ddrphy_phyinit_LoadPieProdCode.c
 *  @addtogroup SrcFunc
 *  @{
 */

#ifndef _DWC_DDRPHY_PHYINIT_LOADPIEPRODCODE_H_
#define _DWC_DDRPHY_PHYINIT_LOADPIEPRODCODE_H_

#include <stdint.h>
#include <stddef.h>
/*! \def COUNTOF
 * \brief Calculate the number of elements of array a
 */
#define COUNTOF(a) (sizeof(a)/sizeof(a[0]))

// Must match pie_ext.c
/*! \def NORMAL_SECTION
 * \brief No jump or condition code
 */
#define NORMAL_SECTION                  0x00

/*! \def START_ADDRESS
 * \brief Jump to an address location
 */
#define START_ADDRESS                   0x01

/*! \def ENABLE_BITS_ANY_BITS
 * \brief Use code section if any enable bits match current configuration
 */
#define ENABLE_BITS_ANY_BITS            0x02

/*! \def ENABLE_BITS_NO_BITS
 * \brief Use code section if no enable bits match current configuration
 */
#define ENABLE_BITS_NO_BITS             0x03

/*! \def ENABLE_BITS_ALL_BITS
 * \brief Use code section only if all enable bits match current configuration
 */
#define ENABLE_BITS_ALL_BITS            0x04

/*! \def RESERVED_SECTION
 * \brief Jump to a relative location
 */
#define RESERVED_SECTION                0x05

/*! \def ENABLE_AND_DISABLE_BITS
 * \brief Use code section only if all enable bits and no disable bits match current configuration
 */
#define ENABLE_BITS_AND_DISABLE_BITS    0x06

// PIE/ACSM configuration enable bits (must match hwt_common_uctl.h)
/*! \def ENABLE_BITS_EN_FSP
 * \brief Defines FSP enable mode (pUserInputAdvanced->DisableFspOp==0)
 */
#define ENABLE_BITS_EN_FSP                                     (0x00000001u) // pUserInputAdvanced->DisableFspOp == 0

/*! \def ENABLE_BITS_ONE_RANK
 * \brief Defines one rank mode (pUserInputBasic->NumRank==1)
 */
#define ENABLE_BITS_ONE_RANK                                   (0x00000002u) // pUserInputBasic->NumRank == 1

/*! \def ENABLE_BITS_BYTE_MODE
 * \brief Defines byte mode (pUserInputBasic->DramDataWidth==8)
 */
#define ENABLE_BITS_BYTE_MODE                                  (0x00000004u) // pUserInputBasic->DramDataWidth == 8

/*! \def ENABLE_BITS_ZQ_MODE
 * \brief Defines ZQ mode ((msgBlk[pUserInputBasic->FirstPState].MR28_A0 & (1u << 5)) >> 5)
 */
#define ENABLE_BITS_ZQ_MODE                                    (0x00000008u) // (msgBlk[pUserInputBasic->FirstPState].MR28_A0 & (1u << 5)) >> 

/*! \def ENABLE_BITS_PPT2_EN
 * \brief Defines PPT2 enable (pUserInputAdvanced->RetrainMode[<any_pstate>] == 0x4u)
 */
#define ENABLE_BITS_PPT2_EN                                    (0x00000010u) // pUserInputAdvanced->RetrainMode[<any_pstate>] == 0x4u





/*! \def ENABLE_BITS_DFILOOPBACK_EN
 * \brief Defines DFI Loopback Enable ( pUserInputAdvanced->DfiLoopbackEn==1)
 */
#define ENABLE_BITS_DFILOOPBACK_EN                             (0x00000200u) // pUserInputAdvanced->DfiLoopbackEn==1    

/*! \def ENABLE_BITS_HALFTXCALCODE_EN
 * \brief Defines Half Tx Cal Code ( pUserInputAdvanced->HalfTxCalCode==1)
 */
#define ENABLE_BITS_HALFTXCALCODE_EN                           (0x00000400u) // pUserInputAdvanced->DfiLoopbackEn==1	

/*! \def ENABLE_BITS_SKIP_PWR_DN_IN_RETRAIN
 * \brief Defines Skip PDE/PDX in Retrain Only ( pUserInputAdvanced->SkipPwrDnInRetrain==1)
 */
#define ENABLE_BITS_SKIP_PWR_DN_IN_RETRAIN                     (0x00000800u) // pUserInputAdvanced->SkipPwrDnInRetrain==1	

/*! \def ENABLE_BITS_SNOOPWA_EN
 * \brief Defines SNOOP WA Enable ( pUserInputAdvanced->SnoopWAEn[<any_pstate>]==1)
 */
#define ENABLE_BITS_SNOOPWA_EN                                 (0x00001000u) //any of pUserInputAdvanced->SnoopWAEn[pstate] == 0x1


/*! \def ENABLE_BITS_TYPE_GENERAL
 * \brief Defines non-RTT_PARK mode bits
 */
#define ENABLE_BITS_TYPE_GENERAL            0

/*! \def ENABLE_BITS_TYPE_RTT_A
 * \brief Defines RTT_PARK mode bits
 */
#define ENABLE_BITS_TYPE_RTT                1

/*! \def ENABLE_BITS_TYPE_RTT_B
 * \brief Defines RTT_PARK mode bits for dummy MRRs
 */
#define ENABLE_BITS_TYPE_RTT_DUMMY          2

/// Internal structure that represents a contiguous code block in PIE/ACSM
typedef struct code_section {
    union {
        uint32_t start_address;  ///< Start address of code block
        uint32_t enable_bits;    ///< Enables code block based on matching current configuration
        uint32_t reserved_size;  ///< Relative jump length
        struct {
            uint16_t enable_bits_16;
            uint16_t disable_bits_16;
        };
    };
    uint16_t section_len;        ///< Length of the code block
    uint8_t enable_type;         ///< Index of the enable bits configuration
    uint8_t section_type;        ///< One of normal, start, or enable bits
} code_section_t;

/// Internal structure that represents one of the code blocks
typedef struct code_marker {
    uint16_t section_index;      ///< Which code section in the array of code sections
    uint32_t* marker_location;   ///< Address location of marker in PIE/ACSM code
    uint32_t* fixup_location;    ///< Call fixup marker in PIE/ACSM code, if needed
    uint16_t prog_ptr;           ///< Program pointer value
    uint16_t dyn_ptr;            ///< Dynamic pointer value
    char* descr_str;             ///< Description of this marker
} code_marker_t;

extern int dwc_ddrphy_phyinit_TestPIEProdEnableBits (phyinit_config_t* phyctx,
        uint32_t enable_bits, uint32_t disable_bits, int mode, uint8_t type);
extern void dwc_ddrphy_phyinit_LoadPIECodeSections (phyinit_config_t* phyctx,
        code_section_t* code_sections, size_t code_section_count,
        uint32_t* code_data, size_t code_data_count,
        code_marker_t* code_markers, size_t code_marker_count);
extern uint16_t dwc_ddrphy_phyinit_FindCodeMarkerIndex(uint32_t* var_array, uint16_t var_array_count,
                                                       uint16_t var_index, code_marker_t* marker_array,
                                                       uint16_t marker_count, uint16_t start_index);
extern uint32_t dwc_ddrphy_phyinit_ConvertFixupSramAddress(uint32_t fixup_value);
#endif // _DWC_DDRPHY_PHYINIT_LOADPIEPRODCODE_H_
/** @} */
