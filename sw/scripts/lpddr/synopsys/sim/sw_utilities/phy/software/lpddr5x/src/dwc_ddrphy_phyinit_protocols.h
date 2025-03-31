

/** \file dwc_ddrphy_phyinit_protocols.h
 *  \brief This file defines which protocol(s) to support in PhyInit
 */

#ifndef _DWC_DDRPHY_PHYINIT_PROTOCOLS_H_
#define _DWC_DDRPHY_PHYINIT_PROTOCOLS_H_

#if defined(_BUILD_LPDDR4X) && !defined(_BUILD_LPDDR4)
///< LPDDR4 protocol defined
#define _BUILD_LPDDR4
#endif

#if defined(_BUILD_LPDDR5X) && !defined(_BUILD_LPDDR5)
///< LPDDR5 protocol defined
#define _BUILD_LPDDR5
#endif

#if !defined(_BUILD_LPDDR4) && !defined(_BUILD_LPDDR5) && !defined(_BUILD_DDR5) && !defined(_BUILD_DDR5R) && !defined(_BUILD_DDR5LR)
#error "You must define at least one protocol (LPDDR4 or LPDDR5 or DDR5 or DDR5R Or DDR5LR)"
#endif

///< Only one protocol defined
#define _SINGLE_PROTOCOL ((!_BUILD_LPDDR4 && !_BUILD_LPDDR5 && _BUILD_DDR5 && !_BUILD_DDR5R && !_BUILD_DDR5LR)||(!_BUILD_LPDDR4 && _BUILD_LPDDR5 && !_BUILD_DDR5 && !_BUILD_DDR5R && !_BUILD_DDR5LR)||(_BUILD_LPDDR4 && !_BUILD_LPDDR5 && !_BUILD_DDR5 && !_BUILD_DDR5R && !_BUILD_DDR5LR)||(!_BUILD_LPDDR4 && !_BUILD_LPDDR5 && !_BUILD_DDR5 && _BUILD_DDR5R && !_BUILD_DDR5LR)||(!_BUILD_LPDDR4 && !_BUILD_LPDDR5 && !_BUILD_DDR5 && !_BUILD_DDR5R && _BUILD_DDR5LR))

#ifndef _SINGLE_PROTOCOL
DramType_t DramType;
#endif

#if !defined(_SINGLE_PROTOCOL) && defined(_BUILD_LPDDR4)
///< Macro for if(LPDDR4) code
#define _IF_LPDDR4(input) if (DramType == LPDDR4) { input}
#elif defined(_BUILD_LPDDR4)
///< Macro for if(LPDDR4) code
#define _IF_LPDDR4(input) input
#else
///< Macro for if(LPDDR4) code
#define _IF_LPDDR4(input)
#endif

#if !defined(_SINGLE_PROTOCOL) && defined(_BUILD_LPDDR5)
///< Macro for if(LPDDR5) code
#define _IF_LPDDR5(input) if (DramType == LPDDR5) { input}
#elif defined(_BUILD_LPDDR5)
///< Macro for if(LPDDR5) code
#define _IF_LPDDR5(input) input
#else
///< Macro for if(LPDDR5) code
#define _IF_LPDDR5(input)
#endif

#if defined(_BUILD_LPDDR5) || defined(_BUILD_LPDDR4)
///< Macro to skip CK1 in PhyInit programming
#define _SKIP_DIFF_CK1_LP5_LP4_ONLY(input) if (input == 6) { continue; }
#elif defined(_BUILD_DDR5)
///< Macro to skip CK1 in PhyInit programming
#define _SKIP_DIFF_CK1_LP5_LP4_ONLY(input)
#endif

#if defined(_BUILD_LPDDR5) || defined(_BUILD_LPDDR4)
///< Macro to skip CK1 in PhyInit programming
#define _SKIP_DIFF_CK0_AC11_D5_ONLY(input1,input2,input3)
#elif defined(_BUILD_DDR5)
///< Macro to skip CK1 in PhyInit programming
#define _SKIP_DIFF_CK0_AC11_D5_ONLY(input1,input2,input3) if ((input1 ==6 && input2 == 1 && input3 ==9)) { break; }
///< Macro to skip upper nibble programming in configs with Nibble ECC - as part of a loop
#define _SKIP_UPPER_NIBBLE_D5_ONLY(input1,input2)  if ((input1 ==  4 || input1 == 9) && (input2 == 1)) {continue; }
///< Macro to skip upper nibble programming in configs with Nibble ECC - but skipping only one line of programming
#define _SKIP_UPPER_NIBBLE_D5_ONLY_OL(input1,input2)  if (!((input1 ==  4 || input1 == 9) && (input2 == 1)))
#endif

#if defined(_BUILD_LPDDR5) || defined(_BUILD_LPDDR4)
///< Macro to program DTO when enabled
#define _PROG_DTO(dtoEn, acx, hmac, csrname, addr, value) if (dtoEn==1 && hmac==0 && acx==0) { \
  dwc_ddrphy_phyinit_cmnt ("[%s] Programming ACX%d HMAC%d Instance%d %s to 0x%x\n", __func__, 0, 14, 14, csrname, value); \
  dwc_ddrphy_phyinit_io_write32(addr, value); \
}
#elif defined(_BUILD_DDR5)
#define _PROG_DTO(dtoEn, acx, hmac, csrname, addr, value)
#endif



#if !defined(_SINGLE_PROTOCOL) && defined(_BUILD_DDR5)
///< Macro for if(DDR5) code
#define _IF_DDR5(input) if (DramType == DDR5) { input}
#elif defined(_BUILD_DDR5)
///< Macro for if(DDR5) code
#define _IF_DDR5(input) input
#else
///< Macro for if(DDR5) code
#define _IF_DDR5(input)
#endif

#if !defined(_SINGLE_PROTOCOL) && defined(_BUILD_DDR5R)
///< Macro for if(DDR5R) code
#define _IF_DDR5R(input) if (DramType == DDR5R) { input}
#elif defined(_BUILD_DDR5R)
///< Macro for if(DDR5R) code
#define _IF_DDR5R(input) input
#else
///< Macro for if(DDR5R) code
#define _IF_DDR5R(input)
#endif

#if !defined(_SINGLE_PROTOCOL) && defined(_BUILD_DDR5LR)
///< Macro for if(DDR5LR) code
#define _IF_DDR5LR(input) if (DramType == DDR5LR) { input}
#elif defined(_BUILD_DDR5LR)
///< Macro for if(DDR5LR) code
#define _IF_DDR5LR(input) input
#else
///< Macro for if(DDR5LR) code
#define _IF_DDR5LR(input)
#endif


#endif
