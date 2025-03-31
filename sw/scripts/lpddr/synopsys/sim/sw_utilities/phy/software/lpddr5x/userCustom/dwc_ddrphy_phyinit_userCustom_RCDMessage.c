// ====================================================================================
// This is user-editable function.  User can edit this function according to their needs.
//
// The purpose of dwc_ddrphy_phyinit_userCustom_RCDMessage() is to handle RCD
// mail box messages
//
// The default behavior of this function is to print commments relating to this process.
//
// User can chooose to leave this function as is, or implement mechanism
// to trigger mailbox poling event in simulation
// ====================================================================================

#include "dwc_ddrphy_phyinit.h"

#ifdef DWC_DDRPHY_PHYINIT_MAILBOX
void dwc_ddrphy_phyinit_userCustom_RCDMessage(uint16_t msgType, uint8_t channel, uint8_t dimm, uint8_t rcwId, uint8_t rcwPage, uint8_t rcwValue)
{
    dwc_ddrphy_phyinit_cmnt("0x%02x %d %d 0x%x 0x%02x 0x%02x\n", msgType, channel, dimm, rcwPage, rcwId, rcwValue);
}
#endif // DWC_DDRPHY_PHYINIT_MAILBOX
