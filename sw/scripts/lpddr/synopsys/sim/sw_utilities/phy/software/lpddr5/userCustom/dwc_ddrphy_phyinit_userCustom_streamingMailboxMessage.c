// ====================================================================================
// This is user-editable function.  User can edit this function according to their needs.
//
// The purpose of dwc_ddrphy_phyinit_userCustom_streamingMailboxMessage() is to handle
// streaming mail box messages
//
// The default behavior of this function is to print commments relating to this process.
//
// User can chooose to leave this function as is, or implement mechanism
// to trigger mailbox poling event in simulation
// ====================================================================================

#include "dwc_ddrphy_phyinit.h"

#ifdef DWC_DDRPHY_PHYINIT_MAILBOX
void dwc_ddrphy_phyinit_userCustom_streamingMailboxMessage(uint16_t msgType, uint32_t strIndex, uint16_t length, uint32_t* data)
{
    dwc_ddrphy_phyinit_cmnt("0x%02x 0x%08x", msgType, strIndex);
    for(uint16_t i = 0; i < length; ++i) {
        dwc_ddrphy_phyinit_cmnt(" 0x%08x", data[i]);
    }
    dwc_ddrphy_phyinit_cmnt("\n");
}
#endif // DWC_DDRPHY_PHYINIT_MAILBOX
