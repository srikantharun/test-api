/** \file
 *  \brief function to implement step G of PUB databook initialization step.
 *  \addtogroup CustFunc
 *  @{
 */
#include "dwc_ddrphy_phyinit.h"

#ifndef DWC_DDRPHY_PHYINIT_MAILBOX
/** \brief Implements the mechanism to wait for completion of training firmware
 * execution.
 *
 * The purpose of user this function is to wait for firmware to finish training.
 * The user can either implement a counter to wait or implement the polling
 * mechanism described in the Training Firmware App Note section "Running the
 * Firmware".  The wait time is highly dependent on the training features
 * enabled via SequenceCtrl input to the message block.  See Training Firmware
 * App note for details.
 *
 * The default behavior of this function is to print comments relating to this
 * process.  A function call of the same name will be printed in the output text
 * file.
 *
 * The user can choose to leave this function as is, or implement mechanism to
 * trigger mailbox polling event in simulation.
 *
 * \param phyctx Data structure to hold user-defined parameters
 *
 * \return void
 */
extern void waitFwDone_sv();
void dwc_ddrphy_phyinit_userCustom_G_waitFwDone (phyinit_config_t* phyctx) {
 waitFwDone_sv();


	dwc_ddrphy_phyinit_cmnt(" [%s] Start of %s()\n", __func__, __func__);
	dwc_ddrphy_phyinit_cmnt(" [%s] Wait for the training firmware to complete.\n", __func__);
	dwc_ddrphy_phyinit_cmnt(" [%s] Implement timeout function or follow the procedure in \"3.4 Running the firmware\" of\n", __func__);
	dwc_ddrphy_phyinit_cmnt(" [%s] the Training Firmware Application Note to poll the Mailbox message.\n", __func__);
	dwc_ddrphy_phyinit_print("%s (phyctx);\n\n", __func__);
	dwc_ddrphy_phyinit_cmnt(" [%s] End of %s()\n", __func__, __func__);
}
#else // DWC_DDRPHY_PHYINIT_MAILBOX
void dwc_ddrphy_phyinit_userCustom_majorMailboxMessage(uint16_t message);
void dwc_ddrphy_phyinit_userCustom_streamingMailboxMessage(uint16_t msgType, uint32_t strIndex, uint16_t length, uint32_t* data);
void dwc_ddrphy_phyinit_userCustom_RCDMessage(uint16_t msgType, uint8_t channel, uint8_t dimm, uint8_t rcwId, uint8_t rcwPage, uint8_t rcwValue);

void dwc_ddrphy_phyinit_getMail(uint16_t* mail, uint16_t* data)
{
    if(mail == NULL) {
        return;
    }

    while(dwc_ddrphy_phyinit_userCustom_io_read16(tAPBONLY | csr_UctShadowRegs_ADDR) & 1 != 0){};
    *mail = dwc_ddrphy_phyinit_userCustom_io_read16(tAPBONLY | csr_UctWriteOnlyShadow_ADDR);

    if(data != NULL) {
        *data = dwc_ddrphy_phyinit_userCustom_io_read16(tAPBONLY | csr_UctDatWriteOnlyShadow_ADDR);
    }
    dwc_ddrphy_phyinit_userCustom_io_write16(tAPBONLY | csr_DctWriteProt_ADDR, 0);
    while(dwc_ddrphy_phyinit_userCustom_io_read16(tAPBONLY | csr_UctShadowRegs_ADDR) == 0) {};
    dwc_ddrphy_phyinit_userCustom_io_write16(tAPBONLY | csr_DctWriteProt_ADDR, 1);
}

void dwc_ddrphy_phyinit_getRCDMessage(uint16_t msgType)
{
    uint16_t dataLo = 0;
    uint16_t dataHi = 0;
    dwc_ddrphy_phyinit_getMail(&dataLo, &dataHi);
    uint8_t channel = (dataHi & 0xf000) >> 12;
    uint8_t dimm = (dataHi & 0xf00) >> 8;
    uint8_t rcwId = dataHi & 0xff;
    uint8_t rcwPage = (dataLo & 0xff00) >> 8;
    uint8_t rcwValue = dataLo & 0xff;
    dwc_ddrphy_phyinit_userCustom_RCDMessage(msgType, channel, dimm, rcwId, rcwPage, rcwValue);
}

void dwc_ddrphy_phyinit_getStreamingMessage(uint16_t msgType)
{
    uint16_t length = 0;
    uint16_t data;
    dwc_ddrphy_phyinit_getMail(&length, &data);
    uint32_t strIndex = (data << 16) | (length & 0xffff);
    uint32_t* stream = malloc(length * sizeof(uint32_t));

    for(uint16_t i = 0; i < length; ++i) {
        uint16_t mail;
        dwc_ddrphy_phyinit_getMail(&mail, &data);
        stream[i] = (data << 16) | (mail & 0xffff);
    }
    dwc_ddrphy_phyinit_userCustom_streamingMailboxMessage(msgType, strIndex, length, stream);
    free(stream);
}

void dwc_ddrphy_phyinit_userCustom_G_waitFwDone (phyinit_config_t *phyctx)
{
    // Protocol Init
    dwc_ddrphy_phyinit_userCustom_io_write16(tAPBONLY | csr_DctWriteProt_ADDR, 1);
    dwc_ddrphy_phyinit_userCustom_io_write16(tAPBONLY | csr_UctWriteProt_ADDR, 1);
    uint16_t mail = 0;
    while((mail != 0x07) && (mail != 0xff) && (mail != 0x10) && (mail != 0x11)) {
        dwc_ddrphy_phyinit_getMail(&mail, NULL);
        if(mail == 0x08) {
            dwc_ddrphy_phyinit_getStreamingMessage(mail);
        } else if(mail == 0x50) {
            dwc_ddrphy_phyinit_getRCDMessage(mail);
        } else {
            dwc_ddrphy_phyinit_userCustom_majorMailboxMessage(mail);
        }
    }
}
#endif // DWC_DDRPHY_PHYINIT_MAILBOX

/** @} */

