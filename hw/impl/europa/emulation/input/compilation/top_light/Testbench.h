/***********************************************************************
 *                                                                     *
 *                  Unpublished work. © Siemens 2021                   *
 *                                                                     *
 *     THIS MATERIAL CONTAINS TRADE SECRETS OR OTHERWISE CONFIDENTIAL  *
 *  INFORMATION OWNED BY SIEMENS INDUSTRY SOFTWARE INC. OR ITS         *
 *  AFFILIATES (COLLECTIVELY, "SSIW"), OR ITS LICENSORS. ACCESS TO AND *
 *  USE OF THIS INFORMATION IS STRICTLY LIMITED AS SET FORTH IN THE    *
 *  CUSTOMER'S APPLICABLE AGREEMENTS WITH SSIW.                        *
 *                                                                     *
 ***********************************************************************
 * $Rev::     $:
 * Author::    :
 * $Date::  1#$:
 ******************************************************************/

#ifndef TESTBENCH_H
#define TESTBENCH_H
#include <systemc.h>
#include <stdio.h>
#include <sys/types.h>
#include <errno.h>
#include <sys/msg.h>
#include "svdpi.h"
#include "vpcie_rootport_sc.h"

class Testbench : public sc_module
{
    private:

        void UserThread();             // Sample SystemC Tester Thread.

        SC_HAS_PROCESS(Testbench);

        vpcie_rootport_sc  *mpvPCIeRp; // VirtualPCIe Top.

    public:

        Testbench(sc_module_name name) : sc_module(name)
        {
            // Construct the vPCIe Top, Providing the HDL Path for the
            // Root Port Transactor.
            mpvPCIeRp = new vpcie_rootport_sc("RootPort", "hdl_top.i_europa.u_aipu.u_pcie_p.u_pcie_subsys.vpcie_rp_pipe441");

            SC_THREAD(UserThread);
        }

        void start_of_simulation();
};

#endif  // TESTBENCH_H

