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

#include <systemc.h>
#include <stdio.h>
#include <sys/types.h>
#include <errno.h>
#include <sys/msg.h>

#include "svdpi.h"
#include "Testbench.h"

void Testbench::UserThread()
{
    printf("Starting user extensible SystemC thread in vPCIe Testbench\n");
}

void Testbench::start_of_simulation()
{
    printf("vPCIe Testbench - Start of Simulation\n");
    fflush(stdout);
}

SC_MODULE_EXPORT(Testbench);

