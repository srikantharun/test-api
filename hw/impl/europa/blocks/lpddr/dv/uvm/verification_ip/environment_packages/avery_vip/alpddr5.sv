/*
 * |-----------------------------------------------------------------------|
 * |                                                                       |
 * |   Copyright Avery Design Systems, Inc. 2015.                          |
 * |     All Rights Reserved.       Licensed Software.                     |
 * |                                                                       |
 * |                                                                       |
 * | THIS IS UNPUBLISHED PROPRIETARY SOURCE CODE OF AVERY DESIGN SYSTEMS   |
 * | The copyright notice above does not evidence any actual or intended   |
 * | publication of such source code.                                      |
 * |                                                                       |
 * |-----------------------------------------------------------------------|
 */
/***************************************************************************
*
*         Name:  alpddr5.sv, includes LPDDR5 Sub-channel A and B
*
***************************************************************************/

`timescale 1ps / 1ps
import amem_pkg::*;
`include "avery_defines.svh"

// Table 1 - Pad Definition, p6
module alpddr5 (
    reset_n, 
    zq,
    ck0_t, ck0_c, 
    ck1_t, ck1_c, 
    dmi,// TODO -re-check seperate for diff channel 

    // Sub-channel A
    // input
    cs_A,
    ca_A,
    wck_t_A, 
    wck_c_A, 
    // inout
    dq_A,
    rdqs_t_A, 
    rdqs_c_A,

    // Channel B
    // input
    cs_B,
    ca_B,
    wck_t_B, 
    wck_c_B, 
    // inout
    dq_B,
    rdqs_t_B, 
    rdqs_c_B
);

    // used if TRACK_ON= 1, combine the monitor files of channelA and channelB
    parameter SINGLE_TRACK_FILE= 0;
    // set 1 to generate performance report
    parameter PERFORMANCE_ON= 0;
    `include "alpddr5_module_parameter.svh"

    // ports
    input    reset_n;
    input    zq;
    input    ck0_t;  
    input    ck0_c; 
    input    ck1_t;  
    input    ck1_c; 
    input    dmi;  

    input    cs_A;
    input    cs_B;
    input [AMEM_CA_BITS-1:0]  ca_A, ca_B;
    input [M_WCK_BITS-1:0]    wck_t_A, wck_t_B; 
    input [M_WCK_BITS-1:0]    wck_c_A, wck_c_B; 
    inout [AMEM_DQ_BITS-1:0]  dq_A, dq_B;
    inout [AMEM_DQS_BITS-1:0] rdqs_t_A, rdqs_t_B; // DQS_t
    inout [AMEM_DQS_BITS-1:0] rdqs_c_A, rdqs_c_B; // DQS_c

    amem_log log;

    // backward compatible declarations
    amem_sparse avy_sparse; 
    amem_sparse avy_sparseB; 
    addr_monitor mon_tracker;
    addr_monitor mon_trackerB;
    alpddr5_timing ddr_timing;
    alpddr5_modereg ddr_modereg;
    alpddr5_modereg ddr_moderegB;
    bit bfm_started = 0;
    bit data_structure_ready= 0;
    bit user_start_bfm= 1;
    //event dq_out_event;

    string module_name= MODULE_NAME;
    // if 1, no output from the memory, check read's data
    bit monitor_only= PASSIVE_MODE;  

    alpddr5_channel #(.MODULE_NAME(MODULE_NAME),
                      .CHANNEL_NO(1),
                      .ADDR_SPEED(ADDR_SPEED),
                      .ADDR_DENSITY(ADDR_DENSITY),
                      .ADDR_TYPE(ADDR_TYPE),
                      .ADDR_IO_WIDTH(ADDR_IO_WIDTH),
                      .TRACK_ON(TRACK_ON),
                      .PASSIVE_MODE(PASSIVE_MODE),
                      .SKIP_POR(SKIP_POR),
                      .SKIP_INIT(SKIP_INIT),
                      .POST_FIX("sub_chnA"),
                      .USER_SETUP_TIME(USER_SETUP_TIME),
                      .UVM_CFGDB_SET(UVM_CFGDB_SET)) sub_channel_A(
        .reset_n(reset_n),
	.dmi(dmi),
        .zq     (zq),
        .ck_t   (ck0_t), 
        .ck_c   (ck0_c),
        .cs     (cs_A),
        .ca     (ca_A),
        .dq     (dq_A),
        .rdqs_t (rdqs_t_A), 
        .rdqs_c (rdqs_c_A),
        .wck_t  (wck_t_A), 
        .wck_c  (wck_c_A)
        );

    alpddr5_channel #(.MODULE_NAME(MODULE_NAME),
                      .CHANNEL_NO(0),
                      .ADDR_SPEED(ADDR_SPEED),
                      .ADDR_DENSITY(ADDR_DENSITY),
                      .ADDR_TYPE(ADDR_TYPE),
                      .ADDR_IO_WIDTH(ADDR_IO_WIDTH),
                      .TRACK_ON(TRACK_ON),
                      .PASSIVE_MODE(PASSIVE_MODE),
                      .SKIP_POR(SKIP_POR),
                      .SKIP_INIT(SKIP_INIT),
                      .POST_FIX("sub_chnB"),
                      .USER_SETUP_TIME(USER_SETUP_TIME),
                      .UVM_CFGDB_SET(UVM_CFGDB_SET)) sub_channel_B(
        .reset_n(reset_n),
	.dmi(dmi),
        .zq     (zq),
        .ck_t   (ck1_t), 
        .ck_c   (ck1_c),
        .cs     (cs_B),
        .ca     (ca_B),
        .dq     (dq_B),
        .rdqs_t (rdqs_t_B), 
        .rdqs_c (rdqs_c_B),
        .wck_t  (wck_t_B), 
        .wck_c  (wck_c_B)
        );
    
    initial begin
        if (module_name == "") 
            module_name= "alpddr5";

        if (log == null)
            log= new(module_name);

        mon_tracker  = new ("mon_tracker",null);//, ddr_if, dfi_timing, ddr_timing);
        mon_trackerB = new ("mon_trackerB",null);//, ddr_if, dfi_timing, ddr_timing);
        // Let this module control alpddr5 sub-channels' structure
        sub_channel_A.set("start_bfm", 0);
        sub_channel_B.set("start_bfm", 0);
        sub_channel_A.wait_event("data_structure_ready", 100us);
        sub_channel_B.wait_event("data_structure_ready", 100us);
        data_structure_ready= 1;
        #USER_SETUP_TIME; // arbitrarily wait for log, sparse, timing, modereg, and monitor to be assigned
        wait_event("user_start_bfm", 100us, $sformatf("Still wait for user start bfm using %m.set(\"start_bfm\",1)"), 0);

        if (user_start_bfm) begin
            // setup sub-channel A by using user assigment (backward compatible)
            if (avy_sparse != null)
                set_avy_sparse(avy_sparse);
            if (mon_tracker == null && avy_sparse != null && avy_sparse.mon_tracker != null)
                set_monitor(avy_sparse.mon_tracker);
            if (mon_tracker != null)
                set_monitor(mon_tracker);
            if (ddr_timing != null)
                set_timing(ddr_timing);
            if (monitor_only)
                sub_channel_A.monitor_only= 1;
            if (ddr_modereg != null)
                set_modereg(ddr_modereg);

            // setup sub-channel B by using user assigment (backward compatible)
            if (avy_sparseB != null)
                set_avy_sparse(avy_sparseB, 1);
            if (mon_trackerB == null && avy_sparseB != null && avy_sparseB.mon_tracker != null)
                set_monitor(avy_sparseB.mon_tracker, 1);
            if (mon_trackerB != null)
                set_monitor(mon_trackerB, 1);
            if (ddr_timing != null)
                set_timing(ddr_timing, 1);
            if (monitor_only)
                sub_channel_B.monitor_only= 1;
            if (ddr_moderegB != null)
                set_modereg(ddr_moderegB, 1);

            if (TRACK_ON && SINGLE_TRACK_FILE) config_shadow_monitor(module_name, sub_channel_A.get_monitor(), sub_channel_B.get_monitor());
            sub_channel_A.set("start_bfm", 1);
            sub_channel_B.set("start_bfm", 1);
            sub_channel_A.wait_event("bfm_started", 100us);
            sub_channel_B.wait_event("bfm_started", 100us);
            bfm_started= 1;
        end
    end

    /* USER API - get_log */
    /* Function: get_log
                 get amem_log from sub-channel A or sub-channel B
       
       is_channel_b - 0 for sub-channel A, 1 for sub-channel B
    */
    function amem_log get_log(input bit is_channel_b= 0);
        amem_log m;
        m= is_channel_b ? sub_channel_B.get_log(): sub_channel_A.get_log();
        return m;
    endfunction

    /* USER API - get_monitor */
    /* Function: get_monitor
                 get addr_monitor from sub-channel A or sub-channel B
       
       is_channel_b - 0 for sub-channel A, 1 for sub-channel B
    */
    function addr_monitor get_monitor(input bit is_channel_b= 0);
        addr_monitor m;
        m= is_channel_b ? sub_channel_B.get_monitor(): sub_channel_A.get_monitor();
        return m;
    endfunction

    /* USER API - get_avy_sparse */
    /* Function: get_avy_sparse
                 get amem_sparse from sub-channel A or sub-channel B
       
       is_channel_b - 0 for sub-channel A, 1 for sub-channel B
    */
    function amem_sparse get_avy_sparse(input bit is_channel_b= 0);
        amem_sparse  m;
        m= is_channel_b ? sub_channel_B.get_avy_sparse(): sub_channel_A.get_avy_sparse();
        return m;
    endfunction

    /* USER API - get_ddr_status */
    /* Function: get_ddr_status
                 get addr3_status from sub-channel A or sub-channel B
       
       is_channel_b - 0 for sub-channel A, 1 for sub-channel B
    */
    function addr3_status get_ddr_status(input bit is_channel_b= 0);
        addr3_status m;
        m= is_channel_b ? sub_channel_B.get_ddr_status(): sub_channel_A.get_ddr_status();
        return m;
    endfunction

    /* USER API - get_timing */
    /* Function: get_timing
                 get alpddr5_timing from sub-channel A or sub-channel B
       
       is_channel_b - 0 for sub_channel A, 1 for sub_channel B
    */
    function alpddr5_timing get_timing(input bit is_channel_b= 0);
        alpddr5_timing m;
        DDR_TIMING d2;

        d2= is_channel_b ? sub_channel_B.get_timing(): sub_channel_A.get_timing();
        if (!$cast(m, d2))
            log.error($sformatf("%m got alpddr5_timing casting failure from type %0s in get_timing(), ignored", d2.device_type.name()));
        return m;
    endfunction

    /* USER API - get_modereg */
    /* Function: get_modereg
                 get DDR_MODEREG from sub-channel A or sub-channel B
       
       is_channel_b - 0 for sub-channel A, 1 for sub-channel B
    */
    function DDR_MODEREG get_modereg(input bit is_channel_b= 0);
        DDR_MODEREG m;
        m= is_channel_b ? sub_channel_B.get_modereg(): sub_channel_A.get_modereg();
        return m;
    endfunction

    /* USER API - set_log */
    /* Function: set_log
                 set amem_log to sub-channel A or sub-channel B
       
       m - target amem_log
       is_channel_b - 0 for sub-channel A, 1 for sub-channel B
    */
    function void set_log(
        input amem_log m, 
        input bit is_channel_b= 0);

        if (is_channel_b) 
            sub_channel_B.set_log(m);
        else sub_channel_A.set_log(m);
    endfunction

    /* USER API - set_monitor */
    /* Function: set_monitor
                 set addr_monitor to sub-channel A or sub-channel B
       
       m - target addr_monitor
       is_channel_b - 0 for sub-channel A, 1 for sub-channel B
    */
    function void set_monitor(
        input addr_monitor_base m, 
        input bit is_channel_b= 0);

        if (is_channel_b)
            sub_channel_B.set_monitor(m);
        else sub_channel_A.set_monitor(m);
    endfunction

    /* USER API - set_avy_sparse */
    /* Function: set_avy_sparse
                 set amem_sparse to sub-channel A or sub-channel B
       
       m - target amem_sparse
       is_channel_b - 0 for sub_channel A, 1 for sub_channel B
    */
    function void set_avy_sparse(
        input amem_sparse m, 
        input bit is_channel_b= 0);

        if (is_channel_b)
            sub_channel_B.set_avy_sparse(m);
        else sub_channel_A.set_avy_sparse(m);
    endfunction

    /* USER API - set_ddr_status */
    /* Function: set_ddr_status
                 set addr3_status to sub-channel A or sub-channel B
       
       m - target addr3_status
       is_channel_b - 0 for sub-channel A, 1 for sub-channel B
    */
    function void set_ddr_status(
        input addr3_status m, 
        input bit is_channel_b= 0);

        if (is_channel_b)
            sub_channel_B.set_ddr_status(m);
        else sub_channel_A.set_ddr_status(m);
    endfunction

    /* USER API - set_timing */
    /* Function: set_timing
                 set alpddr5_timing to sub-channel A or sub-channel B
       
       m - target alpddr5_timing
       is_channel_b - 0 for sub-channel A, 1 for sub-channel B
    */
    function void set_timing(
        input DDR_TIMING m, 
        // 0: sub-channel A, 1: sub-channel B, 2: both channels
        input int is_channel_b= 0);

        if (is_channel_b inside {1, 2})
            sub_channel_B.set_timing(m);
        if (is_channel_b inside {0, 2})
            sub_channel_A.set_timing(m);
    endfunction

    /* USER API - set_modereg */
    /* Function: set_modereg
                 set modereg to sub-channel A or sub-channel B
       
       m - target alpddr5_modereg
       is_channel_b - 0 for sub-channel A, 1 for sub-channel B
    */
    function void set_modereg(
        input alpddr5_modereg m, 
        input bit is_channel_b= 0);

        if (is_channel_b)
            sub_channel_B.set_modereg(m);
        else sub_channel_A.set_modereg(m);
    endfunction

    /* USER API - set_severity */
    /* Function: set_severity
                 set severity for sub-channel A or sub-channel B
       
       id - check item ID
       v - severity
       is_channel_b - 0 for sub-channel A, 1 for sub-channel B, 2: both channels
    */
    function void set_severity(
        input string id, 
        input amem_severity v, 
        input int is_channel_b= 2);

        if (is_channel_b inside {1, 2})
            sub_channel_B.set_severity(id, v);
        if (is_channel_b inside {0, 2})
            sub_channel_A.set_severity(id, v);
    endfunction

    /* USER API - set_module_name */
    /* Function: set_module_name
                 set module name to sub-channel A or sub-channel B
       
       m - target alpddr5_modereg
       is_channel_b - 0 for sub-channel A, 1 for sub-channel B
    */
    function void set_module_name(
        input string m,
        input int is_channel_b= 0);

        if (is_channel_b)
            sub_channel_B.set_module_name(m);
        else sub_channel_A.set_module_name(m);
    endfunction

    // DO NOT call this if not using Avery's memory controller and PHY.
    // Backdoor sync up with Avery's controller and PHY. Pass null pointer for phy or mc if not available.
    task bkdoor_sync_up(adfi_mc_class mc, adfi_phy_class phy, addr_monitor mon= null, bit is_channel_b= 0);
        if (is_channel_b)
            sub_channel_B.bkdoor_sync_up(mc, phy, mon, 1);
        else sub_channel_A.bkdoor_sync_up(mc, phy, mon);
    endtask
    
    function void config_shadow_monitor(
        input string name2,
        input addr_monitor mon_main2,
        input addr_monitor mon_shadow2);
        string tracker_name2;
        string dtracker_name2;

        tracker_name2= $sformatf("%0s_monh.txt", name2); 
        dtracker_name2= $sformatf("%0s_mon.txt", name2);

        mon_main2.tracker_name= tracker_name2;
        mon_main2.dtracker_name= dtracker_name2;
         
        mon_shadow2.set("total_cs", mon_main2.total_cs);
        mon_shadow2.set("num_slice_per_cs", mon_main2.num_of_slice);
        mon_shadow2.tracker_name= mon_main2.tracker_name;
        mon_shadow2.dtracker_name= mon_main2.dtracker_name;
        mon_shadow2.channel_number= mon_main2.channel_number;
        mon_shadow2.tracker_shared= 1;
        mon_shadow2.shared_monitor= mon_main2;

        if (log.dbg_flag[AMEM_DBG_monitor])
            log.debug($sformatf("%0s configs %0s to be main monitor and %0s to be shadow monitor", 
                      name2, mon_main2.monit_name, mon_shadow2.monit_name));
    endfunction

    task automatic wait_event( string entry           ,
                     time   timer            = 0,
                     string timeout_msg      = "",
                     bit    fatal_on_timeout = 1,
                     // 0: sub-channel A, 1: sub-channel B, 2: both channels
                     int    is_channel_b     = 2);
        fork begin
            if (log.dbg_flag[AMEM_DBG_api])
                log.dbg_api($sformatf("%m.wait_event(\"%0s\", %0dns, \"%0s\")", entry, timer/1ns, timeout_msg));
            if (timer > 0) fork
                if (fatal_on_timeout)
                    #(timer) log.fatal($sformatf("%m.wait_event(%s, %0t, ...): timer expired (%s)", entry, timer, timeout_msg));
                else repeat (10) begin
                    #(timer) log.debug($sformatf("%m.wait_event(%s, %0t, ...): still waiting (%s)", entry, timer, timeout_msg));
                end
            join_none
            if (bfm_started == 0 && !(entry inside {"bfm_started", "data_structure_ready", "user_start_bfm"}) ) begin
                log.usage("BFM is not started yet: call wait_event(\"bfm_started\") first", 1);
            end
   
            case (entry)
                // wait until this BFM is started. Before it's started, none of the
                // state machines is active.
                "user_start_bfm": wait (user_start_bfm);
                "bfm_started": wait (bfm_started);
                "data_structure_ready": wait (data_structure_ready);
                default: begin
                    log.usage($sformatf("\"%s\" is not a valid entry for %m.wait_event()", entry));
                    $finish;
                end
            endcase
    
            if (timer > 0)
                disable fork;
        end join
    endtask

    function void set(input string  entry,                                                                                                                                                               
                    input bit[63:0] value = 0,
                    input string    sub_entry = "");
        if (log != null && log.dbg_flag[AMEM_DBG_api])
            if (entry == "watchdog_timeout")
                log.dbg_api($sformatf("%m(\"%0s\", %0d us, \"%0s\")", entry, value/1us, sub_entry));
            else if (sub_entry != "")
                log.dbg_api($sformatf("%m(\"%0s\", %0h, \"%s\")", entry, value, sub_entry));
            else
                log.dbg_api($sformatf("%m(\"%0s\", %0h)", entry, value));
        case (entry)
            "start_bfm": begin
                user_start_bfm = value > 0;
            end
            default: begin
                log.usage($sformatf("\"%s\" is not a valid entry for %m()", entry), 1);
            end
        endcase
    endfunction

endmodule

`include "alpddr5_channel.sv"
