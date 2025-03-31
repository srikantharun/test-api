// (C) Copyright Axelera AI 2024
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description:
// UVM Style in order scoreboard
// 2 analysis ports - expected and observed
// Comparision occurs when there is valid data on each side of the board
// Additional features:
//  - All comparisions are on the expected data type using built-in compare() function
//  - User defined convert function to allow comparison to/from different data types
//  - Check phase checks:
//      - Number of comparision > minimum comparision count (default=1)
//      - Scoreboard is empty (no outstanding items on either side)
// Owner: abond

`uvm_analysis_imp_decl (_AXE_SB_EXP)
`uvm_analysis_imp_decl (_AXE_SB_OBS)

// Class : axe_uvm_scoreboard
class axe_uvm_scoreboard #(type EXP_T=uvm_object, type OBS_T=uvm_object) extends uvm_scoreboard;

    typedef axe_uvm_scoreboard #(EXP_T, OBS_T) sb_t;

    uvm_analysis_imp_AXE_SB_EXP #(EXP_T, sb_t) analysis_imp_exp;
    uvm_analysis_imp_AXE_SB_OBS #(OBS_T, sb_t) analysis_imp_obs; 
    EXP_T                                           expQ[$];
    EXP_T                                           obsQ[$];
    int                                             error_max  = 1;
    int                                             error_cnt  = 0;
    int                                             comp_min   = 1;
    int                                             comp_cnt   = 0;

    `uvm_component_param_utils_begin(sb_t)
        `uvm_field_int(error_max, UVM_DEFAULT)
        `uvm_field_int(error_cnt, UVM_DEFAULT)
        `uvm_field_int(comp_min,  UVM_DEFAULT)
        `uvm_field_int(comp_cnt,  UVM_DEFAULT)
    `uvm_component_utils_end

    /* Function: new 

       Constructor

       Parameters:

          name - Name of the scoreboard class
          parent - Parent class

       Returns:

          Instance axe_uvm_scoreboard
    */
    function new (string name, uvm_component parent);
        super.new(name, parent);
        analysis_imp_exp = new("analysis_port_exp", this);
        analysis_imp_obs = new("analysis_port_obs", this);
    endfunction : new

    /* Function: convert 

       Convert observed object into data type of expected object

       Parameters:

          t - Observed object

       Returns:

          Instance of expected object class
    */
    virtual function EXP_T convert (OBS_T t);
        // Default to NULL operation
        return t;
    endfunction : convert

    /* Function: write_AXE_SB_EXP

        write callback for expected port
    
        Parameters:

            t - item
    */
    virtual function void write_AXE_SB_EXP (EXP_T t);
        expQ.push_back(t);
        checkQ();
    endfunction

    /* Function: write_AXE_SB_OBS

        write callback for observed port
    
        Parameters:

            t - item
    */
    virtual function void write_AXE_SB_OBS (EXP_T t);
        obsQ.push_back(convert(t));
        checkQ();
    endfunction 

    /* Function: checkQ

       Check Queue contents and compare if valid
    */
    virtual function void checkQ();
        while ((expQ.size() > 0) && (obsQ.size() > 0)) begin
            EXP_T exp = expQ.pop_front();
            EXP_T obs = obsQ.pop_front();

            if (exp.compare(obs)) begin
                `uvm_info(get_full_name(), $sformatf("Compare successfull\n%s\n", exp.sprint()), UVM_DEBUG)
            end else begin
                `uvm_error(get_full_name(), $sformatf("Compare failed. Expected:\n%s\n Observed:\n%s\n", exp.sprint(), obs.sprint()))
                error_cnt += 1;
            end
            comp_cnt += 1;

            if (error_cnt >= error_max) begin
                `uvm_fatal(get_full_name(), "Max Error Count Reached")
            end
        end
    endfunction : checkQ

    /* Function: check_phase
       UVM Check phase

       Parameters:
        phase - UVM built-in
    */
    virtual function void check_phase(uvm_phase phase);
        if (comp_cnt < comp_min) begin
            `uvm_error(get_full_name(), "Minimum comparison threshold not met")
        end

        if (expQ.size() != 0) begin
            `uvm_error(get_full_name(), $sformatf("%0d Outstanding Expected Items\n%s\n", expQ.size(),expQ[0].sprint()))
        end

        if (obsQ.size() != 0) begin
            `uvm_error(get_full_name(), $sformatf("%0d Outstanding Observed Items\n%s\n", obsQ.size(), obsQ[0].sprint()))
        end      
    endfunction : check_phase

    /* Function: report_phase
       UVM Report phase

       Parameters:
        phase - UVM built-in
    */
    virtual function void report_phase(uvm_phase phase);
        `uvm_info(get_full_name(), $sformatf("Compared %0d items", comp_cnt), UVM_NONE)
    endfunction : report_phase
endclass : axe_uvm_scoreboard
