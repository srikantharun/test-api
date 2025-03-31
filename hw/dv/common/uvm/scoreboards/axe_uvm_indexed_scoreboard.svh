// (C) Copyright Axelera AI 2024
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description:
// UVM Style indexed in order scoreboard
// Multiple sub-scoreboards created and indexed by index()
// For more details - see axe_uvm_scoreboard
// Owner: abond

// Class : axe_uvm_scoreboard
class axe_uvm_indexed_scoreboard #(type EXP_T=uvm_object, type OBS_T=uvm_object, type IDX_T=int) extends axe_uvm_scoreboard #(EXP_T, OBS_T);

    typedef axe_uvm_indexed_scoreboard #(EXP_T, OBS_T, IDX_T) idx_sb_t;
    typedef IDX_T                                             indices_t[];

    sb_t sb[IDX_T];

    `uvm_component_param_utils(idx_sb_t)

    /* Function: new 

       Constructor

       Parameters:

          name - Name of the scoreboard class
          parent - Parent class

       Returns:

          Instance axe_uvm_indexed_scoreboard
    */
    function new (string name, uvm_component parent);
        super.new(name, parent);
    endfunction : new

     /* Function: build_phase
       UVM Build phase

       Parameters:
        phase - UVM built-in
    */   
    function void build_phase(uvm_phase phase);
        indices_t idxs = indices();
        string    idx_name;
        foreach(idxs[i]) begin
            sb[idxs[i]] = sb_t::type_id::create($sformatf("m_sb[%s]", index_name(idxs[i])), this);
        end
    endfunction : build_phase

   /* Function: indices

        Returns array of all possible indices
    
        Returns:

            Array of indices
    */
    virtual function indices_t indices();
        // To be overridden by user specific scoreboard
        return '{0};
    endfunction : indices

    /* Function: index

        Returns the index for a transation
    
        Parameters:

            t - item

        Returns:

            Index
    */
    virtual function IDX_T index(EXP_T t);
        // To be overridden by user specific scoreboard
        return 0;
    endfunction : index

    /* Function: index_name

        Returns the index name for an index as string
        Used to give useful names to sub-scoreboards
    
        Parameters:

            i - index

        Returns:

            Index name
    */
    virtual function string index_name(IDX_T i);
        // To be overridden by user specific scoreboard
        string retVal;
        retVal.itoa(i);
        return retVal;
    endfunction : index_name

    /* Function: write_AXE_SB_EXP

        write callback for expected port
    
        Parameters:

            t - item
    */
    virtual function void write_AXE_SB_EXP (EXP_T t);
        IDX_T idx = index(t);

        if (sb.exists(idx) == 1'b0) begin
            sb[idx] = sb_t::type_id::create("m_sb", this);
        end
        sb[idx].write_AXE_SB_EXP(t);
    endfunction

    /* Function: write_AXE_SB_OBS

        write callback for observed port
    
        Parameters:

            t - item
    */
    virtual function void write_AXE_SB_OBS (EXP_T t);
        IDX_T idx = index(convert(t));

        if (sb.exists(idx) == 1'b0) begin
            sb[idx] = sb_t::type_id::create("m_sb", this);
        end
        sb[idx].write_AXE_SB_OBS(t);
    endfunction 

    /* Function: checkQ

       Check Queue contents and compare if valid
    */
    virtual function void checkQ();
        `uvm_fatal(get_type_name(), "Call of parent checkQ")
    endfunction : checkQ

    /* Function: check_phase
       UVM Check phase

       Parameters:
        phase - UVM built-in
    */
    virtual function void check_phase(uvm_phase phase);
        `uvm_info(get_type_name(), "check_phase", UVM_DEBUG)
    endfunction : check_phase

    /* Function: report_phase
       UVM Report phase

       Parameters:
        phase - UVM built-in
    */
    virtual function void report_phase(uvm_phase phase);
        `uvm_info(get_type_name(), "report_phase", UVM_DEBUG)
    endfunction : report_phase
endclass : axe_uvm_indexed_scoreboard
