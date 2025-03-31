//------------------------------------------------------------------------------
//                                                                              
//            CADENCE                    Copyright (c) 2013                     
//                                       Cadence Design Systems, Inc.           
//                                       All rights reserved.                   
//                                                                              
//  This work may not be copied, modified, re-published, uploaded, executed, or 
//  distributed in any way, in any medium, whether in whole or in part, without 
//  prior written permission from Cadence Design Systems, Inc.                  
//------------------------------------------------------------------------------
//                                                                              
//   Author                : (username)@cadence.com                              
//                                                                              
//   Date                  : $Date$
//                                                                              
//   Last Changed Revision : $LastChangedRevision$
// 
//------------------------------------------------------------------------------
//   Description                                                                
//                                                                 
//   Base classes definitions.
//   
//   File contents  : package components_pkg 
//                    class   component_cl
//                    class   active_component_cl
//                    class   environment_cl                                    
//------------------------------------------------------------------------------

`timescale 1ns/100ps

`include "sv_macros.svh"

package components_pkg;

  import tb_pkg::*;
  
  //--------------------------------------------------------------------------
  //                      C O M P O N E N T   C L A S S
  //--------------------------------------------------------------------------
  //                            * DEFINITION *
  //--------------------------------------------------------------------------
  // Purpose:
  // + base class for TB components for use with parent/children topology
  //--------------------------------------------------------------------------

  virtual class component_cl;

    int                    debug=0;         // Debugging message level
              string       instance_name;   // This instance name 
    protected component_cl parent;          // Parent handle
    protected component_cl children[$];     // Child handles queue

    extern function              new (string _name, component_cl _parent);
    extern function       string get_name();
    extern function component_cl get_parent();
    extern function       string get_hier_name();
    extern virtual function  bit is_active_component();
    extern         function  bit check_objections();
    extern function       string get_full_hier(int ident);
  endclass : component_cl
  
  //--------------------------------------------------------------------------
  //                      C O M P O N E N T   C L A S S
  //--------------------------------------------------------------------------
  //                           * IMPLEMENTATION *
  //--------------------------------------------------------------------------
  // Purpose:
  // + base class for TB components for use with parent/children topology
  //--------------------------------------------------------------------------

  //__________________________________________________________________________
  // component_cl constructor
  function component_cl::new (string _name, component_cl _parent);
    instance_name   = _name;
    parent = _parent;
    if (parent != null)
      // This is not a top-level component so
      // must add itself to its parent's list of children.
      parent.children.push_back(this);

    assert (_name!="") else $warning($psprintf("> created instance with empty name under %s",
      (parent != null) ? parent.get_hier_name() : "null"));
    if (debug)  $display("> constructed %s", get_hier_name());
  endfunction : new
  
  //__________________________________________________________________________
  // get instance name without hierarchy
  function string component_cl::get_name();
    return instance_name;
  endfunction : get_name

  //__________________________________________________________________________
  // get instance name with hierarchy
  function string component_cl::get_hier_name();
    if (parent == null)
      return instance_name;
    else
      return {parent.get_hier_name(), ".", instance_name};
  endfunction : get_hier_name

  //__________________________________________________________________________
  // get parent handle
  function component_cl component_cl::get_parent();
    return parent;
  endfunction : get_parent

  //__________________________________________________________________________
  // says whether this component implements phases
  function bit component_cl::is_active_component();
    return 1'b0;
  endfunction : is_active_component

  //__________________________________________________________________________
  // report no obejctions from passive components
  function bit component_cl::check_objections();
    return 1'b0;
  endfunction : check_objections

  //__________________________________________________________________________
  // prints (recursively) a multi-line description of hierarchy of components
  function string component_cl::get_full_hier(int ident);
    string tmp = "", x;
    if (ident == 0)
      $swrite(tmp, "%s's subcomponents:\n", get_name());
    else begin
      for (int i = 0; i < ident; ++i)
        $swrite(tmp, "%s ", tmp);
      $swrite(tmp, "%s%s (%s)\n", tmp, get_name(),
        is_active_component() ? "A" : "I");
    end
    foreach (children[i]) begin
      x = children[i].get_full_hier(ident+3);
      $swrite(tmp, "%s%s", tmp, x);
    end
    return tmp;
  endfunction : get_full_hier

  //--------------------------------------------------------------------------
  //                 A C T I V E   C O M P O N E N T   C L A S S
  //--------------------------------------------------------------------------
  //                            * DEFINITION *
  //--------------------------------------------------------------------------
  // Purpose:
  // + base class for TB components with defined simulation phases
  //--------------------------------------------------------------------------

  virtual class active_component_cl extends component_cl;
   
    extern         function           new (string _name, component_cl _parent);
    extern virtual function       bit is_active_component();
    extern virtual function      void build();
    `PURE  virtual protected function   void make();             `ENDPUREFUNCTION
    extern virtual function      void connect();
    `PURE  virtual protected function   void link_up();          `ENDPUREFUNCTION
    extern         task               launch();
    `PURE  virtual protected task     run(); `ENDPURETASK
    extern virtual task                      log_hierarchy();
    extern virtual function      void wrap_up();

    `PURE  virtual function           string get_class_name();   `ENDPUREFUNCTION
    extern         function      stringqueue hierarchy(stringqueue _hierarchy_tree);
    
    bit                                      obj_active;
    event                                    obj_change;
    bit                                      obj_list[$];
    
    extern function                      int new_objection();
    extern function                     void raise_objection(int obj_no);
    extern function                     void drop_objection (int obj_no);
    extern function                      bit check_objections();

  
  
  endclass : active_component_cl
  
  //--------------------------------------------------------------------------
  //                 A C T I V E   C O M P O N E N T   C L A S S
  //--------------------------------------------------------------------------
  //                           * IMPLEMENTATION *
  //--------------------------------------------------------------------------
  // Purpose:
  // + base class for TB components with defined simulation phases
  //--------------------------------------------------------------------------

  //__________________________________________________________________________
  // active_component_cl constructor
  function active_component_cl::new (string _name, component_cl _parent);
    super.new(_name, _parent);
    if (parent != null) begin
      assert (parent.is_active_component)
      else $fatal(1,"Active component %s cannot be a child of a passive component",
        this.get_hier_name);
    end
    obj_active = `FALSE;
  endfunction : new

  //__________________________________________________________________________
  // says whether this component implements phases
  function bit active_component_cl::is_active_component();
    return 1'b1;
  endfunction : is_active_component

  //__________________________________________________________________________
  // build phase implementation
  function void active_component_cl::build;
    int result;
    active_component_cl act_comp;
    // instantiate children
    this.make();  
    // call build -> make to all childrens
    foreach (children[i])
      if (children[i].is_active_component) begin
        result=$cast(act_comp, children[i]);
        assert(result) else $fatal(1,"non-active component pretends to be active");
        act_comp.build;
      end
  endfunction : build

  //__________________________________________________________________________
  // connect phase implementation
  function void active_component_cl::connect;
    active_component_cl act_comp;
    int result;
    // make connection to childrens
      this.link_up();
    // call connect->link_up to all childrens
    foreach (children[i])
      if (children[i].is_active_component) begin
        result = $cast(act_comp, children[i]);
        assert (result) else $fatal(1,"non-active component pretends to be active");
        act_comp.connect;
      end
  endfunction : connect

  //__________________________________________________________________________
  // run phase initiation (run phase to be implemented in the run method)
  task active_component_cl::launch;
    active_component_cl act_comp;
    int result;
    if (parent == null) begin
      this.build;
      this.connect;
      this.log_hierarchy;
    end

    for (int i = 0; i < children.size; ++i)
      if (children[i].is_active_component) begin
        result = $cast(act_comp, children[i]);
        assert (result) else $fatal(1, "non-active component pretends to be active");
        act_comp.launch;
      end
      
    fork
      this.run;
    join_none

    #1;
  endtask : launch

  //__________________________________________________________________________
  // log build hierarchy
  task active_component_cl::log_hierarchy; endtask

  //__________________________________________________________________________
  // wrap_up phase implementation
  function void active_component_cl::wrap_up;
    active_component_cl act_comp;
    int result;
    foreach (children[i])
      if (children[i].is_active_component) begin
        result = $cast(act_comp, children[i]);
        assert (result) else $fatal(1, "non-active component pretends to be active");
        act_comp.wrap_up;
      end
  endfunction : wrap_up

  //__________________________________________________________________________
  // report
  function stringqueue active_component_cl::hierarchy(stringqueue _hierarchy_tree);
    active_component_cl act_comp;
    stringqueue hierarchy_tree = _hierarchy_tree;
    int result;
    // append children names
    foreach (children[i])
      if (children[i].is_active_component) begin
        result = $cast(act_comp, children[i]);
        assert (result) else $fatal(1, "non-active component pretends to be active"); 
        hierarchy_tree = act_comp.hierarchy(hierarchy_tree);
      end else
        hierarchy_tree.push_front($psprintf("%s (passive/%s)",act_comp.get_hier_name,this.get_class_name));
    
    // and finaly append my name
    hierarchy_tree.push_front($psprintf("%s (active/%s)",this.get_hier_name,this.get_class_name));
    
    return  hierarchy_tree;     
  endfunction
  
  //__________________________________________________________________________
  // create new objection and instert to the objections queue
  // + returns new objection nuber
  function int active_component_cl::new_objection();
    int objection_number;
    obj_list.push_back(`FALSE);
    return obj_list.size()-1;     
  endfunction
  
  //__________________________________________________________________________
  // raise selected objection 
  function  void active_component_cl::raise_objection(int obj_no);
    assert(obj_list[obj_no]==`FALSE) else $warning("Raisng already active objection @%s",get_hier_name());
    obj_list[obj_no]=`TRUE;
    ->obj_change;
  endfunction
  
  //__________________________________________________________________________
  // raise selected objection 
  function  void active_component_cl::drop_objection (int obj_no);
     assert(obj_list[obj_no]==`TRUE) else $warning("Dropping non active objection @%s",get_hier_name());
     obj_list[obj_no]=`FALSE;
    ->obj_change;
  endfunction    

  //__________________________________________________________________________
  // check and return `TRUE if any objection raised
  function bit active_component_cl::check_objections();
    active_component_cl active;
    int result;
    if (debug) $display ("checking objections @%s",get_hier_name());
    // check own objections 
    foreach (obj_list[i]) 
      if (obj_list[i]==`TRUE) return `TRUE;
    // check children objections
    foreach (children[i]) begin
      if (children[i].is_active_component) begin
        result = $cast(active, children[i]);
        assert (result) else $fatal(1, "non-active component pretends to be active"); 
        if (active.check_objections) return `TRUE;
        end
      end
    // no raised objections detected
    return `FALSE;
  endfunction

  //==========================================================================
  //--------------------------------------------------------------------------
  //        E N V I R O N M E N T    C O M P O N E N T     C L A S S
  //--------------------------------------------------------------------------
  //                           * IMPLEMENTATION *
  //--------------------------------------------------------------------------
  // Purpose:
  // + base class for TB components with defined simulation phases
  //--------------------------------------------------------------------------

  virtual class environment_cl extends active_component_cl;
  
    //__________________________________________________________________________
    // environment_cl constructor
    function new(string _name = "test_env");
      super.new(_name, null);
    endfunction
  endclass : environment_cl

  //==========================================================================

endpackage : components_pkg

