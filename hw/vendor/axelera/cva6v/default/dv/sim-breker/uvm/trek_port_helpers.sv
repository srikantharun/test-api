// COPYRIGHT (c) Breker Verification Systems
// This software has been provided pursuant to a License Agreement
// containing restrictions on its use.  This software contains
// valuable trade secrets and proprietary information of
// Breker Verification Systems and is protected by law.  It may
// not be copied or distributed in any form or medium, disclosed
// to third parties, reverse engineered or used in any manner not
// provided for in said License Agreement except with the prior
// written authorization from Breker Verification Systems.
//
`ifndef GUARD__TREK_PORT_HELPERS__SV
`define GUARD__TREK_PORT_HELPERS__SV

/// This file is just included in trek_uvm_pkg, separated out here
/// to maintain focus in that more important file.
///
/// It defines some methods used in Trek's TLM UVM infrastructure.


function void port_built(input string tb_path);
  if (portInfo.exists(tb_path)) begin: ok
    portInfo[tb_path].built += 1;
  end
endfunction: port_built


function void audit_port_info(input string name,
    input string port_type, input string primary_type,
    input string secondary_type);

  string prefix;

  // *IF* we make ports extend from uvm_object, and *IF* we also
  // use the `uvm_object_begin() macro, then it will construct a
  // "default object" for use by the factory. That object will
  // have an empty name field, so we need this escape to ignore
  // construction of such a "default object".
  if (name.len() == 0)
    return;

  $sformat(prefix, "tb_path='%s': ", name);

  if (portInfo.exists(name) == 0) begin: tbpath
    `uvm_warning("trek_uvm_pkg::audit_port_info()",
      {prefix, "is not a known port instance"})
  end else begin: checks
    if (portInfo[name].built > 1) begin: built
      `uvm_info("trek_uvm_pkg::audit_port_info()",
        $sformatf("%s has been built %0d times",
                  prefix, portInfo[name].built), UVM_HIGH)
    end
    if (portInfo[name].port_type != port_type) begin: datatype
      `uvm_warning("trek_uvm_pkg::audit_port_info()",
        {prefix, "is of datatype '", portInfo[name].port_type,
         "' but you use type '", port_type, "'"})
    end
    if (portInfo[name].primary_txn_type != primary_type) begin: primary
      `uvm_warning("trek_uvm_pkg::audit_port_info()",
        {prefix, "uses primary transaction type '",
         portInfo[name].primary_txn_type, "' but you use type '",
         primary_type, "'"})
    end
    if (portInfo[name].port_base_type == "trek_master_port") begin: only_master_port
      if (portInfo[name].secondary_txn_type != secondary_type) begin: secondary
        `uvm_warning("trek_uvm_pkg::audit_port_info()",
          {prefix, "uses secondary transaction type '",
           portInfo[name].secondary_txn_type, "' but you use type '",
           secondary_type, "'"})
      end
    end: only_master_port
  end: checks
endfunction: audit_port_info

`endif  // GUARD__TREK_PORT_HELPERS__SV
