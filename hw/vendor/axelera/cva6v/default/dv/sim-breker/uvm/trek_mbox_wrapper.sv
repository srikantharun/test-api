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
`ifndef GUARD__TREK_MBOX_WRAPPER__SV
`define GUARD__TREK_MBOX_WRAPPER__SV

// Example helper class that CAN be used to fire trek_poll_mbox() when
// a Trek mailbox write occurs (when Trek has placed T2C and C2T
// mailboxes into memory.
//
// It goes and reads/clears those C2T/T2C mailboxes only when a user
// calls trek_uvm_pkg::trek_poll_mbox(). In simulation, there's not much
// overhead to do it every clock, but in emulation we want to minimize
// backdoor reads and writes.
//
// This helper class can help ensure that happens efficiently.
//
// You can see the trek-side of this mechanism in trek_uvm.sv. It waits
// for a user to put an address that was written to into an "SV mailbox".
// (Unfortunate name collision...)  When the address matches one used by
// Trek for its backdoor communications it fires the trek_poll_mbox().
// If unused, this code will sit quietly.
//
// To use this style, in your code (typically in trek_user_backdoor.sv)
// you fetch the trek_mbox_wrapper handle from the uvm_config_db. Each
// time you see a write to your memory, you send the addresss. Here's
// pseudo code...
//
//     trek_mbox_wrapper   mbox_wrapper;
//
//     uvm_config_db#(trek_mbox_wrapper)::get(
//         this, "", "mbox_wrapper", mbox_wrapper);
//
//     always @(write_seen)
//       ...wait_for_data_to_settle_where_backdoor_is_peeking...
//       mbox_wrapper.mbox_event.put(address);
//

  class trek_mbox_wrapper extends uvm_object;

    mailbox#(longint unsigned) mbox_event;

    `uvm_object_utils(trek_mbox_wrapper)

    function new(string name = "trek_mbox_wrapper");
      super.new(name);
      mbox_event = new(0); // unbounded!
    endfunction

  endclass: trek_mbox_wrapper

`endif  // GUARD__TREK_MBOX_WRAPPER__SV
