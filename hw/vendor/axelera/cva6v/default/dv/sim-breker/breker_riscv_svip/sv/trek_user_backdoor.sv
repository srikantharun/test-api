/// custom routines defined for the platform

// These two routines are specific to a particular design. They are used
// to read and write to the "mailbox" locations, to synchronize behaviors
// between C code on the processors with activity performed in UVM (and
// among activities in UVM).
//
// Every design will be different. Here we just have a simple Verilog
// array that we can read and write.
//

import "DPI-C" function void tb_memory_read(
  input longint addr,
  input int len,
  output byte data[]
);
import "DPI-C" function void tb_memory_write(
  input longint addr,
  input int len,
  input byte data[],
  input bit strb[]
);

function automatic void trek_backdoor_read64(
  input longint unsigned address,
  output longint unsigned data,
  input     int unsigned debug = 1);

  byte _data_[8];

  if (address[1:0] != 2'b00) begin: misaligned
    $display("%t trek_backdoor_read64: Misaligned address", $time);
    $finish();
  end

  tb_memory_read(address, 8, _data_);
  for (int j = 0; j < 8; j++) begin
    data[j*8+:8] = _data_[j];
  end
  if (data != 0)
    $display("%t trek_backdoor_read64: Read 64'h%016h from address 64'h%016h", $time, data, address);
endfunction: trek_backdoor_read64


function automatic void trek_backdoor_write64(
  input longint unsigned address,
  input longint unsigned data,
  input     int unsigned debug = 1);

  byte _data_[8];
  byte _strb_[8];

  if (address[1:0] != 2'b00) begin: misaligned
    $display("%t trek_backdoor_write64: Misaligned address", $time);
    $finish();
  end

  for (int j = 0; j < 8; j++) begin
    _data_[j] = data[j*8+:8];
    _strb_[j] = byte'('1);
  end
  tb_memory_write(address, 8, _data_, _strb_);

  $display("%t trek_backdoor_write64: Wrote 64'h%016h to address 64'h%016h", $time, data, address);
endfunction: trek_backdoor_write64

// For performance, we want to read mailboxes ONLY when they're written to!
// (This is very important on emulators!)
//
// Here we trigger a signal when a memory write happens to the range of
// addresses where the mailboxes are.
//
// A clock later, we go poll all the mailboxes (using the "backdoor_read"
// method above.
//
// Each design will be different, depending on where you are able to snoop
// for writes and how long it takes a write to propagate from that point
// to the place where the backdoor read will find it.

// Design specifc: one stage delayed so write has a time to settle
always @(posedge`DELAY_CLK iff `DELAY_INIT) begin: read_all_mailboxes
  trek_poll_mbox();
end

initial begin: main
   // Design specific:
   //   Wait here for reset and memory load of static data and code
   @(posedge `DELAY_INIT);

   // trigger start of backdoor initialization
   trek_uvm_pkg::trek_uvm_events::do_backdoor_init();
end : main
