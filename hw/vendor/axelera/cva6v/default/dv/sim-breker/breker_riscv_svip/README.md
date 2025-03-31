# Bringing up Trek Hello test #

## Setup to run Trek tool ##

```shell
% pushd /apps/eda/breker/trek5-2.1.7-GCC6_el7
% source bin/setup.csh (or setup.bash)
% popd
```
***NOTE*** This breaks our sim flow so you need to do this in a separate shell

## Generate your first test ##

```shell
% tar xf breker_riscv_svip.tgz
% cd breker_riscv_svip/run/
% make hello
```

You should see something like

```shell
trek: info: Loading property file ../yaml/platform.yaml...
trek: info: Loading property file /mnt/dev_data/work/git/dev/trek5/examples/tutorials/svip/treksvip/yaml/treksvip.yaml...
trek: info: Loading property file /mnt/dev_data/work/git/dev/trek5/examples/tutorials/svip/treksvip/tests/test_hello.yaml...
[...]
trek: info: memory resource ddr0: initialization mode set to TREK_MEMORY_INIT_BACKDOOR with base address 0x78000000
trek: info: memory resource C2TMBOXES: initialization mode set to TREK_MEMORY_INIT_BACKDOOR with base address 0x80002000
trek: info: memory resource T2CMBOXES: initialization mode set to TREK_MEMORY_INIT_BACKDOOR with base address 0x80003000
Generating scenario # 1...
Generating scenario # 2...
trek: info: Generating file: /mnt/dev_data/work/git/sup/customers/mips/breker_riscv_svip/run/trek_hello.c
trek: info: Generating file: /mnt/dev_data/work/git/sup/customers/mips/breker_riscv_svip/run/trek_hello.tbx
trek: info: Coverage file: /mnt/dev_data/work/git/sup/customers/mips/breker_riscv_svip/run/trek_hello.tcv
```

Note that files `trek_hello.c` and `trek_hello.tbx` have been created.

Run
```shell
% trekdebug trek_hello.tbx
```

## Compile the generated test case ##

Compile generated `test_hello.c` using the same flow that was used previously for `test_qual.c`


## Generate UVM code ##

```shell
% cd breker_riscv_svip/run/
% make uvm_output
```

You should see:

```shell
[...]
trek: info: Generated uvm_output/trek_uvm_pkg.sv
```

Review the generated uvm files:

```shell
% ls uvm_output/
```

You should see

```shell
trek_check_port.sv		     trek_master_port_delay_req_delay_req.sv  trek_tlm_adapter.sv
trek_delay_req_delay_req_adapter.sv  trek_master_port.sv		      trek_uvm_events.sv
trek_delay_req.sv		     trek_mbox_wrapper.sv		      trek_uvm_pkg.sv
trek_dpi_pkg.sv			     trek_port_base.sv			      trek_uvm.sv
trek_dpi.sv			     trek_port_helpers.sv
trek_get_port.sv		     trek_put_port.sv
```

In particular review file `trek_uvm.sv`

```c++
  // This module contains the method that the user calls to start TrekSoC.
  // It also contains methods that are called by TrekSoc, to indicate that
  // transaction data is available, and to issue messages in a consistent manner.
  module trek_uvm();
  […]
  export "DPI-C" function trek_backdoor_read64;
  export "DPI-C" function trek_backdoor_write64;
  // *** IMPORTANT ***
  // You must define the methods "trek_backdoor_read64()" and
  // "trek_backdoor_write64()" void functions for your system
  // and put them in a file with this name so the compiler
  // fetches it here! They need to appear in this "scope".
  `include "trek_user_backdoor.sv"
  […]
endmodule: trek_uvm
```

This file is including the `sv/trek_user_backdoor.sv` that was previously developed when running the Breker Qual Test


## Integrate TrekBox to your testbench compile ##

-   instantiate the `trek_uvm()` as a top level module in your testbench

-   Add the generated `trek_uvm_pkg.sv` to your simulator file list.

-   Add an `+incdir+/path/to/uvm_output` to include the set of generated SV files.

-   Add `+incdir+` to the directory containing your `trek_user_backdoor.sv` file

-   Add `-sv_lib ${BREKER_ARCH}/lib/libtrek.so` DPI library to your simulation build.


## Call do\_backdoor\_init() from your testbench ##

This is currently done in `sv/trek_user_backdoor.sv`, but can be moved else where in the testbench:

```verilog
initial begin: main
   // Design specific:
   //   Wait here for reset and memory load of static data and code
   @(posedge `DELAY_INIT);
   // trigger start of backdoor initialization
   trek_uvm_pkg::trek_uvm_events::do_backdoor_init();
```

## Call trek\_poll\_mbox() every memory clock  ##

This is currently done in `sv/trek_user_backdoor.sv`, but can be moved else where in the testbench:

```verilog
// Design specifc: one stage delayed so write has a time to settle
always @(posedge `DELAY_CLK) begin: read_all_mailboxes
  trek_poll_mbox();
end
```

## Run trek\_hello test with +TREK\_TBX\_FILE plusarg ##

Run the compile `trek_hello` test case with the plusarg `+TREK_TBX_FILE=path/to/trek_hello.tbx`

You should see log messages similar to:

```shell
UVM_INFO @ 0: reporter [trek] trek: Starting with +TREK_TBX_FILE=tut_sdv-hello.tbx
UVM_INFO @ 0: reporter [trek] trek: Waiting for user to call trek_uvm_events::do_backdoor_init(##)...
UVM_INFO @ 1201ns: reporter [trek] trek: info: Generating file: CMAKE_CURRENT_BINARY_DIR/tbi/soc/src/tut_sdv-hello.tdb
UVM_INFO @ 1201ns: reporter [trek] trek: info: random seed: 0x4a88a0cc
UVM_INFO @ 1201ns: reporter [trek] trek: info: ****  Start of Test ****
UVM_INFO BREKER_HOME/examples/designs/uvm_ref/uart/sequences/apb_master_seq.sv(##) @ 1201ns: uvm_test_top.env.apb_cpu0.master.sequencer@@cpu0_seq [cpu0_seq(apb_master_seq)] trek: uvm: starting 'cpu0_seq'(apb_master_seq) on a port with tb_path 'cpu0' using adapter 'adapter'.
UVM_INFO @ 135550ns: reporter [trek] trek: info: **** Start of Processor cpu0 Iteration **** [event:0x7 MAIN iteration: 1]
UVM_INFO @ 152150ns: reporter [trek] trek: info: Thread trek_cpu0_T0 started [event:0x2 MAIN iteration: 1]
UVM_INFO @ 163850ns: reporter [trek] trek: info: Begin entry.1 [event:0x3 agent:cpu0 thread:T0 instance:entry.1 iteration: 1]
UVM_INFO @ 163850ns: reporter [trek] trek: info: [hello.entry]: Hello World - TARGET (RUNTIME) [event:0x3 agent:cpu0 thread:T0 instance:entry.1 iteration: 1]
UVM_INFO @ 175550ns: reporter [trek] trek: info: End entry.1 [event:0x4 agent:cpu0 thread:T0 instance:entry.1 iteration: 1]
UVM_INFO @ 205850ns: reporter [trek] trek: info: Thread trek_cpu0_T0 completed [event:0x5 MAIN iteration: 1]
UVM_INFO @ 224250ns: reporter [trek] trek: info: Processor cpu0 iteration done [event:0x8 MAIN iteration: 1]
UVM_INFO @ 242650ns: reporter [trek] trek: info: Get test status [event:0xa MAIN iteration: 1]
UVM_INFO @ 242650ns: reporter [trek] trek: info: ****  End of Test ****
UVM_INFO @ 242650ns: reporter [trek] trek: info: **** Test Report Summary ****
trek: info: summary: 9 Events Executed ( Last Event: 0x4 Instance: entry.1 )
trek: info: summary: Test PASSED
```

Please check the following in your log:

-   a message that contains `trek: Starting with +TREK_TBX_FILE=` .tbx file provide
-   a message related to `do_backdoor_init`
-   a message for the test start `trek: info: ****** Start of Test ****`
-   a message when the test ends `trek: info: ****** End of Test ****`
-   a report message `trek: info: ****** Test Report Summary ****`
-   final status message of PASSED or FAILED `trek: info: summary: Test PASSED`
