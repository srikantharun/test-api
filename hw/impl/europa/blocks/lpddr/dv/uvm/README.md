# Status

This `uvm/` directory contains the exact testbench + RTL delivery as provided by Siemens.

This testbench version contains the SS3 DFT inserted RTL.

Current `lpddr_subsystem_sanity_test` is failing - this is expected on this release.

More test are deliverd with this drop, but these haven't been debugged by Siemens yet (no point in running them).

# Steps to run

```
cd $REPO_ROOT
source .env-default-modules
cd hw/impl/europa/blocks/lpddr/dv/uvm/
source set_siemens_lpddr_testbench
cd project_benches/sim/
make TEST=lpddr_subsystem_sanity_test NO_WAVE=1 VERBOSITY=UVM_HIGH
```
