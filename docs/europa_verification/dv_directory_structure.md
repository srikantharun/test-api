# DV Directory Structure

## Common DV Components

The expectation here is that these are generic re-useable components.
In the case of RTL and UVM we’ll assume they’ll be compiled into all test-benches, but that doesn’t mean they’ll be elaborated.
For the rest as they won’t be picked up by Bender, they can be explicitly added via the makefiles.

Can be:

- Docs
    - Whatever makes sense markdown, word, excel, csv
- UVM code (in-house developed or small imports)
    - Sub-dirs in here are freeform - team can divide as they feel is sensible
- RTL code
    - Common modules / macros / functions used in multiple test-benches
    - Follow LD team w.r.t. include directory
    - Sub-dirs, again, freeform - team to divide up in most sensible way
- C code (used in test-benches + models not tools - see scripts)
    - PLI, VPI, DPI code
    - High performance functional models
- Coverage
    - Common excludes
    - UNR infrastructure
    - Custom merge scripts
- Scripts
    - Scripts and tools used across the team
    - Use correct shebang and file extensions to be obvious

```
hw
|-- dv
|   |-- docs
|   |-- rtl
|   |   |-- <files>
|   |   |-- include
|   |   |   |- <files>
|   |   |-- module0
|   |   |   |-- include
|   |   |   |   |- <files>
|   |   |   |- <files>
|   |-- uvm
|   |   |-- package0
|   |   |   |-- <files> + <directories>
|   |   |-- package1
|   |   |   |-- <files> + <directories>
|   |-- c
|   |   |-- <files> + <directories>
|   |-- coverage
|   |   |-- <files> + <directories>
|   |-- scripts
|   |   | -- <files> + <directories>
```

## IP Specific DV components

- Just because the code here is associated with an IP doesn’t mean it’s not re-usable.
    - For example we may have monitors and checkers for MVM in the IP directory, but it will also be picked up in AICORE or top level test-benches.
- The difference between this and the common is that it’s not generic.
    - For example in common we may have a UVM scoreboard class (threaded with good debug / helper functions). In the IP directory we may extend this to be an MVM specific scoreboard class.
- Keep the same sub-dirs (rtl, uvm etc.) as common / shared code.
- Add sim as the directory to contain executable test-benches and associated helper scripts)
    - If there are multiple test-benches (sim environments) they can also have rtl, uvm, etc. code 

```
hw
|-- ip
|   |-- <ipname>/<version>
|   |   |-- dv
|   |   |   |-- docs
|   |   |   |-- rtl
|   |   |   |-- uvm
|   |   |   |-- c
|   |   |   |-- coverage
|   |   |   |-- scripts
|   |   |   |-- sim
|   |   |   |   |-- docs
|   |   |   |   |-- rtl
|   |   |   |   |-- uvm
|   |   |   |   |-- c
|   |   |   |   |-- coverage
|   |   |   |   |-- scripts
|   |   |   |   |-- README
```
