---
title: "Bender Style Guide"
doc:
  status: draft
  version: [0, 0, 0]
  confidentiality: internal
---

## Table of Contents

- [Table of Contents](#table-of-contents)
- [Basics](#basics)
- [About .bender.yml](#about-root-benderyml)
- [Example Bender.yml Manifest](#example-benderyml-manifest)
- [Detailed](#detailed)
  - [Package (*REQUIRED*)](#package-required)
    - [Package: Name (*REQUIRED*)](#package-name-required)
    - [Package: Description (*RECOMMENDED*)](#package-description-recommended)
    - [Package: Authors (*REQUIRED*)](#package-authors-required)
  - [Dependencies (*OPTIONAL*)](#dependencies-optional)
  - [Export\_include\_dirs (*OPTIONAL*, *NOT RECOMMENDED*)](#export_include_dirs-optional-not-recommended)
  - [Sources (*REQUIRED*)](#sources-required)
    - [Sources: Target (*OPTIONAL*)](#sources-target-optional)
      - [Sources: Target: Default Targets](#sources-target-default-targets)
      - [Sources: Target: Simulation and Synthesis](#sources-target-simulation-and-synthesis)
      - [Sources: Target: Technology Specifier](#sources-target-technology-specifier)
      - [Sources: Target: DFT Insertion](#sources-target-dft-insertion)
    - [Sources: Library (*OPTIONAL*)(*Currently not supported!*)](#sources-library-optionalcurrently-not-supported)
    - [Sources: Include\_dirs (*OPTIONAL*)](#sources-include_dirs-optional)
    - [Sources: Defines (*OPTIONAL*)](#sources-defines-optional)
    - [Sources: Files (*RECOMMENDED*)](#sources-files-recommended)

## Basics

`Bender` is a dependency management tool for hardware design projects.
It provides a way to define dependencies between hardware IPs and generate scripts for compiling said sources for various tools.

Initially `bender` was developed at the IIS group of ETH and [open-sourced on GitHub](https://github.com/pulp-platform/bender).
For Axelera a [fork on GitLab](https://git.axelera.ai/ai-hw-team/bender) was made to facilitate internal needs and customizations.

The `Bender.yml` manifest describes the relative location of hardware source files.
This guide defines how to write the `Bender.yml` manifest. The goals are:

* Promote consistency throughout the project.
* Cleanly separate hardware source-file dependencies between:
  * RTL code
  * Testbench / Verification code
  * Technology / Synthesis specifics

Preamble: The key words "*MUST*", "*MUST NOT*", "*REQUIRED*", "*SHALL*", "*SHALL NOT*", "*SHOULD*", "*SHOULD NOT*", "*RECOMMENDED*", "*NOT RECOMMENDED*", "*MAY*", and "*OPTIONAL*" in this document are to be interpreted as described in [BCP 14](https://tools.ietf.org/html/bcp14) [RFC2119](https://tools.ietf.org/html/rfc2119) [RFC8174](https://tools.ietf.org/html/rfc8174) when, and only when, they appear in all capitals, as shown here.


## About .bender.yml

The `.bender.yml` file is used as a global registry of all packages used in the project.
This aim to reduce maintenance when changing a package path and to make sure any package is unique.

* All packages are *REQUIRED* to be listed in `${REPO_ROOT}/.bender.yml`
* A package *SHALL* be added in form: **<pkg_name>: { path: "path/to/pkg" }**

Example of `.bender.yml`:

```yaml
overrides:

  pkg:         { path: "path_to/pkg" }
  another_pkg: { path: "path_to/another_pkg" }
````


## Example Bender.yml Manifest

It is *REQUIRED* that the manifest file is named `Bender.yml`. So each directory *MUST* only include one `Bender.yml` manifest file.

To separate the dependency trees is is *REQUIRED* that per IP a `Bender.yml` manifest exist in the respective folder for:
  * `rtl` or `src` (*REQUIRED*): Containing all RTL source files.
    * `package:name:` *SHALL* be `<ip_name>`
  * `rtl/pkg` or `src/pkg` (*OPTIONAL*): Containing packages expected to be used in different IP, amount of dependencies *SHALL* be small.
    * `package:name:` *SHALL* be `<ip_name>_pkg`
  * `verif` (*REQUIRED*): Containing all verification testbenches and verification sources for the IP. This *MUST* call the `rtl` manifest as a direct dependency.
    * `package:name:` *SHALL* be `<ip_name>_verif` or `<ip_name>_tb`
  * `syn` (*OPTIONAL*): Containing synthesis wrappers for trial synthesis.

Example folder structure and respective manifests for an IP:

```bash
ip
├── doc
├── rtl
│   ├── pkg
│   │   └── Bender.yml <--- Specifies RTL package sources to be included by other IP
│   ├── ip_pkg.sv
│   ├── ip_file_0.sv
│   ├── ip_file_1.sv
│   └── Bender.yml     <--- Specifies RTL sources (MAY depend on rtl/pkg/Bender.yml)
├── dv
│   ├── ip_tb.sv
│   └── Bender.yml     <--- Specifies Verification sources (MUST depend on rtl/Bender.yml)
└── syn
    ├── ip_synth.sv
    └── Bender.yml     <--- Specifies Synthesis wrapper sources (MUST depend on rtl/Bender.yml)
```

There *MAY* exists an IP top-level `Bender.yml` which contains the default verification manifest as sole dependency.

The example manifest provided here *SHALL* serve as an example. It is *RECOMMENDED* that only strictly required keys are used.
Each file in the example has a unique name. The suffix indicates the inter file dependency. E.g.: `file_3_01.sv` instantiates constructs from `file_0.sv` and `file_1.sv`.

```yaml
package:
  name: <manifest_name>
  description: "This Bender.yml serves as a simple example"
  authors:
    - "Code Owner <code.owner@axelera.ai>"
    - "Author Alice <author.alice@axelera.ai>"
    - "Author Bob <author.bob@axelera.ai>"

dependencies:
  dep_1: { path: "path/to/top/../path/to/dep_1" }
  dep_2: { path: "path/to/top/../path/to/dep_2" }

sources:
  - files:
      # Packages
      - package_1_pkg.sv
      - package_2_pkg.sv

  - target: rtl
    files:
      # Level 0
      - file_0.sv
      - file_1.sv
      # Level 1
      - file_2_0.sv
      - file_3_01.sv
      # Level 2
      - file_4_023.sv

  - target: simulation
    include_dirs:
      - dv/
    files:
      # Level 0
      - uvm_env_pkg.sv
      # Level 1
      - hdl_top.sv
```

## Detailed

This section goes into detail for each of the keywords which *MAY* appear in a `Bender.yml` manifest and the rules to use them.

*Note:* This is not an exhaustive list of all possible configuration options and serves as a guideline for the most common cases.

### Package (*REQUIRED*)

The *REQUIRED* manifest top-level `package` key describes the metadata associated with the IP package.
It is used for bookkeeping and to call in this package as a dependency.

#### Package: Name (*REQUIRED*)

Each package manifest *MUST* have a unique name in the project. The usual IP naming conventions from the [**styleguide**](https://git.axelera.ai/ai-hw-team/docs/-/wikis/Style-Guides/Style-Guide-RTL) apply.
For packages belonging to a testbench or IP verification, i.e. calling the RTL IP as a dependency, the Ip name is suffixed with the purpose. For implementation the overall implementation name *MUST* be prefixed.

Example:

```yaml
# RTL manifest name example
package:
  name: <ip_name>_pkg

# RTL sources manifest example:
package:
  name: <ip_name>

dependencies:
  <ip_name>_pkg: { path: "pkg" }

# Implementation manifest example:
package:
  name: <impl_name>_<ip_name>

dependencies:
  <ip_name>: { path: "path/to/<ip_name>" }
```


#### Package: Description (*RECOMMENDED*)

It is *RECOMMENDED* that each package manifest contains a small description detailing the purpose of the hardware IP.

Example:

```yaml
package:
  description: "This is an example of a Bender.yml manifest."
```

#### Package: Authors (*REQUIRED*)

A list of code authors *MUST* be provided with each package and *SHALL* follow the following structure:

* The name plus email *SHALL* be added as a list item in the form: **- "User Name <user.name@axelera.ai>"**
* The code-owner *MUST* be listed first.
* Multiple additional authors *MAY* exist and *SHALL* be listed in alphabetical order.

Example:

```yaml
package:
  authors:
    - "Code Owner <code.owner@axelera.ai>"
    - "Author Alice <author.alice@axelera.ai>"
    - "Author Bob <author.bob@axelera.ai>"
```


### Dependencies (*OPTIONAL*)

A dependency calls in the dependency subtree containing all files required for that specific package.
It is defined that:

* An IP *MAY* have none, one or multiple dependencies.
* A dependency *SHALL* be added in form: **<dep_name>: { path: "" }**
* For readability it is *RECOMMENDED* that the `path` keywords are aligned.
* To help with the project structure, all dependency paths first *SHALL* go via the repository root.
* It is *REQUIRED* to **only add direct dependencies** of an IP.

A direct dependency is defined as when:

* A `module` form the dependency is used.
* A SystemVerilog `package` from the respective dependency is used.
* An `include` from the dependency is used. For this it is *REQUIRED* that the include directory is listed under `export_include_dirs`.

Example:

```yaml
dependencies:
  # As all dependencies are stored in the .bender.yml, path **SHALL** be left empty
  my_dep:       { path: "" }
  # Legacy path declaration
  my_other_dep: { path: "${REPO_ROOT}/go/to/my_dep/bender/package/directory" }
```


### Export_include_dirs (*OPTIONAL*, *NOT RECOMMENDED*)

This setting *SHALL* only be used, when other packages are in need to have access to the include directories, i.e. for `typedef` macros or verification IP. Note that the include directory only propagates up **one level of hierarchy**. To use an include of another package, it *MUST* be added as a direct dependency.

* It is *RECOMMENDED* to use `include_dirs` locally for each fileset.

Example:
```yaml
export_include_dirs:
  - to/include/dir
```

### Sources (*REQUIRED*)

Here all *REQUIRED* source files for this IP are specified. Each file can be listed separately, however it is *RECOMMENDED* that source files are grouped as much as possible using the **`files`** keyword.

A source file group:

* *MUST* be specified in compile order.
* *SHALL* only contain files belonging to the IP. It is *NOT RECOMMENDED* to add files directly from different IPs. To add a file from a different IP is is *RECOMMENDED* to call in the respective dependency.
* *SHALL* be grouped in levels.
  * Packages: *SHALL* be listed first and in compile order.
  * Level 0: *SHALL* have only package dependencies.
  * Level 1: Files *SHALL* depend only on files in level 0.
  * Level 2: Files *SHALL* depend only on files in level 0 and 1.
  * Files within a level *SHALL* be ordered alphanumerically.
* *MUST* only contain source files written in the same HDL (Verilog/SystemVerilg/VHDL).

Example:

```yaml
sources:
  # This filegroup is compiled first.
  - files:
      # Packages
      - package_0.sv
      - package_1.sv
      # Level 0
      - file_0.sv
      - file_1.sv
      # Level 1
      - file_2_0.sv
      - file_3_01.sv
      # Level 2
      - file_4_0123.sv

  # This filegroup is compiled second
  - files:
      # Level 0
      - file_5.vhd
      - file_6.vhd
      # Level 1
      - file_7_56.vhd
```


#### Sources: Target (*OPTIONAL*)

The target keyword provides flags which *MAY* be used to filter source files.

Targets specify a simple expression language, as follows:

* `*` matches any target (*NOT RECOMMENDED*)
* `name` matches the target "name"
* `all(T1, ..., TN)` matches if all of the targets `T1` to `TN` match (boolean *AND*)
* `any(T1, ..., TN)` matches if any of the targets `T1` to `TN` match (boolean *OR*)
* `not(T)` matches if target `T` does not match (boolean *NOT*)

In general if the RTL source is synthesizable for any technology, a target specifier *MUST NOT* be used.

The allowed targets *SHALL* be the following:

| Target Combination              | Usecase |
| ---                             | ---     |
| `simulation`                    | **Testbench** and general **simulation models**. |
| `all(asic, sf5a)`               | Files using `tsmc12` technology cells. (**synthesizable**) |
| `all(asic, sf5a, simulation)`   | **Simulation models** for tsmc12 `library_cells` and `hardmacros`. |
| `all(fpga, xilinx)`             | Files using `xilinx` technology cells. (**synthesizable**) |
| `synthesis`                     | **IP-Level Synthesis Wrapper** for sanity synthesis |
| `dft`                           | For files added by **dft insertion**. |
| `not(dft)`                      | For original RTL files **before** dft insertion. |


##### Sources: Target: Default Targets

**NOTE:** The `bender` script generation will specify **defines for default targets**. it can be disabled by providing the `--no-default-target` to the `bender` command.

This has two impacts:

1. Files flagged with the respective target are included in any bender generated output:
  * **<target>** : *(RECOMMENDED)* : provided from the outside with the `bender <command> -t <target>` switch
  * **<tool>** : *(NOT RECOMMENDED)* : depending on the `bender script <tool>` that is generated
  * **simulation** : (RECOMMENDED) : if the *<tool>* is a simulator
  * **synthesis** : (RECOMMENDED) : if the *tool* is a synthesizer
2. For `Verilog/Systemverilog` scripts the **default defines are set!**. It is *NOT RECOMMENDED* to use these in any sourcecode!
  * **TARGET_<TARGET>**: for all targets provided to the bender command
  * **TARGET_<TOOL>**: for the tool the script is generated
  * **TARGET_SIMULATION**: for simulation tools
  * **TARGET_SYNTHESIS**: for synthesis tools

Example of the default defined targets in generated VCS script:

```shell
bender script vcs -t asic -t tsmc12
```

| Files tracked in Manifest with target | Defines Specified in Verilog analyze |
| ------------------------------------- | ------------------------------------ |
| target: asic                          | +define+TARGET_ASIC                  |
| target: tsmc12                        | +define+TARGET_TSMC12                |
| target: vcs                           | +define+TARGET_VCS                   |
| target: simulation                    | +define+TARGET_SIMUALTION            |

Example of the default defined targets in generated SYNOPSYS script:

```shell
bender script synopsys -t asic -t tsmc12
```

| Files tracked in Manifest with target | Defines Specified in Verilog analyze |
| ------------------------------------- | ------------------------------------ |
| target: asic                          | +define+TARGET_ASIC                  |
| target: tsmc12                        | +define+TARGET_TSMC12                |
| target: synopsys                      | +define+TARGET_SYNOPSYS              |
| target: synthesis                     | +define+TARGET_SYNTHESIS             |


##### Sources: Target: Simulation and Synthesis

Not all RTL code is synthesizable.

* `simulation`: *MUST* be used to flag simulation models and non-synthesizable testbench code.
* `synthesis`: *SHALL* be used for synthesis wrappers.

Examples:

```yaml
sources:
  # Testbench code MUST be behind the simulation target
  - target: simulation
    files:
      - my_tb.sv

  # For synthesis wrapper
  - target: synthesis
    files:
      - my_synth_wrapper.sv
```

##### Sources: Target: Technology Specifier

Sources (instantiating cells) belonging to a specific technology *MUST* be flagged with a tuple of the form **`all(<type>, <node>)`**.

Additionally non-synthesizable simulation models of a technology cell / blackbox *MUST* be flagged with the tripel **`all(<type>, <node>, simulation)`**.

The `<type>` and respective `<node>` *SHALL* be of:

* `asic`: Specifies sources targeting an ASIC technology.
  * `all(asic, tsmc12)`: Specifies the TSMC12 technology node.
* `fpga`: Specifies sources targeting an FPGA technology.
  * `all(fpga, xilinx)`: Specifies any Xilinx FPGA.

Examples:

```yaml
sources:
  # General non-synthesizable simulation model
  - target: all(any(not(asic), not(fpga)), simulation)
    files:
      - rtl/axe_tcl_sram.sv

  # Simulation models for the tsmc12 technology
  - target: all(asic, tsmc12, simulation)
    files:
      - tsmc12/models/model_0.v
      - tsmc12/models/model_1.v

  # Technology specific synthesizable RAM wrapper
  - target: all(asic, tsmc12)
    files:
      - tsmc12/axe_tcl_sram_tsmc12.sv

  # Technology specific synthesizable RAM wrapper
  - target: all(fpga, xilinx)
    files:
      - xilinx/axe_tcl_sram_xilinx.sv
```


##### Sources: Target: DFT Insertion

The DFT insertion currently adds different files to partitions. The ports and names of the modules change.
To switch between non-DFT and DFT design one *SHALL* use the `dft` target.

* `dft`: *SHALL* be used to switch between RTL sources with DFT inserted structures.
  * `not(dft)`: *SHALL* be used for the non-inseted partition.
  * `dft`: *SHALL* be used for all dft inserted modules.

Examples:

```yaml
sources:
  # Non-DFT RTL
  - target: not(dft)
    files:
      - ai_core_p.sv

  # DFT inserted
  - target: dft
    include_dirs:
      - dft/sms_modules
    files:
      - dft/dft_replaced_submodule.sv
      - dft/ai_core_p.sv
```


#### Sources: Library (*OPTIONAL*)(*Currently not supported!*)

The `library` keyword *MAY* be used to specify a specific design compile library for the respective file goup. This *MUST* be used for *VHDL* sources which use a different library other than *WORK*.

Example:

```yaml
sources:
  # The library keyword is used to secify a compile library
  - library: ip_lib
    files:
      - file_in_ip_lib_0.vhd
      - file_in_ip_lib_1.vhd
```


#### Sources: Include_dirs (*OPTIONAL*)

The `include_dirs` keyword specifies a path for a `Verilog/SystemVerilg` include directory for the respective file group.
It is *RECOMMENDED* that `include` directories:

* *SHALL* only be added where necessary.
* *SHALL* be specified with local relative paths.
* *SHALL* belong to the IP the manifest belong to.

It is *NOT RECOMMENDED* to add a local `include` directory from a different IP.

* It is *RECOMMENDED* to use a dependency with the `include` directory listed in `export_include_dirs` instead.

Example:

```yaml
sources:
  # The include_dirs keyword is local to the filegroup
  - include_dirs:
      # Specific include directory relative from the manifest location
      - include
      # Directory where the manifest is located
      - .
    files:
      - file_using_include_0.sv
      - file_using_include_1.sv

# If the include directory shall be used by other IP
export_include_dirs:
  - include/to/be/used/by/other/ip

# If include directory of another IP has to be used
dependencies:
  ip_with_export_include_dirs: { path: "../../../this/ip/has/a/export_include_dirs" }
```


#### Sources: Defines (*OPTIONAL*)

The `defines` keyword specifies a dictionary for all `Verilog/Systemverilog` defines which are added statically for the respective file group.
The defines *MAY* be used to always configure a define for a respective IP. E.g.: To configure an IP and having the same configuration for all modes.

Note: A define will **only** apply for the respective source file group! To define a define globally for all sources use:

```shell
# RECOMMENDED
bender script <tool> --vlog-arg="+define+<define>..."

# NOT RECOMMENDED
bender script <tool> -D <define>...
bender script <tool> --define <define>...
```

To specify locally a define for a source file group:

```yaml
sources:
  - defines:
      # Define without a value for this group.
      EXCLUDE_MAGIC: ~
      # Define with a value for this group.
      PREFIX_NAME: prefix_
    files:
      # Package
      - package.sv
      # Level 0
      - file_0.sv
      - file_1.sv
```


#### Sources: Files (*RECOMMENDED*)

This describes the list of files for which the aforementioned keys belong to. This keyword groups source files together into a compilation/analyse unit.

* It is *RECOMMENDED* to group source files together as much as possible with the `files` keyword.
* It is *REQUIRED* to use the `files` keyword when any other keyword (e.g. `target`, `library`, `include_dirs`, `defines`) is used for the filegroup.

Example of two source file groups showing advanced usage:

```yaml
sources:
  # This is the first fileset and  is compiled before the next one
  - target: all(asic, tsmc12)
    # If the files should be compiled for a different library than the default one
    library: ip_lib
    # Provide the local include directories
    include_dirs:
      - path/to/include_1
      - path/to/include_2
    # Defines for this fileset
    defines:
      # Define without a value for this group.
      EXCLUDE_MAGIC: ~
      # Define with a value for this group.
      PREFIX_NAME: prefix_
    # Definition of source files
    files:
      # Package
      - package.sv
      # Level 0
      - file_0.sv
      - file_1.sv
      # Level 1
      - file_2_01.sv
      # Level 2
      - file_3_2.sv

  # This is fileset 2 and is compiled after the previous one
  # The dash indicating a group MAY NOT be inline with the keys.
  - # And MAY contain a comment describing the group instead.
    target: all(asic, tsmc12)
    # It is RECOMMENDED to adapt manifest comments as seem fit
    files:
      # File groups can be nested (NOT RECOMMENDED).
      # SHALL be used with utmost care, e.g technology synthesis/simulation model switch.
      # Here as example an if/else for simulation/synthesis model switch.
      - target: simulation
        files:
          - model_0.sv
          - model_1.sv
      - target: synthesis
        files:
          - synth_0.sv
          - synth_1.sv
```
