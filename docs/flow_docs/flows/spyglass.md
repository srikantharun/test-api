### Steps to setup Spyglass run for an IP Block(Ex. `l1`):

1. cd to the IP dir, Ex: `hw/ip/l1/default`.

   ```bash
   cd hw/ip/l1/default
   ```

2. Run the following cookiecutter command that creates a new directory `lint-spyglass_vc`. Enter the correct `block` and `author` details when prompted.

   ```bash
   cookiecutter  --verbose ../../../scripts/cookiecutter/lint_spyglass_directory
   ```

   This new directory will include pre-configured Spyglass run configuration.

3. CD to this new directory:

   ```bash
   cd lint-spyglass_vc && ls
   ```

   The directory should contain:

   I. `Makefile` - a symbolic link to the Spyglass make file in `hw/scripts/flow_makefiles/sg.mk`

   II. `sg_config.mk` - additional config required to run spyglass, including block name:

      ```make
      IP_NAME            ?= l2
      BENDER_MANI_LOC_RTL?= $(MAKEFILE_DIR)/../rtl
      BENDER_TARGETS 	 += -t rtl -t asic -t sf5a  
      ```
   
   III. `sg_workdir` - Directory containing the following files:
         `<block>_waivers.awl` - Spyglass waivers file - Modify as needed
         `lint_rtl_custom_rules.tcl` - Spyglass rules & goal config file - Modify as needed
         `sg_proj.prj` - Spyglass project file

4. Run `spyglass` or `spyglass_vc`:

   ```bash
   make spyglass
   ```
   ```bash
   make spyglass_vc
   ```

   This command will run bender to generate the `<block>.add_sources.tcl` file and call spyglass.

Other variables and targets in the flow:

```
  SG_FLOW_CONFIG                ="sg_config.mk"                                  Specify configuration options, modify if required
  SG_GOALS                      lint/lint_rtl                                    Goals to run spyglass
  SG_DIR                        sg_workdir                                       Spyglass working directory
  SG_BATCH                      -batch                                           Spyglass batchmode
  SG_VERSION                    U-2023.03                                        Spyglass version for module load
  SPYGLASS_TERA_TEMPATE         hw/scripts/bender_templates/spyglass_tcl.tera    Spyglass tera template for bender
  BENDER_SPYGLASS_TARGETS.      -t spyglass -t synopsy -t synthesis              Additional targets for spyglass
  spyglass                      Runs spyglass flow
  spyglass_vc                   Runs spyglass_vc flow
  clean_spyglass                Clean all spyglass generated files
```

#### Limitations:

1. SG project file does not import tech cell libs as in Triton.

   Need to check correct tech import tcl file with load function

   ![image.png](/uploads/a01f6a00d779cf537197fdf590ac3e86/image.png)
