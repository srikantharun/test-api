### Steps to setup Formality run for an IP Block(Ex. `l1`):

1. cd to the IP dir, Ex: `hw/ip/l1/default`.

   ```bash
   cd hw/ip/l1/default
   ```

2. Run the following cookiecutter command that creates a new directory `fm`. Enter the correct `block` name details when prompted.

   ```bash
   module load cookiecutter/default
   cookiecutter  --verbose ../../../scripts/cookiecutter/formality_directory
   ```

   This new directory will include pre-configured Formality run configuration.

3. CD to this new directory:

   ```bash
   cd fm && ls
   ```

   The directory should contain:

   I. `Makefile` - a symbolic link to the Formality make file in `hw/scripts/flow_makefiles/fm.mk`

   II.  `fm.tcl` - pre configured input file for formality to run the comparisons

   III. `run.tcl` - run setup for Formality, specifically environment setup for run.

      ```
      # NETLIST_TYPE should be set from the cmdline using the -x directive
      # If NETLIST_TYPE not set, the default is rtla

      #source $REPO_ROOT/fm_ip_versions.tcl

      if ![info exist NETLIST_TYPE] {
      puts "WARNING: NETLIST_TYPE not set. Defaulting to rtla"
      set NETLIST_TYPE "rtla"
      }

      if { $NETLIST_TYPE == "rtla" } {
      puts "INFO: using rtla netlist as compare netlist"
      } elseif { $NETLIST_TYPE == "pdsyn" } {
      set PD_RELEASE_VERSION  $SYN_SUB_VER_l1
      puts "INFO: using $NETLIST_TYPE from $PD_RELEASE_DIR/$PD_RELEASE_VERSION"
      } elseif { $NETLIST_TYPE == "rtl_dft" } {
      puts "INFO: using DFT inserted RTL as implementation design"
      } else {
      puts "ERROR: unkown netlist type $NETLIST_TYPE"
      exit
      }
   ```
   
   IV. `fm_constrains.tcl` - additional config required to run formality, including pre configured setup to run comparisons:

      ```
      if { $NETLIST_TYPE == "rtla" } {
      puts "INFO: applying formality constraints for rtla netlist"
      } elseif { $NETLIST_TYPE == "pdsyn" } {
      puts "INFO: applying formality constraints for pdsyn netlist"
      } elseif { $NETLIST_TYPE == "rtl_dft" } {
      puts "INFO: applying formality constraints for DFT inserted RTL"
      } else {
      puts "ERROR: given netlist type $NETLIST_TYPE not supported."
      exit
      }
      ```
   

4. Run `formality`:

   ```bash
   make formality
   ```

   This command will run formality based on configuration.

5. Clean:

   To cleanup the directory of any previous formality run, simply do:

   ```
   make clean_formality
   ```

   This will remove all the temporary run files created by formality.
