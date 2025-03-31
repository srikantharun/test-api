################################################
### GDB automatic triton test load and execution
################################################

##### CONSTANTS #####
set width 0
set height 0
set verbose off
set logging file gdb.output
set logging enabled on

##### DEFINITIONS #####
define hook-quit
    set confirm off
end

##### SCRIPT START #####

# shut down OpenOCD once GDB detaches from it
monitor [target current] configure -event gdb-detach {shutdown}

# load your elf
printf "- Load your executable file\n"
load

# Set a breakpoint at system_completion
b exit

# Run your app until hitting a breakpoint
run

# Now we should hit a breakpoint at system_completion
# First arg of system_completion is return code
if $a0 == 0
    printf "- TEST_SUCCESS !\n"
else
    printf "- TEST_FAILED with exit_code: %d\n", $a0
end

set logging enabled off

# Forward return code of system_completion
quit $a0
