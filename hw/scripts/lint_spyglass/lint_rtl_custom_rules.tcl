################################################################################
# SPYGLASS LINT
################################################################################
current_goal lint/lint_rtl

# Enable processing of big signals
set_parameter handle_large_bus yes;

# Keeping the oldest behavior for ip waivers
set_option compat_opts dont_check_ip_in_hierarchy;

# Enable parsing of SystemVerilog constructs
set_option enableSV12 yes;

# Restricting rule W415a checking to nonblocking assignment statements. 
set_parameter checknonblocking yes;

# Do not use the reserved Verilog, System Verilog, or VHDL keywords.
set_goal_option addrules STARC05-1.1.1.3;
set_goal_option overloadrules STARC05-1.1.1.3+severity=Warning;

# Uninitializable flip-flop coexists with flip-flops having asynchronous reset/set description in the same block.
set_goal_option addrules STARC-2.3.6.1;
set_goal_option overloadrules STARC-2.3.6.1+severity=Error;

# Initial value and terminating condition of loop variable of for construct must be constant and the loop variable must not be modified inside the for construct. (Verilog)
set_goal_option addrules STARC05-2.9.1.2;
set_goal_option overloadrules STARC05-2.9.1.2+severity=Error;

# Mixing combinational and sequential styles.
set_goal_option addrules W238;
set_goal_option overloadrules W238+severity=Error;

# The last statement in a function does not assign to the function.
set_goal_option addrules W489;
set_goal_option overloadrules W489+severity=Error;

# Signals must be reset to constant values.
set_goal_option addrules NonConstReset-ML;
set_goal_option overloadrules NonConstReset-ML+severity=Error;

# Identifies assignments in which the LHS width is greater than the RHS width
set_goal_option addrules W164b;
set_goal_option overloadrules W164b+severity=Error;

# Only tristate pins may be WORed (multiple drivers only allowed, if all driving pins are of type tristate).
set_goal_option addrules checkMultipleDrivers;
set_goal_option overloadrules checkMultipleDrivers+severity=Error;

# The conditions of an if/unique-if/priority-if construct inside an always_comb block should be exhaustive.
set_goal_option addrules AlwaysCombExhaustive-ML;
# demoting to warning, as check is wrong, default assignments are not picked up. Latch finding is done in other rules anyhow:
set_goal_option overloadrules AlwaysCombExhaustive-ML+severity=Warning;

# Bit data type signal has been used in the design.
set_goal_option addrules BitDataType-ML;
set_goal_option overloadrules BitDataType-ML+severity=Error;

# Ensures that two variables of different enumerated data types are not compared
set_goal_option addrules EnumBaseComparison-ML;
set_goal_option overloadrules EnumBaseComparison-ML+severity=Error;

# Data type objects (user-defined type declarations and definitions of identifiers) should not be present or visible in global Scope.
set_goal_option addrules GlobalDataTypeDefined-ML;
set_goal_option overloadrules GlobalDataTypeDefined-ML+severity=Error;

# Interface Signal Name conflicts with other signal name
set_goal_option addrules InterfaceNameConflicts-ML;
set_goal_option overloadrules InterfaceNameConflicts-ML+severity=Error;

# Interfaces should make use of modport declarations.
set_goal_option addrules InterfaceWithoutModport-ML;
set_goal_option overloadrules InterfaceWithoutModport-ML+severity=Error;

# Ensures that variable name are not same as that of the System Verilog type-defined name
set_goal_option addrules TypedefNameConflict-ML;
set_goal_option overloadrules TypedefNameConflict-ML+severity=Error;

# Unique, Unique0, or priority case constructs used with full_case or parallel_case or both.
set_goal_option addrules UniqueCase-ML;
set_goal_option overloadrules UniqueCase-ML+severity=Error;

# Do not declare unpacked structure outside the package.
set_goal_option addrules UnpackedStructUsed-ML;
set_goal_option overloadrules UnpackedStructUsed-ML+severity=Error;

# The SelfDeterminedExpr-ML rule flags use of self determined arithmetic expressions present in the design.
set_goal_option addrules SelfDeterminedExpr-ML;
set_goal_option overloadrules SelfDeterminedExpr-ML+severity=Error;

# ImproperRangeIndex-ML Possible discrepancy in the range index or slice of an array
set_goal_option addrules ImproperRangeIndex-ML;
set_goal_option overloadrules ImproperRangeIndex-ML+severity=Error;

#  flip-flop should have an asynchronous set or an asynchronous reset
set_goal_option addrules { STARC05-3.3.1.4b }

# Width mismatch checks.
set_goal_option addrules { W164a_b }
set_goal_option addrules { W164a_a }

# Operator <= or >= used in binary expressions with std_logic, std_ulogic, , std_logic_vector or std_ulogic_vector type operands
set_goal_option addrules { ReportCompOperator-ML }

# Do not use an instance name identical to involved master name 
set_goal_option addrules { InstNameSameAsMaster-ML }

# Do not use a port name identical to the unit name
set_goal_option addrules { PortNameSameAsModule-ML }

# Repeat statements are non-synthesizable
set_goal_option addrules { NonSynthRepeat-ML }

# Reports violation for modules without any port.
set_goal_option addrules { CheckModulesWithoutPorts-ML }

# Reports violation for registers with self-gating logic
set_goal_option addrules { SelfGatingRegister-ML }

# While/forever loop has no break control 
set_goal_option addrules { infiniteloop }

# PWRDN pins of cells should be connected to either IO cells or sequential elements.
set_goal_option addrules { pwrdnPinConnToSeqOrIOCells }

# Do not specify flip-flop initial value using initial construct. (Verilog)
set_goal_option addrules { STARC05-2.3.4.1 }

# Do not use while-loop statement in the design (VHDL)
set_goal_option addrules { STARC-2.1.10.4 }

# task constructs should not be used in the design. (Verilog)
set_goal_option addrules { STARC-2.1.2.5 }

# Do not use bit and bit_vector data types in the design (VHDL)
set_goal_option addrules { STARC-2.1.2.4 }

# Do not use set_dont_touch directive directly on cells 
set_goal_option addrules { STARC-1.6.6.2 }

# Do not use fork-join constructs. (Verilog)
set_goal_option addrules { STARC-2.7.4.3 }

# Do not use fork-join constructs. (Verilog)
set_goal_option addrules { STARC05-2.7.4.3 }

# Reports initial construct used.
set_goal_option addrules { STARC05-2.3.4.2 }

# Specify Range for std_logic_vector (VHDL)
set_goal_option addrules { STARC-2.1.2.6 }

# The SafeLatch-ML rule checks for all the unsafe suspect latches.
#set_goal_option addrules { SafeLatch-ML }

# Checks for asynchronous pin configurations in library cells
set_goal_option addrules { AsyncPinsOfLibraryCells-ML }

# Destination of an assignment is an IN port
set_goal_option addrules { W397 }

# Duplicate design unit
set_goal_option addrules { W546 }

# Event variable appearing in a posedge/negedge expression
set_goal_option addrules { W326 }

# 
set_goal_option addrules { RegOutputs }
set_goal_option overloadrules RegOutputs+severity=Error;

set_parameter handle_large_bus yes
set_parameter checknonblocking yes

set_option sgsyn_loop_limit 100000


##################################################################################
### SPYGLASS CDC
##################################################################################
##current_goal cdc/cdc_verify_struct
##
###Setting convergence sequential depth t3
##set_parameter conv_sync_seq_depth 3;
##
###Increase threshold limit to avoid false triggering rule FLAT_504. Macro logic evaluation done partially as its size crosses the threshold limit
##set_option define_cell_sim_depth 17;
##
##
##################################################################################
### SPYGLASS DFT
##################################################################################
##current_goal dft/dft_best_practice
### Rule: BIST_01
### flopInFaninCount: The default value is 150. Set the value of the parameter to any natural number to set the maximum limit on the total number of flip-flops and black boxes allowed in the data pin fan-in cone of any flip-flop as checked by the BIST_01 rule.
##set_parameter flopInFaninCount 200000
### Rule: Topology_10
### pathDepth: The default value is 500. Set the value of the parameter to any natural number to set the maximum limit on the number of combinational logic levels that can be present between two registers.
##set_parameter pathDepth 6000
##
##################################################################################
### SPYGLASS DESIGN AUDIT
##################################################################################
##current_goal lint/design_audit
##set_goal_option rules Clock_info15

current_goal none

