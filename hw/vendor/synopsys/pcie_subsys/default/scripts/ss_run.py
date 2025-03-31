#! /usr/bin/env python3

import subprocess

# Arrange your testcases based on the VPLAN
testcases=[
#"basic_soft_rst ",
#"basic_warm_rst ",
#"reg_access_invalid_reg ",
#"ss_phy_internal_loopback_jtag ",
#"pl_speed_change ",
#"ft_rasdp ",
#"ft_ras_des_event_count ",
#"ft_ras_des_tba ",
#"ss_fsm_track ",
#"ss_pcie_int ",
#"tl_cpl_timeout ",
#"ft_ras_des_einj ",
#"tl_dynamic_linkwidth ",
"tl_basic ",
#"ss_debug_signals ",
#"pl_link_down ",
#"pm_pcipm_l1 ",
#"tl_msi ",
"tl_enumeration ",
#"pm_pcipm_l2 ",
#"tl_rx_msg ",
#"tl_msg_misc ",
#"tl_vmi ",
#"ss_pipe_loopback ",
#"tl_perst ",
#"tl_linkup ",
#"ss_reg_bit_bash ",
#"ss_reg_hw_reset ",
#"tl_msg_vdm ",
#"tl_msg_ltr ",
"reg_pcie_bit_bash ",
"reg_pcie_hw_reset ",
"reg_pcie_wire_access ",
"ss_reg_phy_access ",
#"ss_apb_timeout "
#"tl_hdma_wr_rd ",
#"tl_hdma_ll_wr_rd ",
#"tl_msg_obff ",
#"ss_err_rpt ",
#"pm_l1_clk_pm ",
#"pm_aspm_l0s ",
]
 
# Add supported configurations
cfg_all = "_ep_mode"
 
# Add extra options that needed for the simulation
long_option = "LONG_SIM"

# Add the group options available in testlist
group_option = ["ral", "all"]

# Add ways to run the testcase/s
run_options = ["Regression", "Group", "Sanity Check", "Testcase/s"]

# Get user input for regression testing or specific test cases
print("Available Run Options:")
for index, run_option in enumerate(run_options, start=1):
    print(f"{index}. {run_option}")
test_option = int(input("Select from Run options available ? "))
print(test_option)
 
if test_option == 1:
    # Execute the ./run command for regression testing
    #run_command = "./run.scr -scratch -nosva -nodbg &" //to disable pipe assertions
    #run_command = "./run.scr -scratch -nodbg &"
    run_command = "./run.scr -localdisk -nodbg &"
    print("Executed Command \n")
    print(run_command)
    result = subprocess.Popen(run_command, shell=True)
    if result.returncode !=0:
        #If any error in code following will display
        print("Error:", result.communicate())
    else:
        #No error
        print(result.communicate())

elif test_option == 2:
    print("Available Group Options:")
    for index, group_sel in enumerate(group_option, start=1):
        print(f"{index}. {group_sel}")
    group_option_sel = int(input("Select from group options available ? "))

    if group_option_sel == 1:

        # Execute the ./run command for regression testing
        #run_command = "./run.scr -scratch -group ral -nosva -nodbg &" //to disable pipe assertions
        run_command = "./run.scr -scratch -group ral  -nodbg &"
        print("Executed Command \n")
        print(run_command)
        result = subprocess.Popen(run_command, shell=True)
        if result.returncode !=0:
            #If any error in code following will display
            print("Error:", result.communicate())
        else:
            #No error
            print(result.communicate())

    else:

        # Execute the ./run command for regression testing
        #run_command = "./run.scr -scratch -group all -nosva -nodbg &" //to disable pipe assertions
        run_command = "./run.scr -scratch -group all -nodbg &"
        print("Executed Command \n")
        print(run_command)
        result = subprocess.Popen(run_command, shell=True)
        if result.returncode !=0:
            #If any error in code following will display
            print("Error:", result.communicate())
        else:
            #No error
            print(result.communicate())

elif test_option == 3:
    # Execute the ./run command for regression testing
    #run_command = "./run.scr -scratch -testlist tests/DWC_pcie_subsystem_sanity.test_list -nosva -nodbg -dumpfsdb &" //to disable pipe assertions 
    run_command = "./run.scr -scratch -testlist tests/DWC_pcie_subsystem_sanity.test_list -nodbg -dumpfsdb &"
    print("Executed Command \n")
    print(run_command)
    result = subprocess.Popen(run_command, shell=True)
    if result.returncode !=0:
        #If any error in code following will display
        print("Error:", result.communicate())
    else:
        #No error
        print(result.communicate())
else:
    # Get user input for testcases
    print("Available testcases:")
    for index, testcase in enumerate(testcases, start=1):
        print(f"{index}. {testcase}")
 
    testcase_choices = input("Enter the numbers of the testcases you want to run (comma-separated): ")
    testcase_indexes = [int(choice) - 1 for choice in testcase_choices.split(",")]
    selected_testcases = [testcases[index] for index in testcase_indexes]
 
    # Check if user wants to run with default run option
    default_input = input("Run the testcase with default options (-dumpfsdb & -scratch ) (y/n): ")
    if default_input.lower() == "y":
        filename = "DS_SS_pcie_subsystem_local.test_list"
 
        # Construct and print the commands
        with open(filename, "w") as file:
            for testcase in selected_testcases:
                cfg = cfg_all
                command = f"{testcase}       -uid {cfg}        --  GROUP=all \n"
                file.write(command)

 
        print("The local testlist is created as", filename)
        
        #run_command = f"./run.scr -testlist DS_SS_pcie_subsystem_local.test_list -scratch -nosva -nodbg -dumpfsdb &" //to disable pipe assertions
        run_command = f"./run.scr -testlist DS_SS_pcie_subsystem_local.test_list -scratch -nodbg -dumpfsdb &"
        print(run_command)

        ## Execute the command
        result = subprocess.Popen(run_command, shell=True)
        if result.returncode !=0:
            #If any error in code following will display
            print("Error:", result.communicate())
        else:
            #No error
            print(result.communicate())
    else:

        # Check if user wants to include long option
        long_input = input("Do you want to include the LONG option? (y/n): ")
        long_dict = {}

        if long_input == "y":
            print("Selected Testcases:")
            for index, testcase in enumerate(selected_testcases, start=1):
                print(f"{index}. {testcase}")

            long_testcases = input("Enter the number of the testcases you want to long (comma-separated), or 'all' for all testcases: ").lower()

            if long_testcases == "all":
                for testcase in selected_testcases:
                    long_dict[testcase] = long_option
            else:
                long_indexes = [int(choice.strip()) - 1 for choice in long_testcases.split(",")]
                for index in long_indexes:
                    long_dict[selected_testcases[index]] = long_option


        # Check if user wants to repeat the testcases
        repeat_input = input("Do you want to repeat test cases ?(y/n):").lower()
        repeat_dict = {}

        if repeat_input == "y":
            print("Selected Testcases:")
            for index, testcase in enumerate(selected_testcases, start=1):
                print(f"{index}. {testcase}")

            repeat_testcases = input("Enter the number of the testcases you want to repeat (comma-separated), or 'all' for all testcases: ").lower()

            if repeat_testcases == "all":
                repeat_count = input ("Enter the number of times you want to repeat the testcase: ")
                for testcase in selected_testcases:
                    repeat_dict[testcase] = repeat_count
            else:
                repeat_indexes = [int(choice.strip()) - 1 for choice in repeat_testcases.split(",")]
                selected_testcases_repeat = [selected_testcases[index] for index in repeat_indexes]

                for index in repeat_indexes:
                    repeat_count = input(f"Enter the number of times you want to repeat {selected_testcases_repeat[index]}: ")
                    repeat_dict[selected_testcases_repeat[index]] = repeat_count

        filename = "DS_SS_pcie_subsystem_local.test_list"
 
        # Construct and print the commands
        with open(filename, "w") as file:
            for testcase in selected_testcases:
                cfg = cfg_all
                
                long_option_str = long_dict.get(testcase, "")
                repeat_option = f"REPEAT={repeat_dict[testcase]}" if testcase in repeat_dict else ""
                command = f"{testcase}       -uid {cfg}        --  GROUP=all       {long_option_str}      {repeat_option} \n"
                file.write(command)

 
        print("The local testlist is created as", filename)
   
        # Take the input of scratch disk or local disk from the user
        scratch_input = input("Do you want to run in scratch or localdisk? (s/l): ")

        if scratch_input.lower() == "l":
            scratch_en = "-localdisk"
        else:
            scratch_en = "-scratch"

        # Take the input of waves enabled or not from the user.
        dump_input = input("Do you want to run with the WAVEFORM (.fsdb)? (y/n): ")

        if dump_input.lower() == "y":
            #run_command = f"./run.scr -testlist DS_SS_pcie_subsystem_local.test_list {scratch_en} -nosva -nodbg -dumpfsdb &" //to disable pipe assertions
            run_command = f"./run.scr -testlist DS_SS_pcie_subsystem_local.test_list {scratch_en} -nodbg -dumpfsdb &"
            print("Executed Command \n")
            print(run_command)
        else:
            #run_command = f"./run.scr -testlist DS_SS_pcie_subsystem_local.test_list {scratch_en} -nosva -nodbg &" //to disable pipe assertions
            run_command = f"./run.scr -testlist DS_SS_pcie_subsystem_local.test_list {scratch_en} -nodbg &"
            print("Executed Command \n")
            print(run_command)
        
        # Execute the command
        result = subprocess.Popen(run_command, shell=True)
        if result.returncode !=0:
            #If any error in code following will display
            print("Error:", result.communicate())
        else:
            #No error
            print(result.communicate())

