# (C) Copyright Axelera AI 2024
# All Rights Reserved
# *** Axelera AI Confidential ***
#
# Owner: Jovin Langenegger <jovin.langenegger@axelera.ai>
# Description: project-agnostic CMake configuration for VerifSDK

enable_testing()

# verifsdk_register_test
# ----------------------
# This function handles the project-agnostic part of the CMake configuration.
# This includes templating the run script and adding the test to CTest
# (multiple times if seeds are specified).
#
# Arguments
# - NAME:       name of the test (and test directory)
# - RUN_SCRIPT: absolute path to the run script
# - RUN_ARGS:   additional arguments to pass to the run script
# - SEEDS:      list of seeds for test execution (optional)
#
# The "output" of this function is a ${NAME}_run_script target, which should be
# depended upon by the "main target" for the test.
function(verifsdk_register_test)
    set(one_value_args NAME RUN_SCRIPT)
    set(multi_value_args RUN_ARGS SEEDS)
    cmake_parse_arguments(ARG "" "${one_value_args}" "${multi_value_args}" ${ARGN})

    set(test_dir "${ARG_NAME}")
    set(run_sh_name "run.sh")
    set(run_sh_path "${test_dir}/${run_sh_name}")

    # add custom target *_run_script, which will be depended upon by the calling code
    add_custom_target(${ARG_NAME}_run_script
        DEPENDS ${run_sh_path}
    )

    # template run script
    string(JOIN " " run_args_spaced ${ARG_RUN_ARGS})
    set(run_script_contents
        "${ARG_RUN_SCRIPT} ${CMAKE_BINARY_DIR}/${test_dir}/${ARG_NAME} ${run_args_spaced} $@"
    )
    add_custom_command(
        COMMAND ${CMAKE_COMMAND} -E echo "#!/bin/sh" > ${run_sh_path}
        COMMAND ${CMAKE_COMMAND} -E echo "${run_script_contents}" >> ${run_sh_path}
        COMMAND chmod 755 ${run_sh_path}
        OUTPUT ${run_sh_path}
        COMMENT "Generating run script ${run_sh_path}"
        VERBATIM
    )

    # add to CTest
    if(DEFINED ARG_SEEDS AND NOT "${ARG_SEEDS}" STREQUAL "")
        # Add test to ctest
        foreach(SEED ${ARG_SEEDS})
        add_test(NAME ${ARG_NAME}_seed_${SEED}
            WORKING_DIRECTORY ${test_dir}
            COMMAND ${run_sh_name} --seed=${SEED}
        )
        endforeach()
    else()
        add_test(NAME ${ARG_NAME}
            WORKING_DIRECTORY ${test_dir}
            COMMAND ${run_sh_name}
        )
    endif()
endfunction()
