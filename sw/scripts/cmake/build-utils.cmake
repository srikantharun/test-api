# Naming Convention:
# - common: for all processors in the system
# - shared or library: for all tests

#------------------------------------------------------
# Toolchain
#------------------------------------------------------
set(CMAKE_C_COMPILER "clang")
set(CMAKE_CXX_COMPILER "clang++")
set(CMAKE_OBJDUMP "llvm-objdump")
set(CMAKE_OBJCOPY "llvm-objcopy")

set(CMAKE_C_COMPILER_WORKS 1 CACHE INTERNAL "Force C Compiler to be treated as working")
set(CMAKE_CXX_COMPILER_WORKS 1 CACHE INTERNAL "Force CXX Compiler to be treated as working")

#--------------------------------------------------
# Directories
#--------------------------------------------------
set(TEST_DIR ${CMAKE_CURRENT_SOURCE_DIR}/src/tests)
set(LIB_DIR ${CMAKE_CURRENT_SOURCE_DIR}/src/lib)
set(COMMON_DIR ${LIB_DIR}/common)
set(AX65_DIR ${LIB_DIR}/ax65)
set(CVA6V_DIR ${LIB_DIR}/cva6v)
set(AICORE_DIR ${LIB_DIR}/aicore)
set(PVE_DIR ${LIB_DIR}/pve)

#--------------------------------------------------
# Core architectures
#--------------------------------------------------
# The reasons for using the large code model (-mcmodel=large) are documented
# in https://git.axelera.ai/prod/europa/-/issues/779.
set(RISCV_TARGET "riscv64-unknown-elf")
set(AX65_ARCH
  --target=${RISCV_TARGET}
  -mcmodel=large
  -march=rv64gc
  -mabi=lp64d
)
# TODO: Add "v" to CVA6V architecture string once vector units are available.
set(CVA6V_ARCH
  --target=${RISCV_TARGET}
  -mcmodel=large
  -march=rv64imafc_zicsr_zifencei_zve32f_zfh_zvfh_zfhmin
  -mabi=lp64f
)
set(CVA6V_VLEN 4096)

#--------------------------------------------------
# Compiler flags (common, AX65)
#--------------------------------------------------
set(COMMON_C_FLAGS
  -DPREALLOCATE=1
  -static
  -std=gnu99
  -ggdb
  -ffreestanding
  -ffast-math
  -fno-common
  -mno-relax
  -Wall
  -Wextra
  -Werror
)
set(AX65_C_FLAGS
  ${AX65_ARCH}
  ${COMMON_C_FLAGS}
)
set(CVA6V_C_FLAGS
  ${CVA6V_ARCH}
  ${COMMON_C_FLAGS}
  -menable-experimental-extensions
  -mllvm --riscv-v-vector-bits-min=${CVA6V_VLEN}
  -fno-vectorize
  -fno-slp-vectorize
  # make it harder to use double-precision soft-float by accident
  -Werror=double-promotion
)

#--------------------------------------------------
# Libraries
#--------------------------------------------------
set(AX65_LINK_LIBRARIES -lm)
set(CVA6V_LINK_LIBRARIES -lm)

#--------------------------------------------------
# Linker flags
#--------------------------------------------------
set(LINKER_SCRIPT ${COMMON_DIR}/link.ld)
set(COMMON_LINK_OPTIONS -fuse-ld=lld -static -nostdlib)
set(AX65_LINK_OPTIONS ${AX65_ARCH} ${COMMON_LINK_OPTIONS})
set(CVA6V_LINK_OPTIONS ${CVA6V_ARCH} ${COMMON_LINK_OPTIONS})
# CVA6V standalone linker script
set(CVA6V_LINKER_SCRIPT ${CVA6V_DIR}/link.ld)

#-------------------------------------------------------------------------------
# Helper functions
#-------------------------------------------------------------------------------

function(run_hook)
  # argument parsing
  set(oneValueArgs
    NAME
  )
  set(multiValueArgs
    CALL
  )
  cmake_parse_arguments(HOOK "${options}" "${oneValueArgs}" "${multiValueArgs}" ${ARGN})

  if(HOOK_CALL)
    execute_process(
      COMMAND ${HOOK_CALL}
      RESULT_VARIABLE result
      OUTPUT_VARIABLE output
      ERROR_VARIABLE error
    )
    string(REGEX REPLACE "\n$" "" cleaned_output "${output}")
    string(REGEX REPLACE "\n$" "" cleaned_error "${error}")
    if(result)
      message(STATUS "${HOOK_NAME}: ${cleaned_output}")
      message(FATAL_ERROR "${HOOK_NAME}: ${cleaned_error}")
    else()
      message(STATUS "${HOOK_NAME}: ${cleaned_output}")
      if(cleaned_error)
        message(WARNING "${HOOK_NAME}: ${cleaned_error}")
      endif()
    endif()
  endif()
endfunction()

# add_europa_linked_object
# ------------------------
# Creates a "linked object" (a.k.a. relocatable object). This contains the full
# text and data for any single processor. Output file (linked+prefixed object)
# will be located at ${BUILD_DIRECTORY}/${NAME}_prefixed.o.
#
# Arguments:
# - BUILD_DIRECTORY:    directory used for build artifacts, including final linked and prefixed object file
# - NAME:               name of the target
# - PREFIX:             prefix to use for sections and symbols
# - SOURCES:            list of sources files to compile
# - INCLUDE_DIRECTORES: list of include directories, for target_include_directories()
# - COMPILE_OPTIONS:    list of compiler options, for target_compile_options()
# - LINK_OPTIONS:       list of linker options, for target_link_options()
# - LINK_LIBRARIES:     list of libraries, for target_link_libraries()
function(add_europa_linked_object)
  # argument parsing
  set(oneValueArgs
    BUILD_DIRECTORY
    NAME
    PREFIX
  )
  set(multiValueArgs
    SOURCES
    INCLUDE_DIRECTORIES
    COMPILE_OPTIONS
    LINK_OPTIONS
    LINK_LIBRARIES
  )
  cmake_parse_arguments(ARG "${options}" "${oneValueArgs}" "${multiValueArgs}" ${ARGN})

  # file names and paths
  set(linked_object_name "${ARG_NAME}_linked.o")
  set(linked_object_path "${ARG_BUILD_DIRECTORY}/${linked_object_name}")
  set(tmp1_object_path "${ARG_BUILD_DIRECTORY}/${ARG_NAME}_tmp1.o")
  set(tmp2_object_path "${ARG_BUILD_DIRECTORY}/${ARG_NAME}_tmp2.o")
  set(prefixed_object_path "${ARG_BUILD_DIRECTORY}/${ARG_NAME}_prefixed.o")

  # "executable" target
  add_executable(${ARG_NAME} EXCLUDE_FROM_ALL ${ARG_SOURCES})
  set_target_properties(${ARG_NAME} PROPERTIES OUTPUT_NAME ${linked_object_name})
  set_target_properties(${ARG_NAME} PROPERTIES RUNTIME_OUTPUT_DIRECTORY ${ARG_BUILD_DIRECTORY})
  target_compile_options(${ARG_NAME} PRIVATE ${ARG_COMPILE_OPTIONS})
  target_include_directories(${ARG_NAME} PRIVATE ${ARG_INCLUDE_DIRECTORIES})
  target_link_libraries(${ARG_NAME} PRIVATE ${ARG_LINK_LIBRARIES})
  target_link_options(${ARG_NAME} PRIVATE -Wl,--relocatable ${ARG_LINK_OPTIONS})

  # Prefix sections and symbols for all processors except APU:
  if (NOT "${ARG_PREFIX}" STREQUAL "")
    # Prefix sections and symbols using objcopy(1) in three stages:
    # 1. prefix ALL sections and symbols
    add_custom_command(
      OUTPUT ${tmp1_object_path}
      COMMAND "${CMAKE_OBJCOPY}"
        --prefix-alloc-sections=.${ARG_PREFIX} --prefix-symbols=${ARG_PREFIX}_
        "${linked_object_path}" "${tmp1_object_path}"
      DEPENDS "${linked_object_path}"
      COMMENT "Creating prefixed (stage 1) C object ${tmp1_object_path}"
      VERBATIM
    )
    # 2. remove prefix again for fixed list of symbols
    set(uniquesymbols_list "${CMAKE_SOURCE_DIR}/src/lib/link/uniquesymbols_${ARG_PREFIX}.lst")
    add_custom_command(
      OUTPUT ${tmp2_object_path}
      COMMAND "${CMAKE_OBJCOPY}"
        --redefine-syms=${uniquesymbols_list}
        "${tmp1_object_path}" "${tmp2_object_path}"
      DEPENDS "${tmp1_object_path}" "${uniquesymbols_list}"
      COMMENT "Creating prefixed (stage 2) C object ${tmp2_object_path}"
      VERBATIM
    )
    # 3. Patch the float ABI encoded in the ELF file header to match the APU (i.e., lp64d).
    #    This is safe as code compiled for the different processors does not call each other.
    add_custom_command(
      OUTPUT ${prefixed_object_path}
      COMMAND patch_elf_float_abi lp64d "${tmp2_object_path}" "${prefixed_object_path}"
      DEPENDS "${tmp2_object_path}"
      COMMENT "Creating prefixed (stage 3) C object ${prefixed_object_path}"
      VERBATIM
    )
  else()
    # APU: no prefixing, simply copy file
    add_custom_command(
      OUTPUT ${prefixed_object_path}
      COMMAND ${CMAKE_COMMAND} -E copy "${linked_object_path}" "${prefixed_object_path}"
      DEPENDS "${linked_object_path}"
      COMMENT "Copying C object ${prefixed_object_path}"
      VERBATIM
    )
  endif()
endfunction()

#--------------------------------------------------
# Test macro
#--------------------------------------------------
# Arguments:
# - NAME:             name of the test
# - DESIGN:           design to compile for (one of top, aicore, pre, post)
# - RUN_SCRIPT:       script to run for test execution (with arguments)
# - PRE_COMPILATION:  script to run prior to ninja to fetch/generate test data
# - SRC_TEST_APU:     list of test sources for the APU
# - SRC_TEST_AICORE0: list of test sources for the AICORE 0
# - SRC_TEST_AICORE1, ..., SRC_TEST_AICORE7
#                      (not implemented yet)
# - SRC_TEST_PVE0:    list of test sources for the PVE 0
#                      (not implemented yet)
# - SRC_TEST_PVE1:    list of test sources for the PVE 1
#                      (not implemented yet)
# - SRC_TEST_CVA6V:   list of test sources for the CVA6V standalone
# - FLAGS:            list of compiler flags for all processors
# - SEEDS:            list of seeds for test execution (optional)
# - ATTRIBUTE_SRCS:   list of library sources for the "main" processor
# - ADDITIONAL_FLAGS: list of additional compiler flags for all processors

macro(add_europa_executable)
  # Parse the arguments passed to the macro
  set(oneValueArgs
    NAME
    DESIGN
    RUN_SCRIPT
  )
  set(multiValueArgs
    SRC_TEST_APU
    SRC_TEST_AICORE0
    SRC_TEST_AICORE1
    SRC_TEST_AICORE2
    SRC_TEST_AICORE3
    SRC_TEST_AICORE4
    SRC_TEST_AICORE5
    SRC_TEST_AICORE6
    SRC_TEST_AICORE7
    SRC_TEST_PVE0
    SRC_TEST_PVE1
    SRC_TEST_CVA6V
    PRE_COMPILATION
    FLAGS
    SEEDS
    ATTRIBUTE_SRCS
    ADDITIONAL_FLAGS
  )
  cmake_parse_arguments(ARG "${options}" "${oneValueArgs}" "${multiValueArgs}" ${ARGN})

  MESSAGE(VERBOSE "Arguments for add_europa_executable")
  MESSAGE(VERBOSE "===================================")
  MESSAGE(VERBOSE "NAME             ${ARG_NAME}")
  MESSAGE(VERBOSE "DESIGN           ${ARG_DESIGN}")
  MESSAGE(VERBOSE "PRE_COMPILATION  ${ARG_PRE_COMPILATION}")
  MESSAGE(VERBOSE "RUN_SCRIPT       ${ARG_RUN_SCRIPT}")
  MESSAGE(VERBOSE "SRC_TEST_APU     ${ARG_SRC_TEST_APU}")
  MESSAGE(VERBOSE "SRC_TEST_AICORE0 ${ARG_SRC_TEST_AICORE0}")
  MESSAGE(VERBOSE "SRC_TEST_AICORE1 ${ARG_SRC_TEST_AICORE1}")
  MESSAGE(VERBOSE "SRC_TEST_AICORE2 ${ARG_SRC_TEST_AICORE2}")
  MESSAGE(VERBOSE "SRC_TEST_AICORE3 ${ARG_SRC_TEST_AICORE3}")
  MESSAGE(VERBOSE "SRC_TEST_AICORE4 ${ARG_SRC_TEST_AICORE4}")
  MESSAGE(VERBOSE "SRC_TEST_AICORE5 ${ARG_SRC_TEST_AICORE5}")
  MESSAGE(VERBOSE "SRC_TEST_AICORE6 ${ARG_SRC_TEST_AICORE6}")
  MESSAGE(VERBOSE "SRC_TEST_AICORE7 ${ARG_SRC_TEST_AICORE7}")
  MESSAGE(VERBOSE "SRC_TEST_PVE0    ${ARG_SRC_TEST_PVE0}")
  MESSAGE(VERBOSE "SRC_TEST_PVE1    ${ARG_SRC_TEST_PVE1}")
  MESSAGE(VERBOSE "SRC_TEST_CVA6V   ${ARG_SRC_TEST_CVA6V}")
  MESSAGE(VERBOSE "FLAGS            ${ARG_FLAGS}")
  MESSAGE(VERBOSE "SEEDS            ${ARG_SEEDS}")
  MESSAGE(VERBOSE "ATTRIBUTE_SRCS   ${ARG_ATTRIBUTE_SRCS}")
  MESSAGE(VERBOSE "ADDITIONAL_FLAGS ${ARG_ADDITIONAL_FLAGS}")

  # split flags into build flags and run flags
  set(BUILD_FLAGS) # empty list
  set(RUN_FLAGS) # empty list
  set(CUSTOM_ELF_FLAG 0)
  set(RUN_SCRIPT_ONLY 0)
  foreach(flag ${ARG_FLAGS} ${ARG_ADDITIONAL_FLAGS})
    if(flag MATCHES "^-[^-].*")
      list(APPEND BUILD_FLAGS ${flag})
    else()
      list(APPEND RUN_FLAGS ${flag})
    endif()
    if(flag MATCHES "^ELF=")
      set(CUSTOM_ELF_FLAG 1)
    endif()
  endforeach()

  # directories relative to ${CMAKE_CURRENT_BINARY_DIR}
  set(target_temp_dir CMakeFiles/${ARG_NAME}.dir)
  set(target_test_dir ${ARG_NAME})

  # --------------------------------------------------------
  # decide for which processors to build
  # --------------------------------------------------------
  # Add ${ATTRIBUTE_SRCS} to the correct processor based on ${DESIGN}
  if(${ARG_DESIGN} STREQUAL "top")
    list(APPEND ARG_SRC_TEST_APU ${ARG_ATTRIBUTE_SRCS})
  elseif(${ARG_DESIGN} STREQUAL "aicore")
    list(APPEND ARG_SRC_TEST_AICORE0 ${ARG_ATTRIBUTE_SRCS})
  elseif(${ARG_DESIGN} STREQUAL "cva6v")
    list(REMOVE_ITEM RUN_FLAGS "RUN_SCRIPT_ONLY") # Flag `RUN_SCRIPT_ONLY` no longer needed
    if (${CUSTOM_ELF_FLAG} EQUAL 1)
      set(RUN_SCRIPT_ONLY 1)
    else()
      set(BUILD_CVA6V 1)
      list(APPEND ARG_SRC_TEST_CVA6V ${ARG_ATTRIBUTE_SRCS})
    endif()
  elseif((${ARG_DESIGN} STREQUAL "uvm") OR (${ARG_DESIGN} STREQUAL "todo"))
    set(RUN_SCRIPT_ONLY 1)
  else()
    message(FATAL_ERROR "${ARG_NAME}: Unknown value for DESIGN: ${ARG_DESIGN}")
  endif()

  # --------------------------------------------------------
  # Run pre compilation hook defined on a per test level
  # --------------------------------------------------------
  run_hook(NAME pre_compilation_${ARG_NAME} CALL ${ARG_PRE_COMPILATION})

  if(RUN_SCRIPT_ONLY)
    # --------------------------------------------------------
    # Create empty target
    # --------------------------------------------------------
    add_custom_target(${ARG_NAME} ALL)
  elseif(BUILD_CVA6V)
    # --------------------------------------------------------
    # Compile CVA6V standalone (separate flow, no prefixes)
    # --------------------------------------------------------
    # executable target
    add_executable(${ARG_NAME} ${ARG_SRC_TEST_CVA6V})
    # change output directory
    set_target_properties(${ARG_NAME} PROPERTIES RUNTIME_OUTPUT_DIRECTORY ${target_test_dir})
    # include directories
    target_include_directories(${ARG_NAME} PRIVATE
      ${CVA6V_DIR}/include
      ${CVA6V_DIR}/drv
      ${CVA6V_DIR}/kernel_layers/include
      ${COMMON_DIR}/include
      ${COMMON_DIR}/drv
      ${TEST_DIR}/tests_cva6v_dv/c/includes
      ${TEST_DIR}
    )
    # compile options
    target_compile_options(${ARG_NAME} PRIVATE ${BUILD_FLAGS} ${CVA6V_C_FLAGS})
    # link options/libraries
    target_link_options(${ARG_NAME} PRIVATE ${CVA6V_LINK_OPTIONS} -T ${CVA6V_LINKER_SCRIPT})
    target_link_libraries(${ARG_NAME} PRIVATE ${CVA6V_LINK_LIBRARIES})
    # add linker script as dependency
    set_target_properties(${ARG_NAME} PROPERTIES LINK_DEPENDS ${CVA6V_LINKER_SCRIPT})

  else()
    # --------------------------------------------------------
    # Compile C Code: linked+prefixed objects per processor
    # --------------------------------------------------------
    set(prefixed_objs) # empty list
    if (ARG_SRC_TEST_APU)
      # --------------------------------------------------------
      # Build APU
      # --------------------------------------------------------
      add_europa_linked_object(
        BUILD_DIRECTORY ${target_temp_dir}
        NAME ${ARG_NAME}_apu
        PREFIX "" # no prefixing for APU
        SOURCES ${ARG_SRC_TEST_APU}
        INCLUDE_DIRECTORIES
          ${AX65_DIR}/include
          ${AX65_DIR}/drv
          ${AX65_DIR}/drv/drv_fiat
          ${COMMON_DIR}/include
          ${COMMON_DIR}/drv
          ${TEST_DIR}
          ${TEST_DIR}/test_drv_fiat/regression # Drv-FIAT stimuli download directory
        COMPILE_OPTIONS ${BUILD_FLAGS} ${AX65_C_FLAGS}
        LINK_OPTIONS ${AX65_LINK_OPTIONS}
        LINK_LIBRARIES ${AX65_LINK_LIBRARIES}
      )
      list(APPEND prefixed_objs ${target_temp_dir}/${ARG_NAME}_apu_prefixed.o)
    endif()

    set(cva6v_include_dirs
      ${CVA6V_DIR}/include
      ${CVA6V_DIR}/drv
      ${CVA6V_DIR}/kernel_layers/include
      ${COMMON_DIR}/include
      ${COMMON_DIR}/drv
      ${TEST_DIR}
    )
    set(aicore_include_dirs
      ${AICORE_DIR}
      ${AICORE_DIR}/drv
      ${AICORE_DIR}/include
      ${AICORE_DIR}/testutils
      ${TEST_DIR}/test_drv_fiat/regression
    )
    set(pve_include_dirs
      ${PVE_DIR}/include
    )
    set(cva6v_compile_options ${BUILD_FLAGS} ${CVA6V_C_FLAGS})

    if (ARG_SRC_TEST_AICORE0)
      # --------------------------------------------------------
      # BUILD AICORE0
      # --------------------------------------------------------
      add_europa_linked_object(
        BUILD_DIRECTORY ${target_temp_dir}
        NAME ${ARG_NAME}_aicore0
        PREFIX aicore0
        SOURCES ${ARG_SRC_TEST_AICORE0}
        INCLUDE_DIRECTORIES ${cva6v_include_dirs} ${aicore_include_dirs}
        COMPILE_OPTIONS ${cva6v_compile_options}
        LINK_OPTIONS ${CVA6V_LINK_OPTIONS}
        LINK_LIBRARIES ${CVA6V_LINK_LIBRARIES}
      )
      list(APPEND prefixed_objs ${target_temp_dir}/${ARG_NAME}_aicore0_prefixed.o)
    endif()

    if (ARG_SRC_TEST_AICORE1)
      # --------------------------------------------------------
      # BUILD AICORE1
      # --------------------------------------------------------
      add_europa_linked_object(
        BUILD_DIRECTORY ${target_temp_dir}
        NAME ${ARG_NAME}_aicore1
        PREFIX aicore1
        SOURCES ${ARG_SRC_TEST_AICORE1}
        INCLUDE_DIRECTORIES ${cva6v_include_dirs} ${aicore_include_dirs}
        COMPILE_OPTIONS ${cva6v_compile_options}
        LINK_OPTIONS ${CVA6V_LINK_OPTIONS}
        LINK_LIBRARIES ${CVA6V_LINK_LIBRARIES}
      )
      list(APPEND prefixed_objs ${target_temp_dir}/${ARG_NAME}_aicore1_prefixed.o)
    endif()

    if (ARG_SRC_TEST_AICORE2)
      # --------------------------------------------------------
      # BUILD AICORE2
      # --------------------------------------------------------
      add_europa_linked_object(
        BUILD_DIRECTORY ${target_temp_dir}
        NAME ${ARG_NAME}_aicore2
        PREFIX aicore2
        SOURCES ${ARG_SRC_TEST_AICORE2}
        INCLUDE_DIRECTORIES ${cva6v_include_dirs} ${aicore_include_dirs}
        COMPILE_OPTIONS ${cva6v_compile_options}
        LINK_OPTIONS ${CVA6V_LINK_OPTIONS}
        LINK_LIBRARIES ${CVA6V_LINK_LIBRARIES}
      )
      list(APPEND prefixed_objs ${target_temp_dir}/${ARG_NAME}_aicore2_prefixed.o)
    endif()

    if (ARG_SRC_TEST_AICORE3)
      # --------------------------------------------------------
      # BUILD AICORE3
      # --------------------------------------------------------
      add_europa_linked_object(
        BUILD_DIRECTORY ${target_temp_dir}
        NAME ${ARG_NAME}_aicore3
        PREFIX aicore3
        SOURCES ${ARG_SRC_TEST_AICORE3}
        INCLUDE_DIRECTORIES ${cva6v_include_dirs} ${aicore_include_dirs}
        COMPILE_OPTIONS ${cva6v_compile_options}
        LINK_OPTIONS ${CVA6V_LINK_OPTIONS}
        LINK_LIBRARIES ${CVA6V_LINK_LIBRARIES}
      )
      list(APPEND prefixed_objs ${target_temp_dir}/${ARG_NAME}_aicore3_prefixed.o)
    endif()

    if (ARG_SRC_TEST_AICORE4)
      # --------------------------------------------------------
      # BUILD AICORE4
      # --------------------------------------------------------
      add_europa_linked_object(
        BUILD_DIRECTORY ${target_temp_dir}
        NAME ${ARG_NAME}_aicore4
        PREFIX aicore4
        SOURCES ${ARG_SRC_TEST_AICORE4}
        INCLUDE_DIRECTORIES ${cva6v_include_dirs} ${aicore_include_dirs}
        COMPILE_OPTIONS ${cva6v_compile_options}
        LINK_OPTIONS ${CVA6V_LINK_OPTIONS}
        LINK_LIBRARIES ${CVA6V_LINK_LIBRARIES}
      )
      list(APPEND prefixed_objs ${target_temp_dir}/${ARG_NAME}_aicore4_prefixed.o)
    endif()

    if (ARG_SRC_TEST_AICORE5)
      # --------------------------------------------------------
      # BUILD AICORE5
      # --------------------------------------------------------
      add_europa_linked_object(
        BUILD_DIRECTORY ${target_temp_dir}
        NAME ${ARG_NAME}_aicore5
        PREFIX aicore5
        SOURCES ${ARG_SRC_TEST_AICORE5}
        INCLUDE_DIRECTORIES ${cva6v_include_dirs} ${aicore_include_dirs}
        COMPILE_OPTIONS ${cva6v_compile_options}
        LINK_OPTIONS ${CVA6V_LINK_OPTIONS}
        LINK_LIBRARIES ${CVA6V_LINK_LIBRARIES}
      )
      list(APPEND prefixed_objs ${target_temp_dir}/${ARG_NAME}_aicore5_prefixed.o)
    endif()

    if (ARG_SRC_TEST_AICORE6)
      # --------------------------------------------------------
      # BUILD AICORE6
      # --------------------------------------------------------
      add_europa_linked_object(
        BUILD_DIRECTORY ${target_temp_dir}
        NAME ${ARG_NAME}_aicore6
        PREFIX aicore6
        SOURCES ${ARG_SRC_TEST_AICORE6}
        INCLUDE_DIRECTORIES ${cva6v_include_dirs} ${aicore_include_dirs}
        COMPILE_OPTIONS ${cva6v_compile_options}
        LINK_OPTIONS ${CVA6V_LINK_OPTIONS}
        LINK_LIBRARIES ${CVA6V_LINK_LIBRARIES}
      )
      list(APPEND prefixed_objs ${target_temp_dir}/${ARG_NAME}_aicore6_prefixed.o)
    endif()

    if (ARG_SRC_TEST_AICORE7)
      # --------------------------------------------------------
      # BUILD AICORE7
      # --------------------------------------------------------
      add_europa_linked_object(
        BUILD_DIRECTORY ${target_temp_dir}
        NAME ${ARG_NAME}_aicore7
        PREFIX aicore7
        SOURCES ${ARG_SRC_TEST_AICORE7}
        INCLUDE_DIRECTORIES ${cva6v_include_dirs} ${aicore_include_dirs}
        COMPILE_OPTIONS ${cva6v_compile_options}
        LINK_OPTIONS ${CVA6V_LINK_OPTIONS}
        LINK_LIBRARIES ${CVA6V_LINK_LIBRARIES}
      )
      list(APPEND prefixed_objs ${target_temp_dir}/${ARG_NAME}_aicore7_prefixed.o)
    endif()


    # TODO: build AICORE1, ..., AICORE7

    if (ARG_SRC_TEST_PVE0)
      # --------------------------------------------------------
      # BUILD PVE0
      # --------------------------------------------------------
      add_europa_linked_object(
        BUILD_DIRECTORY ${target_temp_dir}
        NAME ${ARG_NAME}_pve0
        PREFIX pve0
        SOURCES ${ARG_SRC_TEST_PVE0}
        INCLUDE_DIRECTORIES ${cva6v_include_dirs} ${pve_include_dirs}
        COMPILE_OPTIONS ${cva6v_compile_options}
        LINK_OPTIONS ${CVA6V_LINK_OPTIONS}
        LINK_LIBRARIES ${CVA6V_LINK_LIBRARIES}
      )
      list(APPEND prefixed_objs ${target_temp_dir}/${ARG_NAME}_pve0_prefixed.o)
    endif()

    if (ARG_SRC_TEST_PVE1)
    # --------------------------------------------------------
    # BUILD PVE1
    # --------------------------------------------------------
    add_europa_linked_object(
      BUILD_DIRECTORY ${target_temp_dir}
      NAME ${ARG_NAME}_pve1
      PREFIX pve1
      SOURCES ${ARG_SRC_TEST_PVE1}
      INCLUDE_DIRECTORIES ${cva6v_include_dirs} ${pve_include_dirs}
      COMPILE_OPTIONS ${cva6v_compile_options}
      LINK_OPTIONS ${CVA6V_LINK_OPTIONS}
      LINK_LIBRARIES ${CVA6V_LINK_LIBRARIES}
    )
    list(APPEND prefixed_objs ${target_temp_dir}/${ARG_NAME}_pve1_prefixed.o)
  endif()

    # --------------------------------------------------------
    # pre-process linker script
    # --------------------------------------------------------
    set(linker_script_preprocessed ${target_temp_dir}/link.ld)
    add_custom_command(
      OUTPUT ${linker_script_preprocessed}
      COMMAND ${CMAKE_C_COMPILER} -E -P -x c -I ${COMMON_DIR}/include ${BUILD_FLAGS}
        ${LINKER_SCRIPT} -o ${linker_script_preprocessed}
      DEPENDS ${LINKER_SCRIPT}
    )
    add_custom_target(${ARG_NAME}_linker_script DEPENDS ${linker_script_preprocessed})

    # --------------------------------------------------------
    # final executable
    # --------------------------------------------------------
    # add target
    add_executable(${ARG_NAME} ${prefixed_objs})
    # set linker language as it cannot be automatically inferred
    set_target_properties(${ARG_NAME} PROPERTIES LINKER_LANGUAGE C)
    # change output directory
    set_target_properties(${ARG_NAME} PROPERTIES RUNTIME_OUTPUT_DIRECTORY ${target_test_dir})
    # link options/libraries
    target_link_options(${ARG_NAME} PRIVATE ${COMMON_LINK_OPTIONS} -T ${linker_script_preprocessed})
    # add linker script as dependency
    set_target_properties(${ARG_NAME} PROPERTIES LINK_DEPENDS ${ARG_NAME}_linker_script)

    # --------------------------------------------------------
    # post-build hooks
    # --------------------------------------------------------
    # Disassemble binary
    # The awk(1) command removes all symbols labels of the form <aicore0_> or
    # <aicore0_.Lpcrel_hi0> (or similar), as well as the preceding newline.
    # These would not be displayed at all if it weren't for the prefixing.
    # This cleans up the disassembly considerably.
    add_custom_command(TARGET ${ARG_NAME} POST_BUILD
      WORKING_DIRECTORY ${target_test_dir}
      COMMAND ${CMAKE_OBJDUMP} -d ${ARG_NAME}
        | awk "BEGIN {RS=\"\\0\"\} {gsub(/\\n\\n[0-9a-f]+ <(aicore[0-7]|pve0|pve1)_(\\.[^\\n]*)?>:/, \"\"); print }"
        > ${ARG_NAME}.S
      VERBATIM
      BYPRODUCTS ${target_test_dir}/${ARG_NAME}.S
    )

  endif()

  # Remove test directory when cleaning
  set_property(TARGET ${ARG_NAME}
    APPEND PROPERTY ADDITIONAL_CLEAN_FILES ${ARG_NAME}
  )

  # --------------------------------------------------------
  # run script and CTest integration
  # --------------------------------------------------------
  verifsdk_register_test(
    NAME ${ARG_NAME}
    RUN_SCRIPT "${CMAKE_SOURCE_DIR}/scripts/run/${ARG_RUN_SCRIPT}"
    RUN_ARGS ${RUN_FLAGS}
    SEEDS ${ARG_SEEDS}
  )
  # make the main target depend on the run script target
  add_dependencies(${ARG_NAME} ${ARG_NAME}_run_script)
endmacro()
