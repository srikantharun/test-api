#!/bin/bash

# Check if the test list YAML file is provided as an argument
if [ "$#" -ne 1 ]; then
    echo "Usage: $0 <testlist_yaml_file>"
    exit 1
fi

TESTLIST_YAML_FILE=$1

# Check if the test list YAML file exists
if [ ! -f "${CVA6_VERIF_HOME}/tests/$TESTLIST_YAML_FILE.yaml" ]; then
    echo "Error: File '${CVA6_VERIF_HOME}/tests/$TESTLIST_YAML_FILE.yaml' not found!"
    exit 1
fi


# Extract test names from the YAML file without trailing comments
TESTS=$(grep -oP '(?<=- test: )[^#]+' "${CVA6_VERIF_HOME}/tests/$TESTLIST_YAML_FILE.yaml" | sed 's/[[:space:]]*$//')

# Convert the TESTS variable to an array
IFS=$'\n' read -rd '' -a TEST_ARRAY <<<"$TESTS"

# Initialize result arrays
declare -A RESULTS
FAILED_TESTS=()
ERROR_MESSAGES=()

# Function to display summary
function display_summary {
    echo
    echo "========================================="
    echo "                SUMMARY                  "
    echo "========================================="
    for TEST in "${!RESULTS[@]}"; do
        echo "$TEST: ${RESULTS[$TEST]}"
    done
    if [ "${#FAILED_TESTS[@]}" -ne 0 ]; then
        echo
        echo "========================================="
        echo "              FAILED TESTS               "
        echo "========================================="
        for i in "${!FAILED_TESTS[@]}"; do
            echo "${FAILED_TESTS[$i]}"
            echo "Error Message: ${ERROR_MESSAGES[$i]}"
        done
    fi
    echo
    echo "========================================="
    echo "              SUMMARY TABLE              "
    echo "========================================="
    echo -e "Total Passed: $(( ${#TEST_ARRAY[@]} - ${#FAILED_TESTS[@]} ))"
    echo -e "Total Failed: ${#FAILED_TESTS[@]}"
}

# Compile once
make compile_vsim COVERAGE=1

# Function to run a single test
run_test() {
    local TEST=$1
    if make run_vsim TESTNAME="$TESTLIST_YAML_FILE.$TEST" NODEPS=1 COVERAGE=1 > /dev/null 2>&1; then
        RESULTS[$TEST]="PASSED"
    else
        RESULTS[$TEST]="FAILED"
        FAILED_TESTS+=("$TEST")
        ERROR_MESSAGES+=("$(make run_vsim TESTNAME="$TESTLIST_YAML_FILE.$TEST" NODEPS=1 COVERAGE=1 2>&1)")
    fi
    echo "Completed test: $TEST (${RESULTS[$TEST]})"
}

# Run tests using background jobs
for TEST in "${TEST_ARRAY[@]}"; do
    run_test "$TEST" &
done

# Wait for all background jobs to finish
wait

# Display the summary
display_summary
echo "All tests completed."
