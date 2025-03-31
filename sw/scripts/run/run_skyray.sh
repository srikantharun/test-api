#!/bin/bash

# The first argument is the TEST_BINARY
TEST_BINARY=$1
shift 1

if [ -z "$TEST_BINARY" ]; then
  echo "Usage: $0 TEST_BINARY"
  exit 1
fi


# Execute the spike command with the given test name
skyray $@ run "${TEST_BINARY}"
