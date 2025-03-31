#!/usr/bin/env bash

# Use getopts for key-value arguments
while getopts "r:p:f:o:" opt; do
  case $opt in
    r) release_version="$OPTARG" ;;
    p) package_name="$OPTARG" ;;
    f) file_name="$OPTARG" ;;
    o) output_dir="$OPTARG" ;;
    \?) echo "Invalid option -$OPTARG" ;;
  esac
done

# Set the default values for unset variables
package_name=${package_name:-"stimuli"}
file_name=${file_name:-"stimuli_europa_drv_fiat_functional.tar.gz"}
output_dir=${output_dir:-"."}

# Check if release version is set
if [[ -z "$release_version" ]]; then
  echo "Please provide a release version with the -r flag."
  exit 1
fi

# Error if Gitlab API token is not set
if [[ -z "${GITLAB_API_TOKEN}" ]]; then
  echo "Please set the environment variable GITLAB_API_TOKEN to your GitLab API token."
  exit 1
fi

echo "Downloading and extracting '$file_name' from '$package_name' package (version '$release_version')..."

# Move to output directory
mkdir --parents $output_dir
cd $output_dir

# Retries a command a configurable number of times with backoff.
#
# The retry count is given by ATTEMPTS (default 5), the initial backoff
# timeout is given by TIMEOUT in seconds (default 1.)
#
# Successive backoffs double the timeout.
function with_backoff {
  local max_attempts=${ATTEMPTS:-5}
  local timeout=${TIMEOUT:-1}
  local attempt=1
  local exitCode=0

  while (( $attempt < $max_attempts ))
  do
    if "$@"
    then
      return 0
    else
      exitCode=$?
    fi

    echo "Failure! Retrying in ${timeout}s.." 1>&2
    sleep $timeout
    attempt=$(( attempt + 1 ))
    timeout=$(( timeout * 2 ))
  done

  if [[ $exitCode != 0 ]]
  then
    echo "You've failed me for the last time! ($@)" 1>&2
  fi

  return $exitCode
}

# Download the stimuli, retry 5 times and exit on failure
if ! with_backoff curl \
  --header "PRIVATE-TOKEN: $GITLAB_API_TOKEN" \
  "https://git.axelera.ai/api/v4/projects/38/packages/generic/$package_name/$release_version/$file_name" \
  -O;
then
  echo "Failed to download stimuli!" >&2
  exit 1
fi

if file $file_name | grep -q 'gzip compressed data';
then
  if ! tar -xzf $file_name --strip-components=1;
  then
    echo "Failed to extract stimuli!" >&2
    exit 1
  fi
fi

echo "Stimuli downloaded to $output_dir"
