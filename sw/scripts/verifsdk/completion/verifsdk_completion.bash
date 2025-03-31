#!/usr/bin/env bash

COMPLETION_HELPER_PATH=$REPO_ROOT/bin/verifsdk-completer

_verifsdk_complete() {
  COMPREPLY=()
  local opts=( "-GNinja" "-GMake" "-P"  "--platform" "-L" "--label" "-F" "--flavors"
    "-C" "--directory" "--no-cmake" "--no-ninja" "-I" "--input" "-v" "-V" "--verbose"
    "--jtag" "-R" "--regex" "--no-optimize" "--verify-yaml" "--list" "--ctest" )

  local curr="${COMP_WORDS[COMP_CWORD]}"
  local prev="${COMP_WORDS[COMP_CWORD-1]}"

  # Check if the current word should be paired with the previous arg
  case "${prev}" in 
    -P|--platform)
      COMPREPLY=( $(compgen -W "$($COMPLETION_HELPER_PATH --print-platforms)" -- "$curr") )
      ;;

    -L|--label)
      COMPREPLY=( $(compgen -W "$($COMPLETION_HELPER_PATH --print-labels)" -- "$curr") )
      ;;

    -F|--flavors)
      COMPREPLY=( $(compgen -W "$($COMPLETION_HELPER_PATH --print-flavors)" -- "$curr") )
      ;;

    --only)
      local platform=""
      local label=""
      local i=""
      local j=""
      for i in ${COMP_WORDS[@]}; do
        case "${j}" in
          -P)
            platform="-p $i"
            ;;
          -L)
            label="-l $i"
        esac
        j="$i"
      done
      COMPREPLY=( $(compgen -W "$($COMPLETION_HELPER_PATH --print-tests $platform $label)" -- "$curr") )
      ;;

    # Leave completion to bash
    -I|--input|-C|--directory|-R|--regex)
      ;;

    *)
      COMPREPLY=( $(compgen -W "${opts[*]}" -- "$curr") )
      ;;
  esac

  return 0
}

complete -F _verifsdk_complete -o bashdefault -o default verifsdk
