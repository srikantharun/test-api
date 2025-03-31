#!/usr/bin/tclsh
# =============================================================================
# Coverage Merge and Report Generation Script (Parallel Merge + Fallback)
# =============================================================================
#
# DESCRIPTION:
#   This script attempts a parallel merge of multiple ModelSim/Questasim
#   coverage database (UCDB) files using vcover parallelmerge. If it fails,
#   it falls back to a serial merge (vcover merge). Then, it generates
#   HTML and text coverage reports.
#
# REQUIREMENTS:
#   - ModelSim/Questasim installation with vcover utility in PATH
#   - TCL interpreter (version 8.5 or higher recommended)
#   - Environment variable REPO_ROOT must be set to the root of your repository
#   - X11 forwarding enabled if planning to use GUI visualization
#
# USAGE:
#   1. Set the REPO_ROOT environment variable:
#      export REPO_ROOT=/path/to/your/repo
#
#   2. Run the script with the path to your build_vsim_* directory:
#      tclsh merge_coverage.tcl /full/path/to/build_vsim_spike
#
#   3. Output will be created in ./merged_coverage/ directory:
#      - merged.ucdb                : Merged coverage database
#      - html_report_<timestamp>    : HTML coverage report
#      - text_report_<timestamp>.txt: Text coverage report
#
# NOTE:
#   If you have multiple 'run_vsim_*' subdirectories under your build_vsim_*
#   folder, coverage.ucdb files from each of them will be merged.
#
# =============================================================================

# -----------------------------------------------------------------------------
# Detect full paths of vcover and vsim
# -----------------------------------------------------------------------------
proc init_questasim_executables {} {
    # Attempt to find the full path to vcover
    if {[catch {set ::vcover_exe [exec which vcover]} err]} {
        puts "Error: Could not locate 'vcover' in your PATH."
        exit 1
    }
    # Attempt to find the full path to vsim
    if {[catch {set ::vsim_exe [exec which vsim]} err]} {
        puts "Error: Could not locate 'vsim' in your PATH."
        exit 1
    }
}

# -----------------------------------------------------------------------------
# Procedure: generate_reports
# -----------------------------------------------------------------------------
# Generates HTML and text reports from the merged coverage data
# -----------------------------------------------------------------------------
proc generate_reports {merged_file} {
    # Generate timestamp for unique report names
    set timestamp [clock format [clock seconds] -format "%Y%m%d_%H%M%S"]
    
    # Generate HTML report
    puts "\nGenerating HTML report..."
    if {[catch {
        exec $::vcover_exe report -html -output merged_coverage/html_report_${timestamp} $merged_file
    } result]} {
        puts "Warning: Error generating HTML report: $result"
    } else {
        puts "HTML report generated: merged_coverage/html_report_${timestamp}/index.html"
    }
    
    # Generate text report
    puts "\nGenerating text report..."
    if {[catch {
        exec $::vcover_exe report -output merged_coverage/text_report_${timestamp}.txt $merged_file
    } result]} {
        puts "Warning: Error generating text report: $result"
    } else {
        puts "Text report generated: merged_coverage/text_report_${timestamp}.txt"
    }
}

# -----------------------------------------------------------------------------
# Procedure: print_visualization_commands
# -----------------------------------------------------------------------------
# Prints commands for visualizing coverage data in vsim GUI or HTML
# -----------------------------------------------------------------------------
proc print_visualization_commands {merged_file} {
    puts "\n=== Commands to view coverage ==="
    puts "To open with vsim GUI:"
    puts "$::vsim_exe -viewcov [file normalize $merged_file]"
    
    puts "\nTo open with vsim GUI using srun (recommended for large files):"
    puts "srun --x11 --mem=64G -c 2 $::vsim_exe -viewcov [file normalize $merged_file]"
    
    puts "\nHTML report can be viewed by opening:"
    puts "[file normalize merged_coverage/html_report_*/index.html]"
}

# -----------------------------------------------------------------------------
# Procedure: parallel_merge_coverage
# -----------------------------------------------------------------------------
# Tries a parallel merge using vcover parallelmerge. If it fails, the calling
# procedure can decide whether to fallback to serial merge.
# -----------------------------------------------------------------------------
proc parallel_merge_coverage {coverage_files merged_file} {
    # We must pass coverage files to parallelmerge either via -filelist
    # or by generating them automatically with -genlist. Below we show
    # how to create a file list manually:
    set file_list "merged_coverage/coverage_list.txt"
    
    # Write coverage files to a text file
    set f [open $file_list "w"]
    foreach cf $coverage_files {
        puts $f $cf
    }
    close $f
    
    # Construct parallelmerge command
    set parallel_cmd [list $::vcover_exe "parallelmerge" \
        "-covmode" "ucdb" \
        "-filelist" $file_list \
        "-outname" $merged_file \
        "-mergetype" "totals" \
        "-j" 8 \
        "-runmode" "local"
    ]
    
    # For more verbose output, you could add: "-verbose"
    # lappend parallel_cmd "-verbose"
    
    puts "\nAttempting parallel merge with command:"
    puts "  [join $parallel_cmd { }]\n"
    
    if {[catch {eval exec $parallel_cmd} result]} {
        puts "Parallel merge failed with error:"
        puts "$result"
        return 1  ;# Return non-zero for failure
    }
    
    # If we reach here, parallel merge succeeded
    return 0
}

# -----------------------------------------------------------------------------
# Procedure: serial_merge_coverage
# -----------------------------------------------------------------------------
# Performs a "classic" serial merge using vcover merge
# -----------------------------------------------------------------------------
proc serial_merge_coverage {coverage_files merged_file} {
    puts "\nAttempting fallback to serial merge..."
    set merge_cmd "$::vcover_exe merge $merged_file"
    foreach cf $coverage_files {
        append merge_cmd " $cf"
    }
    
    puts "\nExecuting serial merge command:"
    puts "  $merge_cmd\n"
    
    if {[catch {eval exec $merge_cmd} result]} {
        puts "Error merging coverage files (serial fallback also failed):"
        puts "$result"
        exit 1
    }
}

# -----------------------------------------------------------------------------
# Procedure: merge_coverage
# -----------------------------------------------------------------------------
# Main procedure: Finds UCDB files, attempts parallel merge, falls back to
# serial merge if parallel fails, then generates coverage reports.
# -----------------------------------------------------------------------------
proc merge_coverage {} {
    # First, detect the full paths to vcover and vsim
    init_questasim_executables

    # Check argument count
    if {$::argc != 1} {
        puts "Error: You must provide the path to a build_vsim_* directory."
        puts "Example usage: tclsh merge_coverage.tcl /full/path/to/build_vsim_spike"
        exit 1
    }
    set build_vsim_dir [lindex $::argv 0]
    
    # Verify that the provided argument is a directory
    if {![file isdirectory $build_vsim_dir]} {
        puts "Error: '$build_vsim_dir' is not a valid directory."
        puts "Please provide the path to a valid build_vsim_* directory."
        exit 1
    }

    # Verify environment setup
    if {![info exists ::env(REPO_ROOT)]} {
        puts "Error: REPO_ROOT environment variable is not set."
        puts "Please set it with: export REPO_ROOT=/path/to/your/repo"
        exit 1
    }

    # Create output directory
    if {![file exists "merged_coverage"]} {
        file mkdir "merged_coverage"
    }
    
    # Find all coverage files under the given build_vsim directory
    # We assume coverage is in run_vsim*/coverage.ucdb
    set coverage_files [glob -nocomplain [file join $build_vsim_dir "run_vsim*/coverage.ucdb"]]
    
    if {[llength $coverage_files] == 0} {
        puts "Error: No coverage.ucdb files found in:"
        puts "       $build_vsim_dir/run_vsim*/coverage.ucdb"
        puts "Please ensure that the runs generated coverage files."
        exit 1
    }
    
    # Summarize
    set total_files [llength $coverage_files]
    puts "\nFound $total_files coverage files to merge:"
    foreach cf $coverage_files {
        puts "  $cf"
    }
    
    set merged_file "merged_coverage/merged.ucdb"
    
    # Try parallel merge first
    set rc [parallel_merge_coverage $coverage_files $merged_file]
    
    # If parallel merge fails, fallback to serial
    if {$rc != 0} {
        serial_merge_coverage $coverage_files $merged_file
    }
    
    # Generate reports and print commands
    generate_reports $merged_file
    print_visualization_commands $merged_file
    
    # Print summary
    puts "\n=== Merge Summary ==="
    puts "Total files merged: $total_files"
    puts "Merged UCDB: [file normalize $merged_file]"
}

# -----------------------------------------------------------------------------
# Execute the merge procedure
# -----------------------------------------------------------------------------
merge_coverage
