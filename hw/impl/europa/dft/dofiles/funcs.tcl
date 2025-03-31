proc num2bin {num width} {
    binary scan [binary format "I" $num] "B*" binval
    return [string range $binval end-$width end]
}
proc bin2hex {bin} {
    set result ""
    set prepend [string repeat 0 [expr (4-[string length $bin]%4)%4]]
    foreach g [regexp -all -inline {[01]{4}} $prepend$bin] {
        foreach {b3 b2 b1 b0} [split $g ""] {
            append result [format %X [expr {$b3*8+$b2*4+$b1*2+$b0}]]
        }
    }
    return $result
}
proc ax_revnum { val {width 21}} {
    set num [num2bin $val [expr $width - 1]]
#    puts $num
    set rnum [string reverse $num]
 #   puts $rnum
    set ret "0x[bin2hex $rnum]"
 #   puts $ret
    return $ret
}

#ax_revfields 0x4a7c1  [list 3 3 9 6] ; # the order of the list is the input CSR order
proc ax_revfields { val {fields [list]} } {
    set width 0
    foreach field $fields {
    incr width $field
    }
    set num [num2bin $val [expr $width - 1]]
 #   puts "$num"
    set ret ""
    foreach field $fields {
    set tmp [string range $num 0 [expr $field -1]]
    set ret "${tmp}${ret}"
    set num [string range $num $field end]
    #puts "DEBUG $field $tmp $ret $num"
    }
   # puts "final $ret"
    return "0x[bin2hex $ret]"
}


#A function that outputs all the iProcs that have been read into the session.
# useful to be sure what is read into a particular run
proc ax_report_iprocs { module }  {
    puts "iProcsForModule $module"
    foreach iproc [get_iproc_list -of_module $module ] {
    set arglist ""
    foreach arg [get_iproc_argument_list $iproc -of_module $module] {
        if {![get_iproc_argument_default $iproc $arg -exist]} {
        append arglist "$arg "
        } else {
        append arglist "{$arg [get_iproc_argument_default $iproc $arg]} "
        }
    }
    if [get_iproc_option $iproc -is_top_iproc -of_module $module] {
        set func "iTopProc"
    } else {
        set func "iProc"
    }
    puts "##[get_iproc_option $iproc -file_path_name -of_module $module]"
    puts "$func $iproc { ${arglist}} {"
    puts "[get_iproc_body  $iproc -of_module $module]"
    puts "}"
    puts ""
    }
}

proc ax_redirect {filename cmd} {
    rename puts ::tcl::orig::puts

    catch {
    set mode w
    set destination [open $filename $mode]

    proc puts args "
            uplevel \"::tcl::orig::puts $destination \$args\"; return
        "

    uplevel $cmd

    close $destination
    }

    rename puts {}
    rename ::tcl::orig::puts puts
}



global _ax_stopwatch_time

proc ax_current_time_str {} {
    return "[clock format [clock add [clock seconds] 60 minutes] -format %T] (GMT)"
}

proc ax_start_stopwatch {} {
    global _ax_stopwatch_time
    set _ax_stopwatch_time  [clock clicks -milliseconds]
    puts "Started stopwatch at [ax_current_time_str]"
}

proc ax_stop_stopwatch {} {
    global _ax_stopwatch_time
    set timestop [clock clicks -milliseconds]
    set timediff [expr {($timestop - $_ax_stopwatch_time)*0.001}]
    set timediff [format "%.3f" $timediff]
    puts "Started stopwatch at [ax_current_time_str]  after $timediff"
}
proc ax_time_cmd {cmd} {
    puts "Comand started at [ax_current_time_str]"
    set start [clock clicks -milliseconds]
    eval $cmd
    set end [clock clicks -milliseconds]
    set runtime [expr $end - $start]
    set seconds [expr $runtime / 1000]
    set cpu_ms [expr $runtime % 1000]
    set cpu_secs [expr { int(floor($seconds)) % 60 }]
    set cpu_mins [expr { int(floor($seconds / 60)) % 60 }]
    set cpu_hrs  [expr { int(floor($seconds / 3600)) }]
    puts [format "Command completed in %d:%02d:%02d.%-03d" $cpu_hrs $cpu_mins $cpu_secs $cpu_ms]
}


proc create_waves_from_scan_cell_rpt { args} {
    define_proc_attributes create_waves_from_scan_cell_rpt \
    -info "" \
    -define_args {
        { -chain "" "" string required}
        { -tb_prefix "" "triton_pcie_p_retarget_transition__full_ser_v_ctl.triton_inst.i_aipu_i_pcie_p" string optional}
        { -hier_delimiter "" "." string optional}
        { -scan_pin "" "SI" string optional}
    }

    parse_proc_arguments -args $args results
    if { [info exists results(-chain)] } {
        set chain $results(-chain)
    }
    if { [info exists results(-tb_prefix)] } {
        set tb_prefix $results(-tb_prefix)
    } else {
        set tb_prefix "triton_pcie_p_retarget_transition__full_ser_v_ctl.triton_inst.i_aipu_i_pcie_p"
    }
    if { [info exists results(-hier_delimiter)] } {
        set hier_delimiter $results(-hier_delimiter)
    } else {
        set hier_delimiter "."
    }
    if { [info exists results(-scan_pin)] } {
        set scan_pin $results(-scan_pin)
    } else {
        set scan_pin "SI"
    }
    redirect -file ./scan_chain.rpt_tmp {report_scan_cell $chain}
    set fileID [ open ./scan_chain.rpt_tmp r+ 0777]
    set EOFile 0
    echo "" > chain_wave.tcl
    while {$EOFile != 1} {
        gets $fileID line
        if { $chain == [lindex $line 1]} {
            set path [regsub -all "/" [lindex $line 3] "$hier_delimiter"]
            echo "add_wave ${tb_prefix}${hier_delimiter}${path}${hier_delimiter}${scan_pin}" >> chain_wave.tcl
        }
        set EOFile [eof $fileID]
    }; #end while eof
    close $fileID
}
