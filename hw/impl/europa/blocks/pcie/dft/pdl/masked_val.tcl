proc hex_to_bin {hex_value} {
    set decimal_value [expr $hex_value]
    set bin_value ""
    while {$decimal_value > 0} {
        set remainder [expr $decimal_value % 2]
        set bin_value "$remainder$bin_value"
        set decimal_value [expr $decimal_value / 2]
    }
    if {$bin_value == ""} {
        return "0"
    }
    return $bin_value
}

proc masked_val {data_hex mask_hex {max_length 16}} {
    # Convert hex to binary strings
    set data_bin [hex_to_bin $data_hex]
    set mask_bin [hex_to_bin $mask_hex]

    # Pad the binary strings so they have the same length
    set data_bin [format "%0*s" $max_length $data_bin]
    set mask_bin [format "%0*s" $max_length $mask_bin]

    # Initialize result
    set result ""

    # Process each bit in the mask
    for {set i 0} {$i < $max_length} {incr i} {
        set mask_bit [string index $mask_bin $i]
        if {$mask_bit == "1"} {
            # Use corresponding bit from data if mask bit is 1
            append result [string index $data_bin $i]
        } else {
            # Replace with 'x' if mask bit is 0
            append result "x"
        }
    }

    # Print the resulting binary string
    return $result
}
