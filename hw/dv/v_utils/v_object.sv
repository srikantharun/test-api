// (C) Copyright Axelera AI 2023
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description:  Generic verification object. 
//   Can be used as the object to transmit using uvm_event.
// Owner: Raymond Garcia <raymond.garcia@axelera.ai>

class v_object extends uvm_object;
    `uvm_object_utils(v_object)

    int                 m_int;
    int unsigned        m_uint;
    string              m_string;
    time                m_time;
    realtime            m_real_time;
    real                m_real;
    bit          [31:0] m_32bit_data;
    bit          [63:0] m_64bit_data;
    bit         [511:0] m_512bit_data;

    int                 m_int_arr[];
    int unsigned        m_uint_arr[];
    string              m_string_arr[];
    time                m_time_arr[];
    realtime            m_real_time_arr[];
    real                m_real_arr[];
    bit          [31:0] m_32bit_data_arr[];
    bit          [63:0] m_64bit_data_arr[];
    bit         [511:0] m_512bit_data_arr[];

    int                 m_int_q[$];
    int unsigned        m_uint_q[$];
    string              m_string_q[$];
    time                m_time_q[$];
    realtime            m_real_time_q[$];
    real                m_real_q[$];
    bit          [31:0] m_32bit_data_q[$];
    bit          [63:0] m_64bit_data_q[$];
    bit         [511:0] m_512bit_data_q[$];

    int                 m_int_arr_int[int];
    int unsigned        m_uint_arr_int[int];
    string              m_string_arr_int[int];
    time                m_time_arr_int[int];
    realtime            m_real_time_arr_int[int];
    real                m_real_arr_int[int];
    bit          [31:0] m_32bit_data_arr_int[int];
    bit          [63:0] m_64bit_data_arr_int[int];
    bit         [511:0] m_512bit_data_arr_int[int];

    int                 m_int_arr_string[string];
    int unsigned        m_uint_arr_string[string];
    string              m_string_arr_string[string];
    time                m_time_arr_string[string];
    realtime            m_real_time_arr_string[string];
    real                m_real_arr_string[string];
    bit          [31:0] m_32bit_data_arr_string[string];
    bit          [63:0] m_64bit_data_arr_string[string];
    bit         [511:0] m_512bit_data_arr_string[string];

    function new(string name = "v_object");
        super.new(name);
    endfunction: new
endclass
