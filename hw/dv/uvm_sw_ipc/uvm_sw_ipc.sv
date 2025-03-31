`ifndef UVM_SW_IPC_SV
`define UVM_SW_IPC_SV

class uvm_sw_ipc_msg_shortener extends uvm_report_catcher;
  function new(string name = "uvm_sw_ipc_msg_shortener");
    super.new(name);
  endfunction

  function action_e catch();
    if (get_severity() == UVM_INFO) begin
      string msg = get_message();
      if ((msg.len() >= 4) && (msg.substr(0, 3) == "[sw]")) begin
        uvm_report_info(get_id(), msg, get_verbosity());
        return CAUGHT;
      end
    end
    return THROW;
  endfunction
endclass

class uvm_sw_ipc extends uvm_component;

  `uvm_component_utils(uvm_sw_ipc)

  // see: https://github.com/bminor/newlib/blob/master/libgloss/riscv/machine/syscall.h
  // classic syscalls
  `define SYS_write 64
  `define SYS_exit 93
  // UVM syscalls
  `define SYS_uvm_print 32
  `define SYS_uvm_gen_event 33
  `define SYS_uvm_wait_event 34
  `define SYS_uvm_quit 35
  `define SYS_uvm_rand 36
  `define SYS_uvm_hdl_deposit 37
  `define SYS_uvm_hdl_force 38
  `define SYS_uvm_hdl_release 39
  `define SYS_uvm_hdl_read 40
  `define SYS_uvm_memcmp 41
  `define SYS_uvm_memcpy 42
  `define SYS_uvm_memset 43
  `define SYS_uvm_udelay 44

  `define UVM_LOG_LEVEL_INFO     0
  `define UVM_LOG_LEVEL_WARNING  1
  `define UVM_LOG_LEVEL_ERROR    2
  `define UVM_LOG_LEVEL_FATAL    3
  `define UVM_PRINTF             4

  // ___________________________________________________________________________________________
  //             C-side                              |              UVM-side
  // ________________________________________________|__________________________________________
  // ...                                             |      uvm_sw_ipc_wait_event(0) waits
  // uvm_sw_ipc_gen_event(0)                      ---|-->   uvm_sw_ipc_wait_event(0) returns
  //                                                 |
  // uvm_sw_ipc_wait_event(16) waits                 |      ...
  // uvm_sw_ipc_wait_event(16) returns            <--|---   uvm_sw_ipc_gen_event(16)
  //
  // uvm_sw_ipc_push_data(0, 0xdeadbeef)          ---|-->   uvm_sw_ipc_pull_data(0, data)
  //                                                 |
  // uvm_sw_ipc_pull_data(1 , &data)              <--|---   uvm_sw_ipc_push_data(1, data)
  //                                                 |
  // uvm_sw_ipc_print_info(1, "data=0x%0x", data) ---|-->   `uvm_info(...)
  //                                                 |
  // uvm_sw_ipc_quit()                            ---|-->   end of simulation

  // high-level API
  extern function void uvm_sw_ipc_gen_event(int event_idx);
  extern task          uvm_sw_ipc_wait_event(int event_idx);
  extern function void uvm_sw_ipc_push_data(input int fifo_idx, input [63:0] data);
  extern function bit  uvm_sw_ipc_pull_data(input int fifo_idx, output [63:0] data);

  uvm_tlm_analysis_fifo#(uvm_sw_ipc_tx) monitor_fifo;
  uvm_event                             event_to_uvm[UVM_SW_IPC_EVENT_NB];
  uvm_event                             event_to_sw[UVM_SW_IPC_EVENT_NB];
  bit [63:0]                            fifo_data_to_uvm[UVM_SW_IPC_FIFO_NB][$];
  bit [63:0]                            fifo_data_to_sw[UVM_SW_IPC_FIFO_NB][$];

  uvm_sw_ipc_config       m_config;
  uvm_sw_ipc_monitor      m_monitor;
  uvm_sw_ipc_msg_shortener m_shortener;
  virtual uvm_sw_ipc_if   vif;

  bit                     m_quit = 0;
  bit [63:0]              m_prev_fifo_data_to_sw_empty = {64{1'b1}};
  string                  m_printf_str;

  extern function new(string name, uvm_component parent);

  extern function void build_phase(uvm_phase phase);
  extern function void connect_phase(uvm_phase phase);
  extern task main_phase(uvm_phase phase);
  extern function void check_phase(uvm_phase phase);

  extern task process_ram_access();
  extern task process_cmd(uvm_sw_ipc_tx tx);
  extern function void process_cmd_print(int severity);
  extern function void process_cmd_gen_event(int event_idx);
  extern task process_cmd_wait_event(int event_idx);
  extern function void process_cmd_hdl_deposit();
  extern function void process_cmd_hdl_force();
  extern function void process_cmd_hdl_release();
  extern function void process_cmd_hdl_read();
  extern function void process_cmd_quit();
  extern function void process_cmd_rand();
  extern function void process_cmd_memcmp();
  extern function void process_cmd_memcpy();
  extern function void process_cmd_memset();
  extern task process_cmd_udelay(integer unsigned udelay);
  extern function void process_fifo_data_to_uvm(uvm_sw_ipc_tx tx, int fifo_idx);
  extern function void process_fifo_data_to_sw(uvm_sw_ipc_tx tx, int fifo_idx);
  extern task update_data_to_sw();
  extern function void check_max_event_idx(int event_idx);

  extern function string str_replace(string str, string pattern, string replacement);
  extern function string str_format(string str, ref bit [63:0] q[$]);
endclass : uvm_sw_ipc


function  uvm_sw_ipc::new(string name, uvm_component parent);
  super.new(name, parent);
  m_printf_str = "";
  monitor_fifo = new("monitor_fifo", this);
  foreach (event_to_uvm[i]) begin
    event_to_uvm[i] = new($sformatf("event_to_uvm_%d", i));
    event_to_sw[i] = new($sformatf("event_to_sw_%d", i));
  end
endfunction : new


function void uvm_sw_ipc::build_phase(uvm_phase phase);
  uvm_table_printer tprinter = new();

  if (!uvm_config_db#(uvm_sw_ipc_config)::get(this, "", "config", m_config))
    `uvm_error(get_type_name(), "uvm_sw_ipc config not found")
  else
    `uvm_info(get_type_name(), $sformatf("uvm_sw_ipc_config:\n%s", m_config.sprint(tprinter)),
              UVM_LOW)

  m_monitor = uvm_sw_ipc_monitor::type_id::create("m_monitor", this);

  m_shortener = new();
  uvm_report_cb::add(this, m_shortener);
endfunction : build_phase


function void uvm_sw_ipc::connect_phase(uvm_phase phase);
  if (m_config.vif == null)
    `uvm_warning(get_type_name(), "uvm_sw_ipc virtual interface is not set!")

  vif                = m_config.vif;
  m_monitor.vif      = m_config.vif;
  m_monitor.m_config = m_config;
  m_monitor.analysis_port.connect(monitor_fifo.analysis_export);
endfunction : connect_phase


function void uvm_sw_ipc::uvm_sw_ipc_gen_event(int event_idx);
  check_max_event_idx(event_idx);
  event_to_sw[event_idx].trigger();
endfunction : uvm_sw_ipc_gen_event


task uvm_sw_ipc::uvm_sw_ipc_wait_event(int event_idx);
  check_max_event_idx(event_idx);
  event_to_uvm[event_idx].wait_on();
  event_to_uvm[event_idx].reset();
endtask : uvm_sw_ipc_wait_event


function void uvm_sw_ipc::uvm_sw_ipc_push_data(input int fifo_idx, input [63:0] data);
  fifo_data_to_sw[fifo_idx].push_back(data);
endfunction : uvm_sw_ipc_push_data


function bit uvm_sw_ipc::uvm_sw_ipc_pull_data(input int fifo_idx, output [63:0] data);
  if (fifo_data_to_uvm[fifo_idx].size() == 0) begin
    return 0;
  end
  data = fifo_data_to_uvm[fifo_idx].pop_front();
  return 1;
endfunction : uvm_sw_ipc_pull_data


task uvm_sw_ipc::main_phase(uvm_phase phase);
  if (m_config.handle_end_of_test) begin
    phase.raise_objection(this);
  end
  vif.backdoor_write(m_config.fifo_data_to_sw_empty_address, {64{1'b1}});
  fork
    update_data_to_sw();
    process_ram_access();
    wait(m_quit);
  join_any
  if (m_config.handle_end_of_test) begin
    phase.drop_objection(this);
  end
endtask : main_phase


task uvm_sw_ipc::process_ram_access();
    forever begin
      uvm_sw_ipc_tx tx;
      monitor_fifo.get(tx);
      if (tx.addr >= m_config.start_address && tx.addr < m_config.end_address) begin
        `uvm_info(get_type_name(), {"received new packet from monitor: ", tx.sprint()}, UVM_DEBUG)
      end
      // command
      if (tx.addr == m_config.cmd_address) begin
        fork
          process_cmd(tx);
        join_none
      end
      // other fifo
      for (int i = 0; i < UVM_SW_IPC_FIFO_NB; i++) begin
        if (tx.addr == m_config.fifo_data_to_uvm_address[i]) begin
          process_fifo_data_to_uvm(tx, i);
        end
        if (tx.addr == m_config.fifo_data_to_sw_address[i]) begin
          process_fifo_data_to_sw(tx, i);
        end
      end
    end
endtask : process_ram_access


task uvm_sw_ipc::process_cmd(uvm_sw_ipc_tx tx);
  if (tx.rwb == uvm_sw_ipc_tx::IPC_WR) begin
    bit [15:0] cmd;
    bit [15:0] cmd_io;
    {cmd_io, cmd} = tx.data;
    `uvm_info(get_type_name(), $sformatf("process_cmd: addr=0x%0x, cmd=0x%0x (%0d)", tx.addr, cmd, cmd), UVM_DEBUG)
    case (cmd)
      // UVM syscalls
      `SYS_uvm_print:       process_cmd_print(.severity(cmd_io));
      `SYS_uvm_gen_event:   process_cmd_gen_event(.event_idx(cmd_io));
      `SYS_uvm_wait_event:  process_cmd_wait_event(.event_idx(cmd_io));
      `SYS_uvm_rand:        process_cmd_rand();
      `SYS_uvm_hdl_deposit: process_cmd_hdl_deposit();
      `SYS_uvm_hdl_force:   process_cmd_hdl_force();
      `SYS_uvm_hdl_release: process_cmd_hdl_release();
      `SYS_uvm_hdl_read:    process_cmd_hdl_read();
      `SYS_uvm_memcmp:      process_cmd_memcmp();
      `SYS_uvm_memcpy:      process_cmd_memcpy();
      `SYS_uvm_memset:      process_cmd_memset();
      `SYS_uvm_udelay:      process_cmd_udelay(.udelay(tx.data[47:16]));
      `SYS_uvm_quit:        process_cmd_quit();
      default: begin
        `uvm_fatal(get_type_name(), $sformatf("cmd=0x%x does not exist", cmd))
      end
    endcase
  end
endtask : process_cmd


function void uvm_sw_ipc::process_cmd_print(int severity);
  bit [63:0] addr;
  string str;
  string str_with_prefix;
  int fifo_cmd_size;
  int printf_last_newline_idx;

  if (fifo_data_to_uvm[UVM_SW_IPC_CMD_ARGS_FIFO_IDX].size() == 0) begin
    `uvm_fatal(get_type_name(), "process_cmd_print: not enough arguments");
  end
  addr = fifo_data_to_uvm[UVM_SW_IPC_CMD_ARGS_FIFO_IDX].pop_front();
  str = str_format(vif.backdoor_get_string(addr), fifo_data_to_uvm[UVM_SW_IPC_FIFO_NB-1]);
  `uvm_info(get_type_name(), $sformatf("print: addr=0x%0x, str=%s", addr, str), UVM_DEBUG)
  str_with_prefix = {"[sw] ", str};
  case (severity)
    `UVM_LOG_LEVEL_INFO:    `uvm_info(get_type_name(), str_with_prefix, UVM_LOW)
    `UVM_LOG_LEVEL_WARNING: `uvm_warning(get_type_name(), str_with_prefix)
    `UVM_LOG_LEVEL_ERROR:   `uvm_error(get_type_name(), str_with_prefix)
    `UVM_LOG_LEVEL_FATAL:   `uvm_fatal(get_type_name(), str_with_prefix)
    `UVM_PRINTF:            m_printf_str = {m_printf_str, str};
    default: begin
      `uvm_fatal(get_type_name(), $sformatf("print severity=%0d is not defined", severity))
    end
  endcase

  // mimic printf() behavior,
  // only call uvm_info when UVM_PRINTF string features a \n
  printf_last_newline_idx= -1;
  foreach (m_printf_str[i]) begin
    if (m_printf_str[i] == "\n") begin
      printf_last_newline_idx = i;
    end
  end
  if (printf_last_newline_idx != -1) begin
    `uvm_info(get_type_name(), {"[sw] ", m_printf_str.substr(0, printf_last_newline_idx-1)}, UVM_LOW);
    m_printf_str = m_printf_str.substr(printf_last_newline_idx+1, m_printf_str.len()-1);
  end

  fifo_cmd_size = fifo_data_to_uvm[UVM_SW_IPC_CMD_ARGS_FIFO_IDX].size();
  if (fifo_cmd_size != 0) begin
    `uvm_fatal(get_type_name(), $sformatf("fifo_cmd_size=%0d at the end of process_cmd_print()", fifo_cmd_size))
  end
endfunction : process_cmd_print


function void uvm_sw_ipc::process_cmd_gen_event(int event_idx);
  `uvm_info(get_type_name(), $sformatf("process_cmd_gen_event(%0d)", event_idx), UVM_DEBUG)
  check_max_event_idx(event_idx);
  event_to_uvm[event_idx].trigger();
endfunction : process_cmd_gen_event


task uvm_sw_ipc::process_cmd_wait_event(int event_idx);
  `uvm_info(get_type_name(), $sformatf("process_cmd_wait_event(%0d) start", event_idx), UVM_DEBUG)
  check_max_event_idx(event_idx);

  event_to_sw[event_idx].wait_on();
  event_to_sw[event_idx].reset();
  fifo_data_to_sw[UVM_SW_IPC_CMD_ARGS_FIFO_IDX].push_back(event_idx);
  `uvm_info(get_type_name(), $sformatf("process_cmd_wait_event(%0d) done", event_idx), UVM_DEBUG)
endtask : process_cmd_wait_event


function void uvm_sw_ipc::process_cmd_hdl_deposit();
  bit [63:0] addr;
  bit [63:0] value;
  string path;
  if (fifo_data_to_uvm[UVM_SW_IPC_CMD_ARGS_FIFO_IDX].size() != 2) begin
    `uvm_fatal(get_type_name(), "process_cmd_hdl_deposit: command queue needs 2 arguments")
  end
  addr = fifo_data_to_uvm[UVM_SW_IPC_CMD_ARGS_FIFO_IDX].pop_front();
  value = fifo_data_to_uvm[UVM_SW_IPC_CMD_ARGS_FIFO_IDX].pop_front();
  path = vif.backdoor_get_string(addr);
  if (!uvm_hdl_deposit(path, value)) begin
    `uvm_fatal(get_type_name(), $sformatf("uvm_hdl_deposit(%0s, 0x%x) failed", path, value))
  end
endfunction : process_cmd_hdl_deposit


function void uvm_sw_ipc::process_cmd_hdl_force();
  bit [63:0] addr;
  bit [63:0] value;
  string path;
  if (fifo_data_to_uvm[UVM_SW_IPC_CMD_ARGS_FIFO_IDX].size() != 2) begin
    `uvm_fatal(get_type_name(), "process_cmd_hdl_force: command queue needs 2 arguments")
  end
  addr = fifo_data_to_uvm[UVM_SW_IPC_CMD_ARGS_FIFO_IDX].pop_front();
  value = fifo_data_to_uvm[UVM_SW_IPC_CMD_ARGS_FIFO_IDX].pop_front();
  path = vif.backdoor_get_string(addr);
  if (!uvm_hdl_force(path, value)) begin
    `uvm_fatal(get_type_name(), $sformatf("uvm_hdl_force(%0s, 0x%x) failed", path, value))
  end
endfunction : process_cmd_hdl_force


function void uvm_sw_ipc::process_cmd_hdl_release();
  bit [63:0] addr;
  string path;
  if (fifo_data_to_uvm[UVM_SW_IPC_CMD_ARGS_FIFO_IDX].size() != 1) begin
    `uvm_fatal(get_type_name(), "process_cmd_hdl_release: command queue needs 1 argument")
  end
  addr = fifo_data_to_uvm[UVM_SW_IPC_CMD_ARGS_FIFO_IDX].pop_front();
  path = vif.backdoor_get_string(addr);
  // VCS uvm_hdl_*() function are implemented with a uvm_fatal() when UVM_NO_DPI is defined,
  // however uvm_hdl_release() signature differs when UVM_NO_DPI is defined (typo, bad copy/paste),
  // which creates a compilation error.
  // Hence this indef UVM_NO_DPI exception for uvm_hdl_release() only
  `ifndef UVM_NO_DPI
    if (!uvm_hdl_release(path)) begin
      `uvm_fatal(get_type_name(), $sformatf("uvm_hdl_release(%0s) failed", path))
    end
  `else
    `uvm_fatal(get_type_name(), "uvm_hdl DPI routines are compiled off. Recompile without +define+UVM_NO_DPI")
  `endif
endfunction : process_cmd_hdl_release


function void uvm_sw_ipc::process_cmd_hdl_read();
  bit [63:0] addr;
  bit [63:0] value;
  string path;
  `uvm_info(get_type_name(), "process_cmd_hdl_read", UVM_DEBUG)
  if (fifo_data_to_uvm[UVM_SW_IPC_CMD_ARGS_FIFO_IDX].size() != 1) begin
    `uvm_fatal(get_type_name(), "process_cmd_hdl_read: command queue needs 1 argument")
  end
  addr = fifo_data_to_uvm[UVM_SW_IPC_CMD_ARGS_FIFO_IDX].pop_front();
  path = vif.backdoor_get_string(addr);
  if (!uvm_hdl_read(path, value)) begin
    `uvm_fatal(get_type_name(), $sformatf("uvm_hdl_read(%0s, value) failed", path))
  end
  `uvm_info(get_type_name(), $sformatf("process_cmd_hdl_read: value is equal to 0x%0x", value), UVM_DEBUG)
  fifo_data_to_sw[UVM_SW_IPC_CMD_ARGS_FIFO_IDX].push_back(value);
endfunction : process_cmd_hdl_read


function void uvm_sw_ipc::process_cmd_quit();
  `uvm_info(get_type_name(), "end of simulation", UVM_LOW)
  m_quit = 1;
endfunction : process_cmd_quit


function void uvm_sw_ipc::process_cmd_rand();
  fifo_data_to_sw[UVM_SW_IPC_CMD_ARGS_FIFO_IDX].push_back({$urandom(), $urandom()});
endfunction : process_cmd_rand

function void uvm_sw_ipc::process_cmd_memcmp();
  bit [63:0] s1, s2, n;
  bit [63:0] data1, data2;
  bit signed [63:0] ret = 0;

  if (fifo_data_to_uvm[UVM_SW_IPC_CMD_ARGS_FIFO_IDX].size() != 3) begin
    `uvm_fatal(get_type_name(), "process_cmd_memcmp: command queue needs 3 arguments")
  end
  s1 = fifo_data_to_uvm[UVM_SW_IPC_CMD_ARGS_FIFO_IDX].pop_front();
  s2 = fifo_data_to_uvm[UVM_SW_IPC_CMD_ARGS_FIFO_IDX].pop_front();
  n  = fifo_data_to_uvm[UVM_SW_IPC_CMD_ARGS_FIFO_IDX].pop_front();

  if ((s1 & 'h7) != 0 || (s2 & 'h7) != 0 || (n & 'h7) != 0) begin
    `uvm_fatal(get_type_name(),
      "process_cmd_memcmp: memcmp() arguments are not sufficiently aligned (8-byte alignment required)")
  end

  while (n > 0) begin
    vif.backdoor_read(s1, data1);
    vif.backdoor_read(s2, data2);
    if (data1 != data2) begin
      // If 64-bit words don't match, compare byte by byte.
      // This is required to return with a positive or negative return code
      // depending on which data is "less than" the other.
      for (int i = 0; i < 8; i++) begin
        bit [7:0] byte1, byte2;
        byte1 = data1[8*i+:8];
        byte2 = data2[8*i+:8];
        if (byte1 < byte2) begin
          ret = -1;
          break;
        end
        if (byte1 > byte2) begin
          ret = 1;
          break;
        end
      end
      break;
    end
    s1 += 8;
    s2 += 8;
    n -= 8;
  end

  fifo_data_to_sw[UVM_SW_IPC_CMD_ARGS_FIFO_IDX].push_back(ret);
endfunction : process_cmd_memcmp

function void uvm_sw_ipc::process_cmd_memcpy();
  bit [63:0] dst, src, n;
  bit [63:0] data;

  if (fifo_data_to_uvm[UVM_SW_IPC_CMD_ARGS_FIFO_IDX].size() != 3) begin
    `uvm_fatal(get_type_name(), "process_cmd_memcpy: command queue needs 3 arguments")
  end
  dst = fifo_data_to_uvm[UVM_SW_IPC_CMD_ARGS_FIFO_IDX].pop_front();
  src = fifo_data_to_uvm[UVM_SW_IPC_CMD_ARGS_FIFO_IDX].pop_front();
  n   = fifo_data_to_uvm[UVM_SW_IPC_CMD_ARGS_FIFO_IDX].pop_front();

  if ((dst & 'h7) != 0 || (src & 'h7) != 0 || (n & 'h7) != 0) begin
    `uvm_fatal(get_type_name(),
      "process_cmd_memcpy: memcpy() arguments are not sufficiently aligned (8-byte alignment required)")
  end

  while (n > 0) begin
    vif.backdoor_read(src, data);
    vif.backdoor_write(dst, data);
    dst += 8;
    src += 8;
    n -= 8;
  end
endfunction : process_cmd_memcpy

function void uvm_sw_ipc::process_cmd_memset();
  bit [63:0] s, n;
  bit [63:0] c;
  bit [63:0] data;


  if (fifo_data_to_uvm[UVM_SW_IPC_CMD_ARGS_FIFO_IDX].size() != 3) begin
    `uvm_fatal(get_type_name(), "process_cmd_memset: command queue needs 3 arguments")
  end
  s = fifo_data_to_uvm[UVM_SW_IPC_CMD_ARGS_FIFO_IDX].pop_front();
  c = fifo_data_to_uvm[UVM_SW_IPC_CMD_ARGS_FIFO_IDX].pop_front();
  n = fifo_data_to_uvm[UVM_SW_IPC_CMD_ARGS_FIFO_IDX].pop_front();

  if ((s & 'h7) != 0 || (n & 'h7) != 0) begin
    `uvm_fatal(get_type_name(),
      "process_cmd_memset: memset() arguments are not sufficiently aligned (8-byte alignment required for s and c)")
  end

  data = {8{c[7:0]}}; // replicate byte `c` 8 times

  while (n > 0) begin
    vif.backdoor_write(s, data);
    s += 8;
    n -= 8;
  end
endfunction : process_cmd_memset


function void uvm_sw_ipc::process_fifo_data_to_uvm(uvm_sw_ipc_tx tx, int fifo_idx);
  `uvm_info(get_type_name(), $sformatf("process_fifo_data_to_uvm(fifo_idx=%0d)", fifo_idx), UVM_DEBUG);
  if (tx.rwb == uvm_sw_ipc_tx::IPC_RD) begin
    `uvm_fatal(get_type_name(), $sformatf("illegal read from SW in fifo_data_to_uvm[%0d]", fifo_idx))
  end
  fifo_data_to_uvm[fifo_idx].push_back(tx.data);
endfunction : process_fifo_data_to_uvm


function void uvm_sw_ipc::process_fifo_data_to_sw(uvm_sw_ipc_tx tx, int fifo_idx);
  `uvm_info(get_type_name(), $sformatf("process_fifo_data_to_sw(fifo_idx=%0d)", fifo_idx), UVM_DEBUG);
  if (tx.rwb == uvm_sw_ipc_tx::IPC_WR) begin
    `uvm_fatal(get_type_name(), $sformatf("illegal write from SW in fifo_data_to_sw[%0d]", fifo_idx))
  end
  if (fifo_data_to_sw[fifo_idx].size() == 0) begin
    `uvm_fatal(get_type_name(), "UVM has no data to transmit to SW")
  end
  void'(fifo_data_to_sw[fifo_idx].pop_front());
endfunction : process_fifo_data_to_sw


task uvm_sw_ipc::process_cmd_udelay(integer unsigned udelay);
  repeat (udelay) #1us;
  fifo_data_to_sw[UVM_SW_IPC_CMD_ARGS_FIFO_IDX].push_back(udelay);
endtask


task uvm_sw_ipc::update_data_to_sw();
  forever begin
    bit [63:0] fifo_data_to_sw_empty;
    @(vif.cb);
    for (int i = 0; i < UVM_SW_IPC_FIFO_NB; i++) begin
      fifo_data_to_sw_empty[i] = 1'b1;
      if (fifo_data_to_sw[i].size() != 0) begin
        `uvm_info(get_type_name(), $sformatf("update_data_to_sw : fifo_data_to_sw[%0d].size=%0d", i, fifo_data_to_sw_empty[i]), UVM_DEBUG);
        fifo_data_to_sw_empty[i] = 1'b0;
        vif.backdoor_write(m_config.fifo_data_to_sw_address[i], fifo_data_to_sw[i][0]);
      end
    end
    if (fifo_data_to_sw_empty != m_prev_fifo_data_to_sw_empty) begin
      `uvm_info(get_type_name(), $sformatf("update_data_to_sw : fifo_data_to_sw_empty=0x%0x and m_prev_fifo_data_to_sw_empty=0x%0x", fifo_data_to_sw_empty, m_prev_fifo_data_to_sw_empty), UVM_DEBUG);
      vif.backdoor_write(m_config.fifo_data_to_sw_empty_address, fifo_data_to_sw_empty);
      m_prev_fifo_data_to_sw_empty = fifo_data_to_sw_empty;
    end
  end
endtask : update_data_to_sw


function void uvm_sw_ipc::check_max_event_idx(int event_idx);
  if (event_idx >= UVM_SW_IPC_EVENT_NB) begin
    `uvm_fatal(get_type_name(), $sformatf("process_cmd_gen/wait_event(%0d): max event_idx is %0d",
      event_idx, UVM_SW_IPC_EVENT_NB-1))
  end
endfunction : check_max_event_idx


function string uvm_sw_ipc::str_replace(string str, string pattern, string replacement);
  string s;
  int p_len;
  s = "";
  p_len = pattern.len();
  foreach (str[i]) begin
    s = {s, str[i]};
    if (s.substr(s.len()-p_len,s.len()-1) == pattern) begin
      s = {s.substr(0, s.len()-p_len-1), replacement};
    end
  end
  return s;
endfunction

class string_formatter;

  typedef enum bit[1:0] {
    NO_FORMAT,
    PARSING_PADDING,
    PARSING_FORMATTER
  } parsing_status_t;

  virtual uvm_sw_ipc_if   vif;
  static string integer_formatters[] = '{"d", "u", "x", "p"};
  static string digits[] = '{"0", "1", "2", "3", "4", "5", "6", "7", "8", "9", "0"};

  string accumulator;
  string formatted_string;
  parsing_status_t status;

  function new();
    accumulator = "";
    formatted_string = "";
    status = NO_FORMAT;
  endfunction

  function void push_to_formatted_string(string str);
    formatted_string = {formatted_string, str};
  endfunction

  function void push_to_accumulator(string str);
    accumulator = {accumulator, str};
  endfunction

    function bit is_digit(string str);
    foreach(digits[i]) begin
      if (str == digits[i]) begin
        return 1;
      end
    end
    return 0;
  endfunction

  function void format_string_accumulator(ref bit[63:0] arg_q[$]);
    bit[63:0] arg = pop_arg(arg_q);
    push_to_formatted_string($sformatf(accumulator, vif.backdoor_get_string(arg)));
    accumulator = "";
  endfunction

  function void format_char_accumulator(ref bit[63:0] arg_q[$]);
    bit[63:0] arg = pop_arg(arg_q);
    push_to_formatted_string($sformatf(accumulator, arg));
    accumulator = "";
  endfunction

  function void format_float_accumulator(ref bit[63:0] arg_q[$]);
    bit[63:0] arg = pop_arg(arg_q);
    push_to_formatted_string($sformatf(accumulator, $bitstoreal(arg)));
    accumulator = "";
  endfunction

  function void format_int_accumulator(ref bit[63:0] arg_q[$]);
    string format_char = string'(accumulator[accumulator.len() -1]);
    foreach (integer_formatters[i]) begin
      if (integer_formatters[i] == format_char) begin
        bit[63:0] arg = pop_arg(arg_q);
        if (format_char == "u") begin
          accumulator[accumulator.len() -1] = "d";
        end else if (format_char == "p") begin
          accumulator[accumulator.len() -1] = "x";
        end

        push_to_formatted_string($sformatf(accumulator, arg));
        accumulator = "";
        return;
      end
    end
    `uvm_fatal("string_formatter", $sformatf("Unsupported formatter: %s", format_char))
  endfunction

  function bit[63:0] pop_arg(ref bit[63:0] arg_q[$]);
    if (arg_q.size() == 0) begin
      `uvm_fatal("string_formatter", "Not enough arguments to format!")
    end
    return arg_q.pop_front();
  endfunction

  function string format_string(input string str, ref bit [63:0] arg_q[$]);
    int i = 0;
    while (i < str.len()) begin
      string char = string'(str[i]);
      case (status)
        NO_FORMAT: begin
          if (str[i] == "%") begin
            status = PARSING_PADDING;
            push_to_accumulator(char);
          end else begin
            push_to_formatted_string(char);
          end
          i++;
        end

        PARSING_PADDING: begin
          // Ignore padding for now
          if (is_digit(char)) begin
            i++;
          end
          else begin
            status = PARSING_FORMATTER;
          end
        end

        PARSING_FORMATTER: begin
          case (char)
            // Ignore length qualifiers for 'lx', 'lu', etc...
            "l": begin
              i++;
              continue;
            end

            "s": begin
              push_to_accumulator(char);
              format_string_accumulator(arg_q);
            end

            "c": begin
              push_to_accumulator(char);
              format_char_accumulator(arg_q);
            end

            "f": begin
              // Deactivate padding
              push_to_accumulator("0");
              push_to_accumulator(char);
              format_float_accumulator(arg_q);
            end

            default: begin
              push_to_accumulator("0");
              push_to_accumulator(char);
              format_int_accumulator(arg_q);
            end
          endcase
          status = NO_FORMAT;
          i++;
        end
        default: begin
          `uvm_fatal("string_formatter", "Unreachable!")
        end
      endcase
    end
    return formatted_string;
  endfunction
endclass

function string uvm_sw_ipc::str_format(input string str, ref bit [63:0] q[$]);
  string s;
  string_formatter formatter = new();
  formatter.vif = vif;
  str = str_replace(str, "%%", "__pct__");
  s = formatter.format_string(str, q);
  s = str_replace(s, "__pct__", "%");
  return s;
endfunction

function void uvm_sw_ipc::check_phase(uvm_phase phase);
  for (int i = 0; i < UVM_SW_IPC_FIFO_NB; i++) begin
    int size = fifo_data_to_uvm[i].size();
    if (size > 0) begin
      `uvm_error(get_type_name(), $sformatf("%0d items remain in fifo_data_to_uvm[%0d]!", size, i))
    end
    size = fifo_data_to_sw[i].size();
    if (size > 0) begin
      `uvm_error(get_type_name(), $sformatf("%0d items remain in fifo_data_to_sw[%0d]!", size, i))
    end
  end
endfunction


`endif  // UVM_SW_IPC_SV
