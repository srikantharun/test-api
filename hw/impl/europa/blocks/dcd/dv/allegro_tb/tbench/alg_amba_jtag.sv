



interface Jtag_if (input logic clk, input logic rstn);
    logic    tdi;
    logic    tms;
    logic    tck;
    logic    trst;
    logic    tdo;

  modport slavemod (
    input  clk,
    input  rstn,
    input  tdi,
    input  tms,
    input  tck,
    input  trst,
    output tdo
  );

  modport mastermod (
    input  clk,
    input  rstn,
    output tdi,
    output tms,
    output tck,
    output trst,
    input  tdo
  );

endinterface



package JtagPkg;
  class Tap;
    virtual Jtag_if jtag_bus;
    int file;
    longint shifted_data;

  task make_tck();
    @(posedge jtag_bus.clk)
    jtag_bus.tck = '1;
    @(posedge jtag_bus.clk)
    jtag_bus.tck = '0;
  endtask : make_tck

  task make_rst();
    make_tck();
    jtag_bus.trst = '1;
    make_tck();
  endtask : make_rst

  task wait_clk();
    repeat(50) make_tck();
  endtask : wait_clk

  task sftrst();
    jtag_bus.tms = '1;
    repeat(5) make_tck();
  endtask : sftrst

  task set_one();
    jtag_bus.tms = '1;
    make_tck();
  endtask : set_one

  task set_zero();
    jtag_bus.tms = '0;
    make_tck();
  endtask : set_zero

  task set_sig(logic tms,logic tdi);
    jtag_bus.tms = tms;
    jtag_bus.tdi = tdi;
    make_tck();
  endtask : set_sig

  task shift_data(logic [63:0] value, integer n);
    shifted_data = 0;
    shifted_data[n-1] = jtag_bus.tdo;
    shifted_data = shifted_data >> 1;
    repeat(n-1)
    begin
      jtag_bus.tdi = value[0];
      value = value >> 1;
      make_tck();
      shifted_data[n-1] = jtag_bus.tdo;
      shifted_data = shifted_data >> 1;
    end
    jtag_bus.tdi = value[0];
  endtask : shift_data

  task sel_ir(logic [31:0] value,logic longpath);
    set_one();
    if(longpath) begin
      set_zero();
      set_one();
      set_zero();
      set_zero();
      set_one();
      set_zero();
      shift_data(value,5);
      set_one();
      set_zero();
      set_zero();
      set_one();
      set_one();
      set_zero();
      set_zero();
      set_one();
    end else begin
      set_zero();
      set_zero();
      shift_data(value,5);
      set_one();
      set_one();
      set_one();
    end
  endtask : sel_ir

  task sel_dr(logic [63:0] value,int size,logic longpath);
    if(longpath) begin
      set_zero();
      set_one();
      set_zero();
      set_zero();
      set_one();
      set_zero();
      shift_data(value,size);
      set_one();
      set_zero();
      set_zero();
      set_one();
      set_one();
      set_zero();
      set_zero();
      set_one();
    end else begin
      set_zero();
      set_zero();
      shift_data(value,size);
      set_one();
      set_one();
      set_one();
    end
  endtask : sel_dr

  function new(virtual Jtag_if jtag_bus);
    int instr;
    int size;
    logic[63:0] data;
    this.jtag_bus = jtag_bus;
    jtag_bus.tms <= '1;
    jtag_bus.trst <= '0;
    jtag_bus.tdi <= '0;
    jtag_bus.tck <= '0;
  endfunction

  task run;
    int res;
    int instr;
    int size;
    logic [63:0] data;
    int address;
    string access;
    string allegro_test_path;
    int file;
    if($value$plusargs("ALLEGRO_TEST_PATH=%s", allegro_test_path)) begin
      allegro_test_path={allegro_test_path,"/"};
      $info("allegro_test_path=%s", allegro_test_path);
    end
    file = $fopen({allegro_test_path,"jtag.hex"}, "r");
    if (file != 0) begin
      wait_clk();
      make_rst();
      sftrst();
      set_zero();
      set_zero();
      set_one();
      while (!$feof(file)) begin
        res = $fscanf(file,"%x,%x,%x,%x,%s\n",instr,size,data,address,access);
        if(res==2) begin
          
          set_sig(instr,size);
          $display("[JTAG] raw data %x %x",instr,size);
        end else if(res==3) begin
          sel_ir(instr,0);
          sel_dr(data,size,0);
          $display("[JTAG] instruction %d of size %d with data in %x and data out %x",instr,size,data,shifted_data);
        end else begin
          if(res==5) begin
            sel_ir(17,1);
            if(access=="write")
              sel_dr({address[9:0],data[31:0],2'b10},size,1);
            else
              sel_dr({address[9:0],data[31:0],2'b01},size,1);
            $display("[JTAG] DM instruction %d of size %d, %s at address %x, data in %x and data out %x",instr,size,access,address[9:0],data[31:0],shifted_data[33:2]);
          end
        end
      end
      $fclose(file);
    end
  endtask

endclass



class Jtag;
  virtual Jtag_if jtag_bus;
  Tap tap;

  function new(virtual Jtag_if jtag_bus);
    this.tap = new(jtag_bus);
    this.jtag_bus = jtag_bus;
  endfunction

  task run;
    @(posedge jtag_bus.rstn)
    @(posedge jtag_bus.clk)
    tap.run;
  endtask

endclass

endpackage
