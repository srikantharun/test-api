


interface Ctrl_if (input logic clk, input logic rstn);
  logic         sel;
  logic         enable;
  logic         write;
  logic [31:0]  wdata;
  logic [31:0]  addr;
  logic [31:0]  rdata;
  logic         ready;
  logic         pintreq;
  logic         load;
  logic         dump;
  string        process;
  logic [31:0]  drive;
  logic [31:0]  frequency;
  logic [15:0]  currentframe;
  logic [15:0]  maxframe;

  modport slavemod (
    input  clk,
    input  rstn,
    input  sel,
    input  enable,
    input  write,
    input  wdata,
    input  addr,
    output rdata,
    output ready,
    output pintreq,
    input  load,
    input  dump,
    input  frequency,
    output drive,
    output currentframe,
    output maxframe
  );

  modport mastermod (
    input  clk,
    input  rstn,
    output sel,
    output enable,
    output write,
    output wdata,
    output addr,
    input  rdata,
    input  ready,
    input  pintreq,
    output load,
    output dump,
    output frequency,
    input  drive,
    input  currentframe,
    input  maxframe

  );

endinterface

package CtrlPkg;

  `include "uvm_macros.svh"
  import uvm_pkg::*;

  class Apb;
    virtual Ctrl_if ctrl_bus;
    int inst_file;
    logic [159:0] interrupts [127:0];
    string line;

    task write(input logic [31:0] addr,input logic [31:0] data);
      @(posedge ctrl_bus.clk);
      ctrl_bus.addr    <= addr;
      ctrl_bus.sel     <= '1;
      ctrl_bus.enable  <= '0;
      ctrl_bus.wdata   <= data;
      ctrl_bus.write   <= '1;
      @(posedge ctrl_bus.clk);
      ctrl_bus.enable  <= '1;
      wait (ctrl_bus.ready);
      @(posedge ctrl_bus.clk);
      ctrl_bus.addr    <= '0;
      ctrl_bus.sel     <= '0;
      ctrl_bus.enable  <= '0;
      ctrl_bus.wdata   <= '0;
      ctrl_bus.write   <= '0;
    endtask

    task read(input logic [31:0] addr, output logic [31:0] data);
      @(posedge ctrl_bus.clk);
      ctrl_bus.addr    <= addr;
      ctrl_bus.sel     <= '1;
      @(posedge ctrl_bus.clk);
      ctrl_bus.enable  <= '1;
      wait (ctrl_bus.ready);
      @(posedge ctrl_bus.clk);
      ctrl_bus.sel     <= '0;
      ctrl_bus.enable  <= '0;
      data              = ctrl_bus.rdata;
    endtask

    task perf(input logic [31:0] addr, output logic [31:0] data);
      read(addr, data);
      $display("[CTRL] PERF: at address 0x%x: %d cycles, %d fps @ %dMHz", addr, data, (ctrl_bus.frequency*1000000)/data, ctrl_bus.frequency);
    endtask

    task poll(input logic [31:0] addr, input logic [31:0] data);
      logic [31:0] r_data;
      integer nb_try = 0;
      read(addr, r_data);
      $display("[CTRL] INFO: Polling %x for %x", addr, data);
      while((r_data & data) != data) begin
        read(addr, r_data);
        nb_try++;
        if (nb_try > 10000000) begin
          $fatal(1, "Error: timeout when polling at addr %x value %x", addr, data);
        end
      end
      $display("[CTRL] INFO: Getting %x", r_data);
    endtask

    task waitirq(input logic [31:0] addr, input logic [31:0] irqnum);
      int itexpected=interrupts[irqnum];
      if (itexpected!=0)
        itexpected=itexpected-1;
      $display("[CTRL] INFO: Interrupt %d wait", irqnum);
      while(interrupts[irqnum]==itexpected) begin
        @(posedge ctrl_bus.clk);
        if (ctrl_bus.pintreq)
          ackirq(addr);
      end
      if (interrupts[irqnum]!=0)
        interrupts[irqnum] <= interrupts[irqnum] - 1'b1;
      @(posedge ctrl_bus.clk);
    endtask





    task ackirq(input logic [31:0] addr);
      logic [31:0] res;
      logic [31:0] itbit='0;
      int core_num=0;
      int irq=0;
      int irq_valid = 0;
      
      read(addr,res);
      for(int i=31;i>=0;i--) begin
        if(res[i]=='1) begin irq=i; irq_valid = 1; break; end
      end
      if (irq_valid == 1) begin
        $display("[CTRL] INFO: Interrupt %d ack", irq);
        itbit[irq]='1;
        write(addr,itbit);
        
        if (irq<4) begin
          core_num=irq+1;
          read(addr+44+8*(core_num-1),res);
          if(res!=0) begin
            for(int j=31;j>=0;j--) begin
              if(res[j]=='1) begin irq=j; break; end
            end
            $display("[CTRL] INFO: Interrupt %d ack (Core %d Interrupt %d)", irq+32*(core_num), core_num-1, irq);
            itbit='0;
            itbit[irq]='1;
            write(addr+44+8*(core_num-1),itbit);
          end else begin
            core_num=0;
          end
        end
        interrupts[irq+32*(core_num)] <= interrupts[irq+32*(core_num)] + 1'b1;
      end
      for(int i=0;i<32;i++) begin
        @(posedge ctrl_bus.clk);
      end
    endtask

    function int open_one_file(string name, string mode);
      int file;
      string allegro_test_path;
      if($value$plusargs("ALLEGRO_TEST_PATH=%s", allegro_test_path)) begin
        allegro_test_path={allegro_test_path,"/"};
        $info("allegro_test_path=%s", allegro_test_path);
      end
      file =  $fopen({allegro_test_path,name}, mode);
      if (file == 0) begin
        $error("[CTRL] Error: Missing %s", {allegro_test_path,name});
        $stop;
      end
      return file;
    endfunction

    function string extract_word(string line, int wordnum);
      int wc=1;
      int start=0;
      int stop=0;
      for(int i=0;i<line.len();i++) begin
        if(line.getc(i)==44) begin
          stop=i-1;
          if(wc==wordnum) break;
          start=i+1;
          wc++;
        end
      end
      return line.substr(start,stop);
    endfunction

    function new(virtual Ctrl_if ctrl_bus);
      string line;
      string tmp_lc;
      int file;
      int frame;
      int lc;
      this.ctrl_bus      = ctrl_bus;
      inst_file = open_one_file("instructions.hex", "r");
      ctrl_bus.addr        <= '0;
      ctrl_bus.sel         <= '0;
      ctrl_bus.enable      <= '0;
      ctrl_bus.wdata       <= '0;
      ctrl_bus.write       <= '0;
      ctrl_bus.drive       <= '0;
      ctrl_bus.load        <= '0;
      ctrl_bus.dump        <= '0;
      ctrl_bus.currentframe<= '0;
      ctrl_bus.maxframe    <= '0;
      interrupts           <= '{default:0};
      ctrl_bus.process     = "";

      frame='0;
      lc=0;
      
      while(!$feof(inst_file) && frame != lc) begin
        int res = $fscanf(inst_file, "%s\n", line);
        if (extract_word(line,1) == "end_frame") begin
          tmp_lc = extract_word(line,4);
          lc = tmp_lc.atoi();
        end
      end

    endfunction

    task run;
      string inst;
      string proc;
      string tmp_when;
      string tmp_addr;
      string tmp_data;
      string tmp_frame;
      int frame;
      shortreal when;
      logic [31:0] addr;
      logic [31:0] data;
      logic [31:0] rdat;

      uvm_event finish_ev;

      `ifndef USE_ALLEGRO_IP_TOP
        // Unreset partitions
        $display("[CTRL] INFO: Unreset partitions");
        write(32'h00230000, 32'h00000001);
        write(32'h00230004, 32'h00000001);
      `endif

      $display("[CTRL] INFO: Start of instructions");
      while(!$feof(inst_file)) begin
        int res = $fgets(line,inst_file);
        inst=extract_word(line,1);
        tmp_when = extract_word(line,2);
        when=tmp_when.atoreal();
        tmp_addr = extract_word(line,3).substr(2,extract_word(line,3).len()-1);
        addr=tmp_addr.atohex();
        if(extract_word(line,3).len() == 0)
          proc="";
        else
          proc={".",extract_word(line,3)};

        tmp_data=extract_word(line,4).substr(2,extract_word(line,4).len()-1);
        data=tmp_data.atohex();
        tmp_frame=extract_word(line,4);
        frame=tmp_frame.atoi();
        case(inst)
          "read" : begin
                     read(addr,rdat);
                     if ((data != rdat) || (^rdat === 1'bX))
                       $error("[CTRL] ERROR: at time %f at address 0x%h read 0x%h (expected 0x%h)", when, addr, rdat, data);
                   end
          "poll" : poll(addr,data);
          "write": write(addr,data);
          "perf" : perf(addr,data);
          "irq"  : waitirq(addr,data);
          "drive": ctrl_bus.drive<=addr;
          "start_frame": begin
                           @(posedge ctrl_bus.clk)
                           if(frame>ctrl_bus.maxframe)
                             ctrl_bus.maxframe<=frame;
                           ctrl_bus.currentframe<=frame;
                           ctrl_bus.process=proc;
                           ctrl_bus.load<='1;
                           @(posedge ctrl_bus.clk)
                           ctrl_bus.load<='0;
                           if ($test$plusargs("CODEC_SYSTEM_LEVEL_TESTCASE") && (proc != ".MCU")) begin
                             // Axelera: In system-level testcases, MCU expects an IRQ
                             //          from host before starting to decode anything.
                             bit   [31:0] CODEC_MCU_IRQ_REG = 32'hb000040c;
                             logic [31:0] rdata;
                             $display("[CTRL] INFO: Notifying MCU for start_frame");
                             // Wait for IRQ bit to be cleared by the MCU (if set)
                             do begin
                               read(CODEC_MCU_IRQ_REG, rdata);
                             end while (rdata[0]);
                             // Send signal by setting IRQ bit
                             write(CODEC_MCU_IRQ_REG, 32'h00000001);
                           end
                         end
          "end_frame"  : begin
                           @(posedge ctrl_bus.clk)
                           ctrl_bus.currentframe<=frame;
                           ctrl_bus.process=proc;
                           ctrl_bus.dump<='1;
                           @(posedge ctrl_bus.clk)
                           ctrl_bus.dump<='0;
                         end
          default: ;
        endcase
      end
      $display("[CTRL] INFO: End of instructions");
      finish_ev = uvm_event_pool::get_global("finish_ev");
      finish_ev.trigger();
      //$finish;
    endtask

  endclass


  class Ctrl;
    virtual Ctrl_if ctrl_bus;
    Apb apb;

    function new(virtual Ctrl_if ctrl_bus);
      this.apb = new(ctrl_bus);
      this.ctrl_bus = ctrl_bus;
    endfunction

    task run;
      @(posedge ctrl_bus.rstn)
      @(posedge ctrl_bus.clk)
      apb.run;
    endtask

  endclass
endpackage
