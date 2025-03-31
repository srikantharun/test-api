



interface Sram_if (input logic clk);
  logic [255:0] rdata;
  logic [255:0] wdata;
  logic [31:0]  wstrb;
  logic [63:0]  raddr;
  logic [63:0]  waddr;
  logic         nwen;
  logic         nren;
  logic         load;
  logic         dump;
  string        process;
  logic [15:0]  currentframe;
  logic [15:0]  maxframe;



  modport slavemod (
    input  clk,
    output rdata,
    input  wdata,
    input  wstrb,
    input  raddr,
    input  waddr,
    input  nwen,
    input  nren,
    input  load,
    input  dump,
    ref    process,
    input  currentframe,
    input  maxframe
  );

  modport mastermod (
    input  clk,
    input  rdata,
    output wdata,
    output wstrb,
    output raddr,
    output waddr,
    output nwen,
    output nren,
    output load,
    output dump,
    ref    process,
    output currentframe,
    output maxframe
  );

endinterface


package SramPkg;

  class Buffer;
    logic [255:0] sram[bit[63:0]];
    typedef struct {longint baseaddr; int sizeaddr; logic init; logic dump;} BufferInfos;
    BufferInfos MapInfos[string][string][string]; 
    BufferInfos MemInfos[string][string][string]; 


    function void write_256(logic [63:0] waddr, logic [255:0] data, logic [31:0] wstrb);

      logic[63:0] addr = waddr >> 5;
      for (int i = 0; i < 32; i++)
        if (wstrb[i])
          sram[addr][8*i +: 8] = data[8*i +: 8];
    endfunction


    function void write_128(logic [63:0] waddr, logic [255:0] data, logic [31:0] wstrb);

      logic[63:0] addr = waddr >> 5;

      int data_offset = 0;
      if (waddr[4])
        data_offset = 128;

      for (int i = 0; i < 16; i++)
        if (wstrb[i])
          sram[addr][8*i + data_offset +: 8] = data[8*i +: 8];

    endfunction


    function void write_64(logic [63:0] waddr, logic [255:0] data, logic [31:0] wstrb);

      logic[63:0] addr = waddr >> 5;

      int data_offset = 0;
      if (waddr[4]) begin
        if (waddr[3]) begin
          data_offset = 192;
        end else begin
          data_offset = 128;
        end
      end else begin
        if (waddr[3]) begin
          data_offset = 64;
        end
      end

      for (int i = 0; i < 8; i++)
        if (wstrb[i])
          sram[addr][8*i + data_offset +: 8] = data[8*i +: 8];
    endfunction


    function void write_32(logic [63:0] waddr, logic [255:0] data, logic [31:0] wstrb);

      logic[63:0] addr = waddr >> 5;

      int data_offset = 0;
      if (waddr[3]) begin
        if (waddr[2]) begin
          data_offset = 24;
        end else begin
          data_offset = 16;
        end
      end else begin
        if (waddr[2]) begin
          data_offset = 8;
        end
      end

      for (int i = 0; i < 4; i++)
        if (wstrb[i])
          sram[addr][8*i + data_offset +: 8] = data[8*i +: 8];
    endfunction


    function void write(logic [63:0] waddr, logic [255:0] data, logic [31:0] wstrb, int access_length);

      case (access_length)
        256 :
          write_256(waddr, data, wstrb);
        128 :
          write_128(waddr, data, wstrb);
        64 :
          write_64(waddr, data, wstrb);
        32 :
          write_32(waddr, data, wstrb);
        default : begin
          $error("[SRAM] ERROR: Access length '%d' is not supported", access_length);
        end
      endcase
    endfunction


    function logic[255:0] read_256(logic [63:0] raddr);

      return sram[raddr>>5];
    endfunction


    function logic[255:0] read_128(logic [63:0] raddr);

      logic [255:0] rdata;
      rdata[255:128] = 'Z;
      case(raddr[4])
        1'b0 : rdata[127:0] = sram[raddr>>5][127:0];
        1'b1 : rdata[127:0] = sram[raddr>>5][255:128];
      endcase

      return rdata;
    endfunction


    function logic[255:0] read_64(logic [63:0] raddr);

      logic [255:0] rdata;
      rdata[255:64] = 'Z;
      case(raddr[4:3])
        2'b00 : rdata[63:0] = sram[raddr>>5][63:0];
        2'b01 : rdata[63:0] = sram[raddr>>5][127:64];
        2'b10 : rdata[63:0] = sram[raddr>>5][191:128];
        2'b11 : rdata[63:0] = sram[raddr>>5][255:192];
      endcase

      return rdata;
    endfunction


    function logic[255:0] read_32(logic [63:0] raddr);

      logic [255:0] rdata;
      rdata[255:32] = 'Z;
      case(raddr[3:2])
        2'b00 : rdata[31:0] = sram[raddr>>5][7:0];
        2'b01 : rdata[31:0] = sram[raddr>>5][15:8];
        2'b10 : rdata[31:0] = sram[raddr>>5][23:16];
        2'b11 : rdata[31:0] = sram[raddr>>5][31:24];
      endcase

      return rdata;
    endfunction


    function logic[255:0] read(logic [63:0] raddr, int access_length);

      if (sram.exists(raddr>>5)) begin
        case (access_length)
          256 :
            return read_256(raddr);
          128 :
            return read_128(raddr);
          64 :
            return read_64(raddr);
          32 :
            return read_32(raddr);
          default : begin
            $error("[SRAM] ERROR: Access length '%d' is not supported", access_length);
          end
        endcase
      end
      else
        return 'z;
    endfunction


    function int open_one_file(string name, string mode, bit no_prefix=0);
      int file;
      string allegro_test_path;
      if(no_prefix == 0) begin
        if($value$plusargs("ALLEGRO_TEST_PATH=%s", allegro_test_path)) begin
          allegro_test_path={allegro_test_path,"/"};
          $info("allegro_test_path=%s", allegro_test_path);
        end
      end
      file =  $fopen({allegro_test_path,name}, mode);
      if (!file) begin
        $warning("[SRAM] WARNING: Missing %s", {allegro_test_path,name});
        $stop;
      end
      return file;
    endfunction


    function void init_output_buffers_to_X(logic [15:0] frame, string process);

      longint addr;
      $display("[SRAM] INFO: init_output_buffer_to_x process %s frame  %d", process, frame);
      foreach(MapInfos[a, b, file_ext]) begin
        if (a == process && int'(b) == frame) begin
          if (MapInfos[process][frame][file_ext].init == 1'b1) begin
            addr = MapInfos[process][frame][file_ext].baseaddr;
            while ( addr < MapInfos[process][frame][file_ext].baseaddr + MapInfos[process][frame][file_ext].sizeaddr ) begin
              sram[addr] = 'x;
              addr = addr + 1;
            end
          end else
            $display("[SRAM] INFO: No init output buffer %s",file_ext);
        end
      end
    endfunction


    function new();

    endfunction

    function string pad_with_zeros(int num, int width);
        string result;
        begin
            result = $sformatf("%0d", num);
            while (result.len() < width) begin
              result = {"0", result};
            end
            return result;
        end
    endfunction

    function void load(logic [15:0] frame, string process);

      int     map_file;
      longint baseaddr;
      longint prev_baseaddr;
      int     sizeaddr;
      int     sizecalc;
      int     index;
      string  frame_num = pad_with_zeros(int'(frame),4);
      string allegro_test_path;

      map_file = open_one_file({"sram_",frame_num,process,".refmap"}, "r");

      $display("[SRAM] INFO: Loading sram content for process %s, frame %d...", process, frame);
      while (!$feof(map_file)) begin
        string line;
        string file_ext;
        string nocheck;

        int ret = $fgets(line,map_file);
        int res = $sscanf(line, "%s %X %d %s", file_ext, baseaddr, sizeaddr, nocheck);
        if(res==3 || res==4) begin
          if (baseaddr&31)
            $error("[SRAM] ERROR: Address %s on process %s is not multiple of 32 bytes", process, baseaddr);
          MapInfos[process][frame][file_ext].baseaddr = baseaddr>>5;
          MapInfos[process][frame][file_ext].sizeaddr = sizeaddr;
          MapInfos[process][frame][file_ext].init = 1'b1;
          MapInfos[process][frame][file_ext].dump = 1'b1;
          if (nocheck == "no_init")
            MapInfos[process][frame][file_ext].init = 1'b0;
          if (nocheck == "no_dump")
            MapInfos[process][frame][file_ext].dump = 1'b0;
        end
      end

      init_output_buffers_to_X(frame, process);

      if($value$plusargs("ALLEGRO_TEST_PATH=%s", allegro_test_path)) begin
        allegro_test_path={allegro_test_path,"/"};
        $info("allegro_test_path=%s", allegro_test_path);
      end
      $readmemh({allegro_test_path,"sram_",frame_num,process,".mem"}, sram);
      $display("[SRAM] INFO: Done, total: %d bytes", sram.num()*32);

      index=0;
      map_file = open_one_file({"sram_",frame_num,process,".mem"}, "r");
      while (!$feof(map_file)) begin
        string line;

        int ret = $fgets(line,map_file); 
        int res = $sscanf(line, "@%x ", baseaddr);
        int com = $sscanf(line, "\/\/@%x \/\/ size: %d", baseaddr, sizeaddr);

        if (com > 0)
        begin
          MemInfos[process][frame][index].baseaddr = baseaddr;
          MemInfos[process][frame][index].sizeaddr = sizeaddr;
          index=index+1;
        end
        else if(res==0 && line.substr(0,1)!="\/\/") begin
          sizecalc=sizecalc+1;
        end else begin
          if(sizecalc!=0) begin
            MemInfos[process][frame][index].baseaddr = prev_baseaddr;
            MemInfos[process][frame][index].sizeaddr = sizecalc;
            index=index+1;
          end
          prev_baseaddr=baseaddr;
          sizecalc=0;
        end

      end

      if ($test$plusargs("CODEC_SYSTEM_LEVEL_TESTCASE")) begin
        // Axelera: For the buffer containing the MCU code, manually set the
        //          size to 1 MiB to avoid false positives in
        //          check_read_address_range(). Also zero out the memory in the
        //          RAM model to avoid reading uninitialized values, which
        //          breaks the MCU caches in simulation.
        if (frame == 0 && process == ".MCU") begin
          // Find the MCU code buffer: frame==0, process==.MCU, baseaddr!=0
          foreach (MemInfos[p,f,i]) begin
            if (int'(f) != frame || p != process)
              continue;
            if (MemInfos[p][f][i].baseaddr != 0) begin
              int prev_sizeaddr = MemInfos[p][f][i].sizeaddr;
              MemInfos[p][f][i].sizeaddr = 1024 * 1024 / 32; // 1 MiB

              // zero out memory that was just "appended" to the buffer
              for (int j = prev_sizeaddr; j < MemInfos[p][f][i].sizeaddr; j++) begin
                sram[MemInfos[p][f][i].baseaddr + j] = '0;
              end

              break;
            end
          end
        end
      end

    endfunction


    function void dump(logic [15:0] frame, string process);

      longint       addr;
      int           out;
      int           ref_file;
      int           ref_file_size;
      logic [255:0] ref_word;
      int           status;
      int           error = 0;
      int           map_file;
      int           index = 0;
      string        frame_num = pad_with_zeros(int'(frame), 4);

      string allegro_test_path;
      if($value$plusargs("ALLEGRO_TEST_PATH=%s", allegro_test_path)) begin
        allegro_test_path={allegro_test_path,"/"};
        $info("allegro_test_path=%s", allegro_test_path);
      end

      $display("[SRAM] INFO: Dumping sram for process %s, frame %d ...", process, frame);
      foreach(MapInfos[a, b, file_ext]) begin
        error=0;
        if (a == process && int'(b) == frame) begin
          if (MapInfos[process][frame][file_ext].dump == 1'b1) begin
            int     sizeaddr;
            longint baseaddr;
            longint addr;
            out = open_one_file({"sram_",frame_num,process,".sim.",file_ext}, "w", 1);
            ref_file = $fopen({allegro_test_path,"sram_",frame_num,process,".ref.",file_ext}, "r");
            if (!ref_file) begin
              $warning("[SRAM] WARNING: Reference file %s doesn't exists", {allegro_test_path,"sram_",frame_num,process,".ref.",file_ext});
            end
            else begin
              void'($fseek(ref_file, 0 , 2));
              ref_file_size = $ftell(ref_file);
              $display("ref_file_size = %d", ref_file_size);
              if(ref_file_size > 0) begin
                $rewind(ref_file);
              end
            end
            addr = MapInfos[process][frame][file_ext].baseaddr;
            while ( addr < MapInfos[process][frame][file_ext].baseaddr + MapInfos[process][frame][file_ext].sizeaddr ) begin
              if (ref_file) begin
                if ($feof(ref_file)) begin
                  $error("[SRAM] ERROR: Output frame is larger than the reference frame");
                  error++;
                end
                else begin
                  status = $fscanf(ref_file, "%h\n", ref_word);
                  if (status != 1) begin
                    $error("[SRAM] ERROR: Reading the reference file failed");
                    error++;
                  end
                  if (ref_word != sram[addr]) begin
                    $error("[SRAM] ERROR: Output frame doesn't match the reference frame (sram[%d]=0x%h != 0x%h)", addr, sram[addr], ref_word);
                    error++;
                  end
                end
              end
              $fdisplay(out, "%h", sram[addr]);
              addr = addr + 1;
            end
            if (ref_file) begin
              if (!$feof(ref_file) && (ref_file_size > 0)) begin
                $error("[SRAM] ERROR: reference frame is larger than the output frame");
                error++;
              end
              if (error > 0) begin
                $error("[SRAM] ERROR: reference frame is different than the output frame");
              end
              else begin
                $display("[SRAM] INFO: reference frame is identical to the output frame");
              end
            end
            $fflush(out);
            $fclose(out);
          end else
            $display("[SRAM] INFO: No dump output buffer %s",file_ext);
        end
      end
      MapInfos[process][frame].delete;

    endfunction

  endclass


  class SramControler;

    virtual Sram_if sram_bus;
    Buffer buff;
    int access_length;

    function new(virtual Sram_if sram_bus, Buffer buff, int access_length);
      this.sram_bus      = sram_bus;
      this.buff          = buff;
      this.access_length = access_length;
    endfunction

    task run;
      forever begin
        @(posedge sram_bus.clk)
        if (!sram_bus.nwen)
          buff.write(sram_bus.waddr, sram_bus.wdata, sram_bus.wstrb, access_length);

        if (!sram_bus.nren)
          sram_bus.rdata <= buff.read(sram_bus.raddr, access_length);
      end
    endtask

  endclass


  class Sram;

    virtual Sram_if sram_bus[7];
    Buffer buff;
    SramControler controler[7];



    function new(virtual Sram_if sram_bus[7]);

      this.buff = new();
      this.sram_bus = sram_bus;
      controler[0] = new(sram_bus[0], buff, 128);
      controler[1] = new(sram_bus[1], buff, 128);
      controler[2] = new(sram_bus[2], buff, 128);
      controler[3] = new(sram_bus[3], buff, 128);
      controler[4] = new(sram_bus[4], buff, 128);
      controler[5] = new(sram_bus[5], buff, 32);  
      controler[6] = new(sram_bus[6], buff, 32);  
    endfunction


    function void check_read_collision();

      for(int i = 0; i < 7 - 1; i++) begin
        for(int j = i+1; j < 7 ; j++) begin
          if(!sram_bus[i].nren && !sram_bus[j].nren &&
              sram_bus[i].raddr == sram_bus[j].raddr) begin
            $warning("[SRAM] WARNING : Concurrent RAM read at same address: %x at time %d", sram_bus[i].raddr, $time);
          end
        end
      end
    endfunction


    function void check_write_collision();

      for(int i = 0; i < 7 - 1; i++) begin
        for(int j = i+1; j < 7 ; j++) begin
          if(!sram_bus[i].nwen && !sram_bus[j].nwen &&
              sram_bus[i].waddr == sram_bus[j].waddr) begin
            $warning("[SRAM] WARNING: Concurrent RAM write at same address: %x at time %d", sram_bus[i].waddr, $time);
          end
        end
      end
    endfunction


    function void check_write_address_range();

      int FoundRange;
      for(int axi = 0; axi < 7; axi++) begin
        FoundRange = 0;
        foreach(buff.MapInfos[str1, str2, str3]) begin
          if ( !sram_bus[axi].nwen && sram_bus[axi].waddr >= buff.MapInfos[str1][str2][str3].baseaddr*32 && sram_bus[axi].waddr < (buff.MapInfos[str1][str2][str3].baseaddr + buff.MapInfos[str1][str2][str3].sizeaddr)*32 )  
            FoundRange = 1;
        end

        if ( !sram_bus[axi].nwen && !FoundRange ) begin
          $warning("[SRAM] WARNING: Write on AXI %d at address 0x%X is out of any output buffer range at time %d", axi, sram_bus[axi].waddr, $time);
        end
      end
    endfunction


    function void check_read_address_range();

      int FoundRange;
      for(int axi = 0; axi < 7; axi++) begin
        FoundRange = 0;
        foreach(buff.MemInfos[str1, str2, str3]) begin
          if ( !sram_bus[axi].nren && sram_bus[axi].raddr >= buff.MemInfos[str1][str2][str3].baseaddr*32 && sram_bus[axi].raddr < (buff.MemInfos[str1][str2][str3].baseaddr + buff.MemInfos[str1][str2][str3].sizeaddr)*32 )  
          begin
            FoundRange = 1;
          end
        end

        if ( !sram_bus[axi].nren && !FoundRange ) begin
        begin
          $warning("[SRAM] WARNING: Read on AXI %d at address 0x%X is out of any input buffer range at time %d", axi, sram_bus[axi].raddr, $time);
        end
        end
      end
    endfunction


    task run_checks();

      forever begin
        @(posedge(sram_bus[0].clk))
        check_read_collision();
        check_write_collision();
        check_read_address_range();
        check_write_address_range();
      end
    endtask


    task load_buff();

      forever begin
        @(posedge(sram_bus[0].clk))
        @(posedge sram_bus[0].load)
        buff.load(sram_bus[0].currentframe,sram_bus[0].process);
      end
    endtask


    task dump_buff();

      forever begin
        @(posedge(sram_bus[0].clk))
        @(posedge sram_bus[0].dump)
        buff.dump(sram_bus[0].currentframe,sram_bus[0].process);
      end
    endtask


    task run;

      fork
        load_buff();
        run_checks();
        controler[0].run();
        controler[1].run();
        controler[2].run();
        controler[3].run();
        controler[4].run();
        controler[5].run();
        controler[6].run();
        dump_buff();
      join_any
    endtask

  endclass
endpackage
