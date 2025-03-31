




module alg_ip_waves
  #(parameter string DEF_PROC="")
(
  input logic   clk,
  input logic   frm_done,
  input string  process
);


  logic   rval;
  logic   wave_dump_enable=0;
  integer wave_dump_start_fr=-1;
  integer wave_dump_end_fr=-1;
  integer wave_dump_cmd=1;
  string  wave_dump_proc;
  wire    wave_dump_proc_undef = wave_dump_proc=="";
  integer wave_dump_high=0;
  integer wave_dump_low=0;

  initial
  begin
    wave_dump_proc=DEF_PROC;

    if(!$value$plusargs("WAVE_DUMP_START=%d", wave_dump_start_fr))
      rval=$value$plusargs("WDS=%d", wave_dump_start_fr);
    if(!$value$plusargs("WAVE_DUMP_STOP=%d", wave_dump_end_fr))
      rval=$value$plusargs("WDE=%d", wave_dump_end_fr);
    if(!$value$plusargs("WAVE_DUMP_PROC=%s", wave_dump_proc))
      rval=$value$plusargs("WDP=%s", wave_dump_proc);
    if(!$value$plusargs("WAVE_DUMP_CMD=%d", wave_dump_cmd))
      rval=$value$plusargs("WDC=%d", wave_dump_cmd);

    if(!$value$plusargs("WAVE_DUMP_HIGH=%d", wave_dump_high))
      rval=$value$plusargs("WDH=%d", wave_dump_high);
    if(!$value$plusargs("WAVE_DUMP_LOW=%d", wave_dump_low))
      rval=$value$plusargs("WDL=%d", wave_dump_low);

    if(wave_dump_start_fr>=0) wave_dump_enable=1;
    if(wave_dump_start_fr==0) wave_on;

    if(wave_dump_enable)
    begin
      $display ("[WAVE] INFO: %m: ---------------------------------------");
      $display ("[WAVE] INFO: %m: WDs=%1d WDE=%1d WDP=<%s> WDH=%1d WDL=%1d",wave_dump_start_fr,wave_dump_end_fr,wave_dump_proc,wave_dump_high,wave_dump_low);
      $display ("[WAVE] INFO: %m: ---------------------------------------");
    end
  end


  wire wav_frm_done = wave_dump_enable && frm_done && ((wave_dump_proc==process) || wave_dump_proc_undef);

  always @(negedge clk)
    if(wav_frm_done&&wave_dump_proc_undef)
    begin
      $display("[WAVE] NOTE: wave_dump_proc is not set, so setting to <%s> Use +WAVE_DUMP_PROC=<name> to select an alternative",process);
      wave_dump_proc=process;
    end



  reg     wave_dump_active=0;
  reg     wave_dump_stop=0;
  integer wave_dump_start=0;

  task wave_on;
    begin
      if(wave_dump_active==1)
      begin
        $display ("[WAVE] INFO: %m: ---------------------------------------");
        $display ("[WAVE] INFO: %m: Wave dumping already active.           ");
        $display ("[WAVE] INFO: %m: ---------------------------------------");
      end
      else
      begin
        wave_dump_start  = wave_dump_cmd;
        wave_dump_active = 1;
        wave_dump_stop   = 0;
        $display ("[WAVE] INFO: %m: ---------------------------------------");
        $display ("[WAVE] INFO: %m: waveform dump started ...%s             ",wave_dump_proc);
        $display ("[WAVE] INFO: %m: ---------------------------------------");
      end
    end
  endtask


  
  
  task wave_off;
    begin
      if(wave_dump_active==0)
      begin
        $display ("[WAVE] INFO: %m: ---------------------------------------");
        $display ("[WAVE] INFO: %m: Wave dumping not active.               ");
        $display ("[WAVE] INFO: %m: ---------------------------------------");
      end
      else
      begin
        wave_dump_stop   = 1;
        wave_dump_active = 0;
        $display ("[WAVE] INFO: %m: ---------------------------------------");
        $display ("[WAVE] INFO: %m: Waveform dump stopped ...%s            ",wave_dump_proc);
        $display ("[WAVE] INFO: %m: ---------------------------------------");
      end
    end
  endtask


  
  reg     wave_dump_pause=0;
  reg     wave_dump_unpause=0;
  task wave_pause;
    begin
      wave_dump_pause    = 1;
      wave_dump_unpause  = 0;
      $display ("[WAVE] INFO: %m: ---------------------------------------");
      $display ("[WAVE] INFO: %m: waveform dump Paused ...               ");
      $display ("[WAVE] INFO: %m: ---------------------------------------");
    end
  endtask

  task wave_unpause;
    begin
      wave_dump_pause    = 0;
      wave_dump_unpause  = 1;
      $display ("[WAVE] INFO: %m: ---------------------------------------");
      $display ("[WAVE] INFO: %m: waveform dump UnPaused ...             ");
      $display ("[WAVE] INFO: %m: ---------------------------------------");
    end
  endtask



  
  integer frame_count = 0;
  wire    wave_start_trig = wave_dump_enable && ~wave_dump_active && wav_frm_done && (frame_count+1)==wave_dump_start_fr;
  wire    wave_stop_trig  = wave_dump_enable &&  wave_dump_active && wav_frm_done && (frame_count+1)==wave_dump_end_fr;

  always @(negedge clk)
  begin
    if(wave_start_trig)       wave_on;
    if(wave_stop_trig)        wave_off;

    if(wav_frm_done)
    begin
      frame_count  = frame_count + 1;
      
    end
  end

  
  int cycle_count=0;
  wire start_pause = cycle_count==1 && !wave_dump_pause;
  wire stop_pause  = cycle_count==1 &&  wave_dump_pause;


  always @(negedge clk)
  begin
    if(wave_dump_active)
    begin
      if(start_pause) wave_pause;
      if(stop_pause)  wave_unpause;

      if(~|cycle_count)
        cycle_count=(wave_dump_pause?wave_dump_low : wave_dump_high)*1000;
      else
        cycle_count=cycle_count-1;
    end
  end

endmodule
