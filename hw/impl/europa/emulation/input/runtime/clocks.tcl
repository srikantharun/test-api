array set Axelera::clocks {
  ref_clk           {path "hdl_top/i_ref_clk" freq 0 unit ""}
  tck               {path "hdl_top/i_tck" freq 0 unit ""}
  spi_clk2x         {path "hdl_top/spi_clk2x" freq 0 unit ""}
  fast_clk_ext      {path "hdl_top/i_europa/u_aipu/u_soc_mgmt_p/u_soc_mgmt/u_soc_mgmt_clk_gen/o_fast_clk_ext" freq 0 unit ""}
  fast_clk_int      {path "hdl_top/i_europa/u_aipu/u_soc_mgmt_p/u_soc_mgmt/u_soc_mgmt_clk_gen/o_fast_clk_int" freq 0 unit ""}
  apu_clk           {path "hdl_top/i_europa/u_aipu/u_soc_mgmt_p/u_soc_mgmt/u_soc_mgmt_clk_gen/o_apu_clk" freq 0 unit ""}
  rtc_clk           {path "hdl_top/i_europa/u_aipu/u_soc_mgmt_p/u_soc_mgmt/rtc_clk" freq 0 unit ""}
  codec_clk         {path "hdl_top/i_europa/u_aipu/u_soc_mgmt_p/u_soc_mgmt/u_soc_mgmt_clk_gen/o_codec_clk" freq 0 unit ""}
  emmc_clk          {path "hdl_top/i_europa/u_aipu/u_soc_mgmt_p/u_soc_mgmt/u_soc_mgmt_clk_gen/o_emmc_clk" freq 0 unit ""}
  periph_clk_ext    {path "hdl_top/i_europa/u_aipu/u_soc_mgmt_p/u_soc_mgmt/u_soc_mgmt_clk_gen/o_periph_clk_ext" freq 0 unit ""}
  periph_clk_int    {path "hdl_top/i_europa/u_aipu/u_soc_mgmt_p/u_soc_mgmt/u_soc_mgmt_clk_gen/o_periph_clk_int" freq 0 unit ""}
  ddr_ref_east_clk  {path "hdl_top/i_europa/u_aipu/u_soc_mgmt_p/u_soc_mgmt/u_soc_mgmt_clk_gen/o_ddr_ref_east_clk" freq 0 unit ""}
  ddr_west_clk      {path "hdl_top/i_europa/u_aipu/u_ddr_west_clock_gen_p/o_ddr_west_clk" freq 0 unit ""}
  ddr_clk_graph_0   {path "hdl_top/i_europa/u_aipu/u_lpddr_p_graph_0/u_lpddr_subsys_wrapper/snps_ddr_subsystem_inst/lpddr5_wck" freq 0 unit ""}
  uart_clk_4x       {path "hdl_top/uart_clk_4x" freq 0 unit ""}
}

array set Axelera::clock_configs_default {
  top.VELOCE_TOP_COMMON {
    ref_clk           {freq 50        unit "MHz" }
    tck               {freq 50        unit "MHz" }
    spi_clk2x         {freq 20        unit "MHz" }
    fast_clk_ext      {freq 50        unit "MHz" }
    fast_clk_int      {freq 50        unit "MHz" }
    apu_clk           {freq 50        unit "MHz" }
    rtc_clk           {freq 50        unit "MHz" }
    codec_clk         {freq 50        unit "MHz" }
    emmc_clk          {freq 50        unit "MHz" }
    periph_clk_ext    {freq 50        unit "MHz" }
    periph_clk_int    {freq 50        unit "MHz" }
    ddr_ref_east_clk  {freq 6250      unit "KHz" }
    ddr_west_clk      {freq 6250      unit "KHz" }
    uart_clk_4x       {freq 460800    unit "Hz"  }
  }
  top.VELOCE_TOP_LIGHT_REAL_LPDDR {
    ref_clk           {freq 50        unit "MHz" }
    tck               {freq 50        unit "MHz" }
    spi_clk2x         {freq 20        unit "MHz" }
    fast_clk_ext      {freq 50        unit "MHz" }
    fast_clk_int      {freq 50        unit "MHz" }
    apu_clk           {freq 50        unit "MHz" }
    rtc_clk           {freq 50        unit "MHz" }
    codec_clk         {freq 50        unit "MHz" }
    emmc_clk          {freq 50        unit "MHz" }
    periph_clk_ext    {freq 50        unit "MHz" }
    periph_clk_int    {freq 50        unit "MHz" }
    ddr_ref_east_clk  {freq 6250      unit "KHz" }
    ddr_west_clk      {freq 33333     unit "KHz" }
    ddr_clk_graph_0   {freq 133332    unit "KHz" }
    uart_clk_4x       {freq 460800    unit "Hz"  }
  }
}
array set Axelera::clock_configs_canonical {
  top.VELOCE_TOP_COMMON {
    ref_clk           {freq 50        unit "MHz" }
    tck               {freq 100       unit "MHz" }
    spi_clk2x         {freq 50        unit "MHz" }
    fast_clk_ext      {freq 1200      unit "MHz" }
    fast_clk_int      {freq 1200      unit "MHz" }
    apu_clk           {freq 1200      unit "MHz" }
    rtc_clk           {freq 50        unit "MHz" }
    codec_clk         {freq 600       unit "MHz" }
    emmc_clk          {freq 200       unit "MHz" }
    periph_clk_ext    {freq 100       unit "MHz" }
    periph_clk_int    {freq 100       unit "MHz" }
    ddr_ref_east_clk  {freq 6250      unit "KHz" }
    ddr_west_clk      {freq 6250      unit "KHz" }
    uart_clk_4x       {freq 460800    unit "Hz"  }
  }
  top.VELOCE_TOP_LIGHT_REAL_LPDDR {
    ref_clk           {freq 50        unit "MHz" }
    tck               {freq 100       unit "MHz" }
    spi_clk2x         {freq 50        unit "MHz" }
    fast_clk_ext      {freq 1200      unit "MHz" }
    fast_clk_int      {freq 1200      unit "MHz" }
    apu_clk           {freq 1200      unit "MHz" }
    rtc_clk           {freq 50        unit "MHz" }
    codec_clk         {freq 600       unit "MHz" }
    emmc_clk          {freq 200       unit "MHz" }
    periph_clk_ext    {freq 100       unit "MHz" }
    periph_clk_int    {freq 100       unit "MHz" }
    ddr_ref_east_clk  {freq 800       unit "MHz" }
    ddr_west_clk      {freq 800       unit "MHz" }
    ddr_clk_graph_0   {freq 3200      unit "MHz" }
    uart_clk_4x       {freq 460800    unit "Hz"  }
  }
}

proc get_clock_config {config platform} {
   # Return appropriate array based on inputs
   switch $platform {
       top.VELOCE_TOP -
       top.VELOCE_TOP_AIC0 -
       top.VELOCE_TOP_LIGHT {
           switch $config {
               "default"    { array set clock_cfg $Axelera::clock_configs_default(top.VELOCE_TOP_COMMON)}
               "canonical"  { array set clock_cfg $Axelera::clock_configs_canonical(top.VELOCE_TOP_COMMON)}
               default      {error "Invalid config $config"}
           }
       }
       top.VELOCE_TOP_LIGHT_REAL_LPDDR {
           switch $config {
               "default"    { array set clock_cfg $Axelera::clock_configs_default($platform)}
               "canonical"  { array set clock_cfg $Axelera::clock_configs_canonical($platform)}
               default {error "Invalid config $config"}
           }
       }
       default {error "Invalid platform $platform"}
   }
   return [array get clock_cfg]
}



add_to_ax_procs "clock_print"
proc clock_print {{verbose 0}} {
  # print all clock frequency

  foreach {clock_name clock_info} [array get Axelera::clocks] {
    array set clock_info_arr $clock_info
    puts [format "%20s %10d %s" $clock_name $clock_info_arr(freq) $clock_info_arr(unit)]
  }
  if {$verbose} {
    velclockgen -info
  }
}


add_to_ax_procs "clock_set_freq"
proc clock_set_freq {clock_name freq unit} {
  # set a clock frequency

  array set clock_info_arr $Axelera::clocks($clock_name)
  velclockgen -set_freq $clock_info_arr(path) $freq $unit
  # update values in internal array
  set clock_info_arr(freq) $freq
  set clock_info_arr(unit) $unit
  set Axelera::clocks($clock_name) [array get clock_info_arr]
}


add_to_ax_procs "clock_set_config"
proc clock_set_config {config_name platform_name} {
  # set all clocks to a specific config
  # config_name: default, canonical
  # platform_name: top.VELOCE_TOP, top.VELOCE_TOP_AIC0, top.VELOCE_TOP_LIGHT, top.VELOCE_TOP_LIGHT_REAL_LPDDR

  array set clock_config_arr [get_clock_config $config_name $platform_name]
  foreach {clock_name clock_info} [array get clock_config_arr] {
    array set clock_info_arr $clock_info
    puts [format "%20s %10d %s" $clock_name $clock_info_arr(freq) $clock_info_arr(unit)]
    clock_set_freq $clock_name $clock_info_arr(freq) $clock_info_arr(unit)
  }

  clock_print
}
