--  --========================================================================--
--  (c)2014 ALLEGRO DVT
--  ----------------------------------------------------------------------------
--  $HeadURL$
--  $Author$
--  $Revision$
--  $LastChangedDate$
--  ----------------------------------------------------------------------------
--   Purpose : Shift register
--  --========================================================================--
library ieee;
use ieee.std_logic_1164.all;
use ieee.std_logic_unsigned.all;
use ieee.numeric_std.all;
--------------------------------------------------------------------------------
entity alg_amba_vip_base_delayline_channel_shift is
--------------------------------------------------------------------------------
  generic (
    FIFO_WIDTH          : integer := 16;
    FIFO_LOG2_DEPTH     : integer := 4
  );
  port (
    -- asynchronous reset
    clk                 : in  std_logic;
    rstn                : in  std_logic;
    --
    bypass              : in  std_logic;
    len_valid           : in  std_logic;
    len_value           : in  std_logic_vector(FIFO_LOG2_DEPTH - 1 downto 0);
    -- write interface
    wreq                : in  std_logic;
    wdata               : in  std_logic_vector((FIFO_WIDTH - 1)  downto 0);
    wfull               : out std_logic;
    -- read interface
    rreq                : in  std_logic;
    rdata               : out std_logic_vector((FIFO_WIDTH - 1)  downto 0);
    rvalid              : out std_logic
  );
end alg_amba_vip_base_delayline_channel_shift;
--------------------------------------------------------------------------------
architecture rtl of alg_amba_vip_base_delayline_channel_shift is
--------------------------------------------------------------------------------
  type t_array_data  is array(0 to (2**FIFO_LOG2_DEPTH - 1)) of std_logic_vector(FIFO_WIDTH downto 0);
  signal s_array      : t_array_data := (others => (others => '0'));
--------------------------------------------------------------------------------
  attribute syn_ramstyle : string;
  attribute syn_ramstyle of s_array : signal is "no_rw_check";
--------------------------------------------------------------------------------
  signal step_en      : std_logic;
  signal wptr         : std_logic_vector(FIFO_LOG2_DEPTH - 1 downto 0);
  signal i_blocked    : std_logic;
  signal i_rvalid     : std_logic;
  signal i_rdata      : std_logic_vector(FIFO_WIDTH  downto 0);
  signal len_cur      : std_logic_vector(FIFO_LOG2_DEPTH - 1 downto 0);
  signal i_wren       : std_logic;
--------------------------------------------------------------------------------
begin
--------------------------------------------------------------------------------
p_ptr : process (clk)
--------------------------------------------------------------------------------
begin
  if rising_edge(clk) then
    if (rstn = '0') then
      len_cur     <= (others => '0');
      wptr        <= (others => '0');
    else
      if bypass = '1' then
        wptr      <= (others => '0');
      elsif len_valid = '1' then
        len_cur   <= len_value;
        wptr      <= (others => '0');
      elsif (wptr = len_cur and step_en = '1') then
        wptr      <= (others => '0');
      else
        wptr      <= wptr + step_en;
      end if;
    end if;
  end if;
end process p_ptr;
--------------------------------------------------------------------------------
-- internal
i_blocked   <= '1' when i_rvalid = '1' and rreq = '0' else '0';
i_rvalid    <= i_rdata(FIFO_WIDTH);
step_en     <= not(i_blocked);
-- outputs
rdata       <= i_rdata(FIFO_WIDTH - 1 downto 0);
rvalid      <= i_rvalid;
wfull       <= i_blocked;
--------------------------------------------------------------------------------
-- There is no reset on the FIFO memory because this is better for FPGA synthesis.
-- TODO: can cause issue on fpga because i_rvalid could be at '1'
--------------------------------------------------------------------------------
i_wren <= step_en and not bypass;
--------------------------------------------------------------------------------
p_data : process (clk)
--------------------------------------------------------------------------------
begin
  if rising_edge(clk) then
    if (i_wren='1') then
      s_array(conv_integer(wptr((FIFO_LOG2_DEPTH -1) downto 0))) <= wreq&wdata;
    end if;
  end if;
end process p_data;
--------------------------------------------------------------------------------
process(rstn, clk)
begin
  if rstn='0' then
    i_rdata <= (others => '0');
  elsif rising_edge(clk) then
    if (step_en='1') then
      if i_wren='1' then
        i_rdata <= s_array(conv_integer(wptr((FIFO_LOG2_DEPTH -1) downto 0)));
      else -- bypass
        i_rdata <= wreq&wdata;
      end if;
    end if;
  end if;
end process;
--------------------------------------------------------------------------------
end rtl;
--------------------------------------------------------------------------------
