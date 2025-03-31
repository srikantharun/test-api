--  --========================================================================--
--  (c)2014 ALLEGRO DVT
--  ----------------------------------------------------------------------------
--  $HeadURL$
--  $Author$
--  $Revision$
--  $LastChangedDate$
--  ----------------------------------------------------------------------------
--   Purpose : Synchronous FIFO
--  --========================================================================--
library ieee;
use ieee.std_logic_1164.all;
use ieee.std_logic_unsigned.all;
use ieee.numeric_std.all;
--------------------------------------------------------------------------------
entity alg_amba_vip_base_fifo is
--------------------------------------------------------------------------------
  generic (
    FIFO_WIDTH        : integer := 16;
    FIFO_LOG2_DEPTH   : integer := 4
  );
  port (
    -- asynchronous reset
    clk               : in  std_logic;
    rstn              : in  std_logic;
    -- write interface
    wreq              : in  std_logic;
    wdata             : in  std_logic_vector((FIFO_WIDTH - 1)  downto 0);
    wfull             : out std_logic;
    -- read interface
    rreq              : in  std_logic;
    rdata             : out std_logic_vector((FIFO_WIDTH - 1)  downto 0);
    rvalid            : out std_logic;
    rempty            : out std_logic
  );
end alg_amba_vip_base_fifo;
--------------------------------------------------------------------------------
architecture rtl of alg_amba_vip_base_fifo is
--------------------------------------------------------------------------------
  type t_array is array (0 to 2**FIFO_LOG2_DEPTH - 1) of std_logic_vector(FIFO_WIDTH - 1 downto 0);
  signal mem   : t_array;
--------------------------------------------------------------------------------
  type t_array_buffout is array (0 to 1) of std_logic_vector(FIFO_WIDTH - 1  downto 0);
--------------------------------------------------------------------------------
  signal i_buff_in_use              : std_logic;
  signal i_buff_in_cnt              : std_logic;
  signal i_buff_in_data             : std_logic_vector(FIFO_WIDTH - 1  downto 0);
--------------------------------------------------------------------------------
  signal i_buff_out_cnt             : std_logic_vector(1 downto 0);
  signal i_buff_out_data            : t_array_buffout;
--------------------------------------------------------------------------------
  signal i_fifo_full                : std_logic;
  signal i_fifo_empty               : std_logic;
  signal i_fifo_wren                : std_logic;
  signal i_fifo_cnt                 : std_logic_vector(FIFO_LOG2_DEPTH     downto 0);
  signal i_fifo_wraddr              : std_logic_vector(FIFO_LOG2_DEPTH - 1 downto 0);
  signal i_fifo_wdata               : std_logic_vector(FIFO_WIDTH - 1  downto 0);
  signal i_fifo_rden                : std_logic;
  signal i_fifo_rden_ff             : std_logic;
  signal i_fifo_rdaddr              : std_logic_vector(FIFO_LOG2_DEPTH - 1 downto 0);
  signal i_fifo_rdata               : std_logic_vector(FIFO_WIDTH - 1  downto 0);
--------------------------------------------------------------------------------
  signal i_rcnt                     : std_logic_vector(1 downto 0);
--------------------------------------------------------------------------------
  signal i_ram_wren                 : std_logic;
  signal i_ram_waddr                : std_logic_vector(FIFO_LOG2_DEPTH - 1 downto 0);
  signal i_ram_wdata                : std_logic_vector(FIFO_WIDTH - 1  downto 0);
  signal i_ram_rden                 : std_logic;
  signal i_ram_rdenff               : std_logic;
  signal i_ram_raddr                : std_logic_vector(FIFO_LOG2_DEPTH - 1 downto 0);
  signal i_ram_rdataz               : std_logic_vector(FIFO_WIDTH - 1  downto 0);
  signal i_ram_rdata                : std_logic_vector(FIFO_WIDTH - 1  downto 0);
--------------------------------------------------------------------------------
  signal i_max_depth                : std_logic_vector(FIFO_LOG2_DEPTH     downto 0);
--------------------------------------------------------------------------------
  -- max fifo depth (zero means physical depth)
  signal max_depth         : std_logic_vector(FIFO_LOG2_DEPTH     downto 0);
  -- max fifo depth for the signal wfull only  (zero means to ignore this signal)
  signal max_full          : std_logic_vector(FIFO_LOG2_DEPTH     downto 0);
--------------------------------------------------------------------------------
begin
-- Unused input (set as internal for now)
max_depth         <= (others => '0');
max_full          <= (others => '0');
--------------------------------------------------------------------------------
wfull  <= '1' when (i_fifo_cnt >= max_full and max_full > 0) or 
                    i_fifo_full = '1'                        or 
                   (i_buff_in_cnt = '1' and i_buff_in_use = '0') 
             else '0';
--------------------------------------------------------------------------------
rdata  <= i_buff_out_data(1);
rvalid <= '0' when i_buff_out_cnt="00" else '1';
rempty <= '0' when (i_fifo_cnt > 0) or wreq = '1' else '1';
--------------------------------------------------------------------------------
process(clk)
begin
  if rising_edge(clk) then
    if rstn='0' then
      i_buff_in_cnt       <= '0';
      i_buff_in_data      <= (others => '0');
      i_fifo_cnt          <= (others => '0');
    else

      if wreq = '1' and rreq = '0' then
        i_fifo_cnt        <= i_fifo_cnt + '1';
      elsif wreq = '0' and rreq = '1' then
        i_fifo_cnt        <= i_fifo_cnt - '1';
      end if;

      if wreq='1' then
        i_buff_in_cnt     <= '1';
        i_buff_in_data    <= wdata;
      elsif i_buff_in_use='1' then
        i_buff_in_cnt     <= '0';
      end if;
    end if;
  end if;
end process;
--------------------------------------------------------------------------------
i_buff_in_use <= i_fifo_wren;
--------------------------------------------------------------------------------
i_fifo_wdata <= i_buff_in_data;
i_fifo_wren  <= i_buff_in_cnt and (not i_fifo_full);
--------------------------------------------------------------------------------
i_fifo_full  <= '1' when (i_fifo_wraddr =  i_fifo_rdaddr - '1')                       or
                         (i_fifo_cnt    >= max_depth and max_depth > 0)               
                       else '0';
i_fifo_empty <= '1' when i_fifo_wraddr = i_fifo_rdaddr       else '0';
--------------------------------------------------------------------------------
process (clk)
begin
  if rising_edge(clk) then
    if rstn='0' then
      i_fifo_wraddr   <= (others => '0');
      i_fifo_rdaddr   <= (others => '0');
      i_max_depth     <= (others => '0');
    else
      i_max_depth    <= max_depth;
      if max_depth /= i_max_depth then
        i_fifo_rdaddr <= (others => '0');
        i_fifo_wraddr <= (others => '0');
      else
        if i_fifo_rden='1' then
          if i_fifo_rdaddr=(max_depth - 1) then
            i_fifo_rdaddr <= (others => '0');
          else
            i_fifo_rdaddr <= i_fifo_rdaddr + '1';
          end if;
        end if;

        if i_fifo_wren='1' then
          if i_fifo_wraddr=(max_depth - 1) then
            i_fifo_wraddr <= (others => '0');
          else
            i_fifo_wraddr <= i_fifo_wraddr + '1';
          end if;
        end if;
      end if;
    end if;
  end if;
end process;
--------------------------------------------------------------------------------
i_fifo_rden <= (not i_fifo_empty) when (rreq='1' or i_rcnt(1)='0') else '0';
--------------------------------------------------------------------------------
process(clk)
variable v_incr : std_logic;
begin
  if rising_edge(clk) then
    if rstn='0' then
      i_rcnt    <= (others => '0');
    else
      if i_fifo_rden='1' and rreq='0' then
        i_rcnt  <= i_rcnt + '1';
      elsif i_fifo_rden='0' and rreq='1' then
        i_rcnt  <= i_rcnt - '1';
      end if;
    end if;
  end if;
end process;
--------------------------------------------------------------------------------
process(clk)
begin
  if rising_edge(clk) then
    if rstn='0' then
      i_fifo_rden_ff      <= '0';
      i_buff_out_cnt      <= (others => '0');
      i_buff_out_data         <= (others => (others => '0'));
    else
      i_fifo_rden_ff      <= i_fifo_rden;

      if i_fifo_rden_ff='1' then
        if rreq='1' or i_buff_out_cnt="00" then
          i_buff_out_data(1)  <= i_fifo_rdata;
          i_buff_out_cnt      <= "01";
        else
          i_buff_out_data(0)  <= i_fifo_rdata;
          i_buff_out_cnt      <= "10";
        end if;
      elsif rreq='1' and i_buff_out_cnt/="00" then
        i_buff_out_data(1)    <= i_buff_out_data(0);
        i_buff_out_data(0)    <= (others => '0');
        i_buff_out_cnt        <= i_buff_out_cnt - '1';
      end if;
    end if;
  end if;
end process;
--------------------------------------------------------------------------------
i_ram_wren  <= i_fifo_wren;
i_ram_waddr <= i_fifo_wraddr;
i_ram_wdata <= i_fifo_wdata;
i_ram_rden  <= i_fifo_rden;
i_ram_raddr <= i_fifo_rdaddr;
--------------------------------------------------------------------------------
i_fifo_rdata <= i_ram_rdata;
--------------------------------------------------------------------------------
  process (clk)
  begin
    if rising_edge(clk) then
      if ( i_ram_wren = '1' ) then
        mem(conv_integer(i_ram_waddr)) <= i_ram_wdata;
      end if;
    end if;
  end process;
--------------------------------------------------------------------------------
  process (clk)
  begin
    if rising_edge(clk) then
      if ( i_ram_rden = '1' ) then
        i_ram_rdataz <= mem(conv_integer(i_ram_raddr));
      end if;
      i_ram_rdenff <= i_ram_rden;
    end if;
  end process;
--------------------------------------------------------------------------------
  i_ram_rdata <= i_ram_rdataz when ( i_ram_rdenff = '1' ) else (others => 'Z');
--------------------------------------------------------------------------------
end rtl;
--------------------------------------------------------------------------------
