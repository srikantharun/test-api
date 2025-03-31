// (C) Copyright Axelera AI 2024
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description:
// SV Delay block
// Maintains order while adding random delay
// Owner: Andrew Bond

module axe_delay #(
  parameter type type_t    = bit
)
(input bit clk, input bit rst_n, input type_t inp, output type_t oup);

  typedef struct {
    int unsigned min;
    int unsigned max;
    int unsigned weight;
  } delay_range_t;

  int unsigned  rate       = 0;
  int unsigned  next_delay = 0;
  int unsigned  n_ranges   = 0;
  delay_range_t ranges[4];
  type_t        data[$];
  type_t        oup_r;
  bit           bypass;

  initial begin
    for (int i = 0 ; i < 4; i++) begin
      ranges[i].min    = 0;
      ranges[i].max    = 0;
      ranges[i].weight = 0;
    end
  end

  function void add_range(int unsigned min, int unsigned max, int unsigned weight);

    ranges[n_ranges].min    = min;
    ranges[n_ranges].max    = max;
    ranges[n_ranges].weight = weight;

    n_ranges += 1;
    assert(n_ranges < 4);
    assert(weight   > 0);
  endfunction : add_range

  function void add_rate(int r);
    rate = r;
    assert(rate  > 0);
    assert(rate <= 100);
  endfunction : add_rate

  function automatic int unsigned get_next_delay();
    get_next_delay = 0;

    if (rate == 0) begin
      // Range / distbribution based approach
      randcase
        ranges[0].weight : get_next_delay =  $urandom_range(ranges[0].max, ranges[0].min);
        ranges[1].weight : get_next_delay =  $urandom_range(ranges[1].max, ranges[1].min);
        ranges[2].weight : get_next_delay =  $urandom_range(ranges[2].max, ranges[2].min);
        ranges[3].weight : get_next_delay =  $urandom_range(ranges[3].max, ranges[3].min);
      endcase
    end
    else begin
      // Rate based approach
      int unsigned r;

      get_next_delay = -1;
      do begin
        get_next_delay += 1;
        r = $urandom_range(100, 0);
      end while (r > rate);
    end

  endfunction : get_next_delay

  always @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      data.delete();
      next_delay <= get_next_delay();
      oup_r      <= '0;
    end
    else begin
      if (data.size() != 0)
        void'(data.pop_front());

      if (|inp && !bypass) begin
        for (int i = 0; i < next_delay; i++) begin
          data.push_back('0);
        end
        data.push_back(inp);
        next_delay <= get_next_delay();
      end 

      if (data.size() != 0)
        oup_r <= data[0];
      else
        oup_r <= '0;
    end
  end

  always_comb bypass = (next_delay == 0) && (data.size() == 0);
  always_comb oup    = (bypass) ? inp : oup_r;

endmodule : axe_delay
