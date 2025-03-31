// (C) Copyright Axelera AI 2024
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description:
// SV Delay block
// Adds delay to a req/gnt handshake
// - drops gnt for n cycles after an acceptance, once expired it raised gnt pending next req
// Owner: Andrew Bond

module axe_gnt (input bit clk, input bit rst_n, input bit req, output bit gnt);

  typedef struct {
    int unsigned min;
    int unsigned max;
    int unsigned weight;
  } gnt_range_t;

  int unsigned  rate       = 0;
  int unsigned  n_ranges   = 0;
  gnt_range_t   ranges[4];
  int unsigned  cnt        = 0;


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
      cnt <= get_next_delay();
    end
    else begin
      if (req && gnt) begin
         cnt <=  get_next_delay();
      end
      else begin
        if (cnt > 0)
          cnt <= cnt - 1;
      end
    end
  end

  always_comb gnt = (cnt == 0);

endmodule : axe_gnt
