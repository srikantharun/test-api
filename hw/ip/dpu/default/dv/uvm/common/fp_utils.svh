`ifndef GUARD_FP_UTILS_SV
`define GUARD_FP_UTILS_SV


//************************************************************************************************
//************************************************************************************************
//************************************************************************************************

//IMPORTANT: The conversion between floating points are following the rules define in MR 321

//************************************************************************************************
//************************************************************************************************
//************************************************************************************************
//exponent and faction width set to binary32 just because it's the largest
//fp used in this class
typedef struct packed {
  bit sign;
  bit [7:0] exponent;
  bit [22:0] fraction;
  
  bit [31:0] a_frac_mask;
  bit [31:0] b_frac_mask;
  bit [31:0] a_exp_bias;
  bit [31:0] b_exp_bias;
  bit [31:0] a_frac_size;
  bit [31:0] b_frac_size;
  bit [31:0] a_exp_mask;
  bit [31:0] b_exp_mask;
  bit [31:0] half_frac;
  bit [31:0] int_size;
  bit [31:0] max_val;
  bit [47:0] out_res;
  bit overflow;
  bit underflow;
  bit round_error;
  bit use_sign;
} fp_t;


typedef enum {
  FP_16, FP_18, FP_24, FP_32, INT_8, INT_16, INT_32, INT_48
} convert_type_t;

typedef struct {
  bit overflow;
  bit underflow;
  bit round_error;
  bit [PWORD_SIZE-1:0][17:0] packed_dt;
} fp18_converted_t;

typedef struct {
  bit overflow;
  bit underflow;
  bit round_error;
  bit [PWORD_SIZE-1:0][15:0] packed_dt;
} fp16_converted_t;

typedef struct {
  bit overflow;
  bit underflow;
  bit round_error;
  bit [PWORD_SIZE-1:0][23:0] packed_dt;
} fp24_converted_t;

typedef struct {
  bit overflow;
  bit underflow;
  bit round_error;
  bit [PWORD_SIZE-1:0][31:0] packed_dt;
} fp32_converted_t;

typedef struct {
  bit overflow;
  bit underflow;
  bit round_error;
  bit [PWORD_SIZE-1:0][7:0] packed_dt;
} int8_converted_t;

typedef struct {
  bit overflow;
  bit underflow;
  bit round_error;
  bit [PWORD_SIZE-1:0][15:0] packed_dt;
} int16_converted_t;

class fp_utils ;
  localparam MATH_LN2 = 0.693147180559945309417;
  typedef bit [PWORD_SIZE-1:0] [OUT_WORD_DW-1:0] out_words_t;
  
/*
  `define convert_pword(a,b,a_width,b_width,a_type, b_type) \
    function bit [PWORD_SIZE-1:0][``a_width-1:0] convert_pword_``a``_to_``b`` (bit [PWORD_SIZE-1:0][``a_width``-1:0] dt, bit use_sign); \
      bit [PWORD_SIZE-1:0][``b_width``-1:0] res; \
      for (int i = 0; i < PWORD_SIZE; i ++ )  \
        res[i] = convert(dt[i], ``a_type``, ``b_type``, use_sign); \
      return res; \ 
    endfunction 
*/

  function fp18_converted_t convert_pword32_int48_to_f18 (bit [PWORD_SIZE-1:0][31:0] dt, bit use_sign);
    fp_t f;
    fp18_converted_t res;
    for (int i = 0, j = 0; i < PWORD_SIZE; i+=2,j++ ) begin
      f                = convert({dt[i+1][15:0], dt[i]} , INT_48, FP_18, use_sign);
      res.packed_dt[j] = f.out_res;
      res.overflow     = f.overflow ? 1 : res.overflow;
      res.underflow    = f.underflow ? 1 : res.underflow;
      res.round_error  = f.round_error ? 1 : res.round_error;
      $display("converting: [%0d] %0h, res: %0h",j, {dt[i+1][15:0], dt[i]}, res.packed_dt[j]);
    end
    return res;
  endfunction

  function fp18_converted_t convert_pword_int32_to_f18 (bit [PWORD_SIZE-1:0][31:0] dt, bit use_sign);
    fp_t f;
    fp18_converted_t res;
    for (int i = 0; i < PWORD_SIZE; i++ ) begin
      f                = convert(dt[i], INT_32, FP_18, use_sign);
      res.packed_dt[i] = f.out_res;
      res.overflow     = f.overflow ? 1 : res.overflow;
      res.underflow    = f.underflow ? 1 : res.underflow;
      res.round_error  = f.round_error ? 1 : res.round_error;
    end
    return res;
  endfunction

  function fp18_converted_t convert_pword32_int16_to_f18 (bit [PWORD_SIZE-1:0][7:0] dt, bit use_sign, bit vm);
    fp_t f;
    fp18_converted_t res;

    if (vm) begin
      for (int i = 0, j = 0; i < PWORD_SIZE; i+=2, j++) begin
        f                = convert({dt[i+1],dt[i]}, INT_16, FP_18, use_sign);
        res.packed_dt[j] = f.out_res;
        res.overflow     = f.overflow ? 1 : res.overflow;
        res.underflow    = f.underflow ? 1 : res.underflow;
        res.round_error  = f.round_error ? 1 : res.round_error;
      end
    end
    else begin
      for (int i = 0; i < PWORD_SIZE; i++ ) begin
        f                = convert(dt[i], INT_16, FP_18, use_sign);
        res.packed_dt[i] = f.out_res;
        res.overflow     = f.overflow ? 1 : res.overflow;
        res.underflow    = f.underflow ? 1 : res.underflow;
        res.round_error  = f.round_error ? 1 : res.round_error;
      end
    end
    return res;
  endfunction

  function fp18_converted_t convert_pword_int8_to_f18 (bit [PWORD_SIZE-1:0][7:0] dt, bit use_sign);
    fp_t f;
    fp18_converted_t res;
    for (int i = 0; i < PWORD_SIZE; i++ ) begin
      f                = convert(dt[i], INT_8, FP_18, use_sign);
      res.packed_dt[i] = f.out_res;
      res.overflow     = f.overflow ? 1 : res.overflow;
      res.underflow    = f.underflow ? 1 : res.underflow;
      res.round_error  = f.round_error ? 1 : res.round_error;
    end
    return res; 
  endfunction

  function fp18_converted_t convert_pword_f32_to_f18 (bit [QUARTER_PWORD_SIZE-1:0][31:0] dt, bit use_sign);
    fp_t f;
    fp18_converted_t res;
    for (int i = 0; i < QUARTER_PWORD_SIZE; i++ ) begin
      f                = convert(dt[i], FP_32, FP_18, use_sign);
      res.packed_dt[i] = f.out_res;
      res.overflow     = f.overflow ? 1 : res.overflow;
      res.underflow    = f.underflow ? 1 : res.underflow;
      res.round_error  = f.round_error ? 1 : res.round_error;
    end
    return res; 
  endfunction

  function fp18_converted_t convert_pword_f24_to_f18 (bit [QUARTER_PWORD_SIZE-1:0][23:0] dt, bit use_sign);
    fp_t f;
    fp18_converted_t res;
    for (int i = 0; i < QUARTER_PWORD_SIZE; i++ ) begin
      f                = convert(dt[i], FP_24, FP_18, use_sign);
      res.packed_dt[i] = f.out_res;
      res.overflow     = f.overflow ? 1 : res.overflow;
      res.underflow    = f.underflow ? 1 : res.underflow;
      res.round_error  = f.round_error ? 1 : res.round_error;
    end
    return res; 
  endfunction

  function fp18_converted_t convert_pword_f16_to_f18 (bit [HALF_PWORD_SIZE-1:0][15:0] dt, bit use_sign);
    fp_t f;
    fp18_converted_t res;
    for (int i = 0; i < HALF_PWORD_SIZE; i++ ) begin
      f                = convert(dt[i], FP_16, FP_18, use_sign);
      res.packed_dt[i] = f.out_res;
      res.overflow     = f.overflow ? 1 : res.overflow;
      res.underflow    = f.underflow ? 1 : res.underflow;
      res.round_error  = f.round_error ? 1 : res.round_error;
    end
    return res; 
  endfunction

  function int8_converted_t convert_pword_f18_to_int8(bit [PWORD_SIZE-1:0][17:0] f18, bit use_sign);
    fp_t f;
    int8_converted_t res; 
    foreach (f18[i]) begin
      f = convert(f18[i], FP_18, INT_8, use_sign);
      res.packed_dt[i] = f.out_res;
      res.overflow     = f.overflow ? 1 : res.overflow;
      res.underflow    = f.underflow ? 1 : res.underflow;
      res.round_error  = f.round_error ? 1 : res.round_error;
    end
    return res; 
  endfunction

  function int16_converted_t convert_pword_f18_to_int16(bit [PWORD_SIZE-1:0][17:0] f18, bit use_sign);
    fp_t f;
    int16_converted_t res; 
    foreach (f18[i]) begin
      f = convert(f18[i], FP_18, INT_16, use_sign);
      res.packed_dt[i] = f.out_res;
      res.overflow     = f.overflow ? 1 : res.overflow;
      res.underflow    = f.underflow ? 1 : res.underflow;
      res.round_error  = f.round_error ? 1 : res.round_error;
    end
    return res; 
  endfunction

  function fp16_converted_t convert_pword_f18_to_f16(bit [PWORD_SIZE-1:0][17:0] f18, bit use_sign);
    fp_t f;
    fp16_converted_t res;
    foreach (f18[i]) begin 
      f                = convert(f18[i], FP_18, FP_16,use_sign);
      res.packed_dt[i] = f.out_res;
      res.overflow     = f.overflow ? 1 : res.overflow;
      res.underflow    = f.underflow ? 1 : res.underflow;
      res.round_error  = f.round_error ? 1 : res.round_error;
    end
    return res;
  endfunction

  function fp24_converted_t convert_pword_f18_to_f24(bit [PWORD_SIZE-1:0][17:0] f18, bit use_sign);
    fp_t f;
    fp24_converted_t res;
    foreach (f18[i]) begin 
      f                = convert(f18[i], FP_18, FP_24,use_sign);
      res.packed_dt[i] = f.out_res;
      res.overflow     = f.overflow ? 1 : res.overflow;
      res.underflow    = f.underflow ? 1 : res.underflow;
      res.round_error  = f.round_error ? 1 : res.round_error;
    end
    return res;
  endfunction

  function fp32_converted_t convert_pword_f18_to_f32(bit [PWORD_SIZE-1:0][17:0] f18, bit use_sign);
    fp_t f;
    fp32_converted_t res;
    foreach (f18[i]) begin 
      f                = convert(f18[i], FP_18, FP_32,use_sign);
      res.packed_dt[i] = f.out_res;
      res.overflow     = f.overflow ? 1 : res.overflow;
      res.underflow    = f.underflow ? 1 : res.underflow;
      res.round_error  = f.round_error ? 1 : res.round_error;
    end
    return res;
  endfunction


  function out_words_t convert_pword_f18_to_int8_bp(bit [PWORD_SIZE-1:0][17:0] f18);
    bit [PWORD_SIZE-1:0][7:0] int8_word;
    foreach (f18[i]) 
      int8_word[i] = f18[i][7:0]; 
    return int8_word;
  endfunction

  function out_words_t convert_pword_f18_to_int16_bp(bit [PWORD_SIZE-1:0][17:0] f18);
    bit [PWORD_SIZE-1:0][15:0] int16_word;
    foreach (f18[i]) 
      int16_word[i] = f18[i][15:0]; 
    return int16_word;
  endfunction

   
  function fp_t convert(bit [DPU_PWORD_BIT_MAX-1:0] val,convert_type_t a, convert_type_t b, bit use_sign);
    fp_t fp;
    fp_t fp_out;
    fp_t out;

    if (a >= INT_8 && b >= INT_8) begin
      $error("Error! Illegal convertion: int to int");
      return 0;
    end
    fp.use_sign = use_sign;
    //organize val to correct float point format according convert_type    
    if (a == FP_16) begin
      fp.sign        = val[15];
      fp.exponent    = val[14:10];
      fp.fraction    = val[9:0];
      fp.a_frac_mask = {10{1'b1}};
      fp.a_frac_size = 10;
      fp.a_exp_mask  = {5{1'b1}};
      fp.a_exp_bias  = 15;
    end
    else if (a == FP_18) begin
      fp.sign        = val[17];
      fp.exponent    = val[16:10];
      fp.fraction    = val[9:0];
      fp.a_frac_mask = {10{1'b1}};
      fp.a_frac_size = 10;
      fp.a_exp_mask  = {7{1'b1}};
      fp.a_exp_bias  = 63;
    end
    else if (a == FP_24) begin
      fp.sign        = val[23];
      fp.exponent    = val[22:15];
      fp.fraction    = val[14:0];
      fp.a_frac_mask = {15{1'b1}};
      fp.a_frac_size = 15;
      fp.a_exp_mask  = {8{1'b1}};
      fp.a_exp_bias  = 127;
    end
    else if (a == FP_32) begin
      fp.sign        = val[31];
      fp.exponent    = val[30:23];
      fp.fraction    = val[22:0];
      fp.a_frac_mask = {23{1'b1}};
      fp.a_frac_size = 23;
      fp.a_exp_mask  = {8{1'b1}};
      fp.a_exp_bias  = 127;
    end
    else if (a >= INT_8)
      fp.int_size = a == INT_16 ? 16 : (a == INT_8 ? 8 :  (a == INT_32 ? 32 : 48));

    if (b == FP_16) begin
      fp.b_frac_mask = {10{1'b1}};
      fp.b_exp_bias  = 15;
      fp.b_frac_size = 10;
      fp.b_exp_mask  = {5{1'b1}};
    end
    else if (b == FP_18) begin
      fp.b_frac_mask = {10{1'b1}};
      fp.b_exp_bias  = 63;
      fp.b_frac_size = 10;
      fp.b_exp_mask  = {7{1'b1}};
    end
    else if (b == FP_24) begin
      fp.b_frac_mask = {15{1'b1}};
      fp.b_exp_bias  = 127;
      fp.b_frac_size = 15;
      fp.b_exp_mask  = {8{1'b1}};
    end
    else if (b == FP_32) begin
      fp.b_frac_mask = {23{1'b1}};
      fp.b_exp_bias  = 127;
      fp.b_frac_size = 23;
      fp.b_exp_mask  = {8{1'b1}};
    end
    else if (b >= INT_8)
      fp.int_size = b == INT_16 ? 16 : (b == INT_8 ? 8 : 32);
                           
    if (a > b)
      fp.half_frac = fp.a_frac_size - fp.b_frac_size;
    else
      fp.half_frac = fp.b_frac_size - fp.a_frac_size;
    
    if (a >= INT_8)
      fp_out = convert_int_to_float(val,fp);
    else if (b >= INT_8)
      fp_out = convert_float_to_int(fp);
    else if (a > b)
      fp_out = convert_float_large_to_small(fp);
    else
      fp_out =convert_float_small_to_large(fp);
   
    case (b)
      INT_8 : begin
        out.out_res[7:0] = fp_out.out_res;
      end
      INT_32 : begin
        out.out_res = fp_out.out_res;
      end
      FP_16: begin
        out.out_res[15]    = fp_out.sign;
        out.out_res[14:10] = fp_out.exponent;
        out.out_res[9:0]   = fp_out.fraction;
      end
      FP_18: begin
        out.out_res[17]    = fp_out.sign;
        out.out_res[16:10] = fp_out.exponent;
        out.out_res[9:0]   = fp_out.fraction;
      end
      FP_32: begin
        out.out_res[31]    = fp_out.sign;
        out.out_res[30:23] = fp_out.exponent;
        out.out_res[22:0]  = fp_out.fraction;
      end
    endcase
    out.overflow    = fp_out.overflow;
    out.underflow   = fp_out.underflow;
    out.round_error = fp_out.round_error;
    return out;
                           
  endfunction : convert
 
  function fp_t convert_float_large_to_small(fp_t a);
    fp_t b;

    //negative numbers and ignore signal, return 0
    if (a.sign && !a.use_sign) return 0; 

    //round-to-nearest-even
    //a.fraction = a.fraction + (1'b1 << (a.half_frac-1));
    b.sign = a.sign;
    b.fraction = a.fraction >> a.half_frac;
    //exp = 0 : subnormal numbers or zero
    //exp > 0 : normal numbers
    if (a.exponent > 0) begin
      //exponent enconding
      int exp = $signed(a.exponent - a.a_exp_bias);
      //-/+ infinity or NaN
      if (exp  > $signed(a.b_exp_bias))  begin
        b.overflow = 1;
        b.exponent = 'hFFFFFFFF;
        b.fraction = 0;
      end 
      //underflow
      else if (exp < $signed(1 - a.b_exp_bias)) begin
        b.underflow = 1;
        b.exponent = 0;
        b.fraction = 0;
      end
      else
        b.exponent = (a.exponent - a.a_exp_bias + a.b_exp_bias); 
    end
    else b.fraction = 0;
    return b;
  endfunction
  

  function fp_t convert_float_small_to_large(fp_t b);
    fp_t a;  

    a.sign = b.sign; 
//    //adjust exponent by subtracting smaller fp exp bias and add larger exp bias
 //   a.exponent = b.exponent - b.b_exp_bias + b.a_exp_bias;
 //   //extend fraction to match larger fp bits
 //   a.fraction = b.fraction << b.half_frac; 

    


    /*if (b.exponent == 0) begin
      if (b.fraction > 0) begin
        b.exponent = b.a_exp_bias - (b.b_exp_bias -1);
        while ((b.fraction & (1 << b.b_frac_size)) == 0) begin
          b.exponent--;
          b.fraction <<= 1;
        end
        a.exponent = b.exponent;
        a.fraction = b.fraction << b.half_frac;  
      end          
    end
    */
    //+/- infinity or NaN
    //else if (b.exponent == b.b_exp_mask) begin

    //Following rules based on: MR321
    if (b.exponent == 0) begin
      a.underflow   = 1;
      a.round_error = 1;
      return a;
    end 

    if (b.exponent == b.b_exp_mask) begin
      a.exponent = 'hFFFFFFFF;
      a.fraction = b.fraction << b.half_frac;
    end
    //normal numbers 
    else begin
      if (b.exponent != 0)
        a.exponent = b.exponent + (b.b_exp_bias - b.a_exp_bias);
      a.fraction = b.fraction << b.half_frac;
    end
    return a;
  endfunction
 

  function fp_t convert_float_to_int (fp_t fp);
    fp_t fp_out;
    bit [32:0] out;
    real res;
    bit sign = fp.use_sign && fp.sign;
    //negative numbers and ignore signal, return 0
    if (fp.sign && !fp.use_sign) return 0; 
    if (fp.exponent == 0) return 0;
    
    res = 2.0 ** (int'(fp.exponent) - int'(fp.a_exp_bias)) * (1 + fp.fraction/2.0**fp.a_frac_size);
    //RNE method
    if (res - $floor(res) == 0.5 && int'($floor(res)) % 2 == 0)
      out = int'($floor(res));
    else
      out = int'(res);
    if (res > (fp.use_sign ? 2 ** (fp.int_size -1) : 2 ** fp.int_size) - 1) begin
      fp_out.overflow = 1;
      if (sign) 
        out = fp.int_size == 8 ? 8'h80 : (fp.int_size == 16 ? 16'h8000 : 32'h8000_0000);
      else if (fp.use_sign && !sign)
        out = fp.int_size == 8 ? 7'h7F : (fp.int_size == 16 ? 16'h7FFF : 31'h7FFF_FFFF);
      else out = 'hFFFF_FFFF;
    end

    if (sign)
      out = ~out + 1; 
    fp_out.out_res = out;
    return fp_out;
  endfunction
  

  function fp_t convert_int_to_float (bit [47:0] int_val, fp_t fp);
    fp_t fp_out;
    int exp_unbiased; 
    int msb_index = -1;
    int int_size;
    convert_type_t a_type, b_type;

    if (fp.int_size == 8)
      a_type = INT_8;
    else if (fp.int_size == 16)
      a_type = INT_16;
    else if (fp.int_size == 32)
      a_type = INT_32;
    else
      a_type = INT_48;

    if (fp.b_exp_bias == 127) begin
      if (fp.b_frac_size == 23)
        b_type = FP_32;
      else
        b_type = FP_24;
    end
    else if (fp.b_exp_bias == 63)
      b_type = FP_18;
    else
      b_type = FP_16;

    fp_out.sign = fp.use_sign ? int_val[fp.int_size - 1] : 0;
    int_size = !fp.use_sign ? fp.int_size : fp.int_size -1;
    if (int_val == 0) return fp_out;

    if (fp_out.sign) 
      int_val = ~int_val + 1;


    for (int i = 0; i < int_size; i++) begin
      if (int_val[i] == 1)
        msb_index = i;
    end

    //no 1 identified, so int_val = most negative int
    if (msb_index == -1) begin
      msb_index = int_size;
    end
    fp_out.exponent[6:0] = int'(fp.b_exp_bias + msb_index);
    if (int'(fp.b_frac_size) - msb_index > 0) begin
      int_val <<= (fp.b_frac_size - msb_index);
      fp_out.fraction = int_val & fp.b_frac_mask;
    end
    //truncate
    else begin
      int rnd = (int_val >> (msb_index  - fp.b_frac_size - 1));
      fp_out.fraction = (int_val >> (msb_index  - fp.b_frac_size)) & fp.b_frac_mask; 
      if (fp.int_size inside {[32:48]} && fp.b_frac_size == 10 && rnd[0] == 1) fp_out.fraction++;
    end
    if (convert({fp_out.sign, fp_out.exponent, fp_out.fraction}, b_type, a_type, fp_out.sign) != int_val)
      fp_out.round_error = 1;
    return fp_out;
  endfunction


  function bit [17:0] convert_real_to_float18(real input_num);
    bit  sign;
    real abs_x;
    int exp, mant, mant_aux;
    real mant_real, exp_real;

    bit [17:0] fp18;

    if (input_num == 0.0) begin
      return 0;  // return 0 in float18
    end
  
    if (input_num < 0.0) begin
      sign  = 1;
      abs_x = -input_num;
    end else begin
      sign  = 0;
      abs_x = input_num;
    end

    if (abs_x < 2.1175823681357084e-22) begin//2.16840434497100886801490560174e-19) begin
      exp  = -63;
      mant = 0;
    end else if (abs_x > 1.844224047408218112e+19  ) begin
      exp  = 64;
      mant = 0;
    end else begin
      //subnormal values
      if (abs_x < 2.166286762602873117167234795488184318e-19)
        exp = -62;
      else
        exp = $floor($ln(abs_x) / MATH_LN2);
      mant_real = (abs_x / $pow(2, exp) - 1) * 1024;
      mant = $floor(mant_real);
      if (((mant_real - mant) == 0.5 && mant[0] == 1'b1) || (mant_real - mant) > 0.5) begin
        mant++;
      end
      if (mant == 1024) begin
        mant = 0;
        exp++;
      end
    end

    if (exp == -62) exp = 0;
    else exp += 63;

    fp18[17:17] = sign;
    fp18[16:10] = exp;
    fp18[9:0]   = mant;

    return fp18;
  endfunction


  function real convert_float18_to_real(bit [17:0] fp);
    real res;
    //exponent == 0
    if (fp[16:10] == 0)
      res = 2.0 ** -62 * (fp[9:0]/1024.0);
    else
      res = 2.0 ** (fp[16:10] - 63.0) * (1.0 + (fp[9:0]/1024.0));
    
    if (fp[17]) return -res;
    else        return res;
  endfunction


  //op = 0 : ADD
  //     1 : SUB
  //     2 : MUL
  function bit[17:0] fp18_op(bit [1:0] op, bit [17:0] a, b);
    //ADD
    if (op == 0) begin
      // Extract sign, exponent, and mantissa
      bit sign_a       = a[17];
      bit [6:0] exp_a  = a[16:10];
      bit [9:0] mant_a = a[9:0];

      bit sign_b       = b[17];
      bit [6:0] exp_b  = b[16:10];
      bit [9:0] mant_b = b[9:0];

      // Implicit leading 1 for normalized numbers
      bit [10:0] norm_mant_a = {1'b1, mant_a};
      bit [10:0] norm_mant_b = {1'b1, mant_b};

      // Align exponents
      bit [10:0] aligned_mant_a;
      bit [10:0] aligned_mant_b;
      bit [6:0] exp_diff;
      bit [6:0] exp_result;
      bit sign_result;
      bit [11:0] mant_result;
      bit [6:0] exp_final;
      bit [9:0] mant_final;
      if (exp_a > exp_b) begin
        exp_diff = exp_a - exp_b;
        aligned_mant_a = norm_mant_a;
        aligned_mant_b = norm_mant_b >> exp_diff;
        exp_result = exp_a;
        sign_result = sign_a;
      end else begin
        exp_diff = exp_b - exp_a;
        aligned_mant_a = norm_mant_a >> exp_diff;
        aligned_mant_b = norm_mant_b;
        exp_result = exp_b;
        sign_result = sign_b;
      end

      // Add/Subtract mantissas
      if (sign_a == sign_b) begin
        mant_result = aligned_mant_a + aligned_mant_b;
      end else begin
        if (aligned_mant_a > aligned_mant_b) begin
          mant_result = aligned_mant_a - aligned_mant_b;
          sign_result = sign_a;
        end else begin
          mant_result = aligned_mant_b - aligned_mant_a;
          sign_result = sign_b;
        end
      end

      // Normalize result
      if (mant_result[11]) begin
        mant_final = mant_result[11:2]; // shift mantissa right
        exp_final = exp_result + 1; // increase exponent
      end else begin
        mant_final = mant_result[9:0]; // no normalization needed
        exp_final = exp_result;
      end
      // Combine sign, exponent, and mantissa into the result
      return {sign_result, exp_final, mant_final};
    end
    //SUB
    else if (op == 1) begin
     // Extract sign, exponent, and mantissa of both inputs
      bit sign_a, sign_b;
      bit [9:0] mant_a, mant_b;
      bit [9:0] mant_a_shifted, mant_b_shifted;
      bit [10:0] mant_result;
      bit [6:0] exp_a, exp_b;
      bit [6:0] exp_diff;
      bit [6:0] exp_result;
      bit result_sign;
      
      sign_a = a[17];          // sign bit of A
      sign_b = b[17];          // sign bit of B
      exp_a = a[16:10];        // exponent of A
      exp_b = b[16:10];        // exponent of B
      mant_a = {1'b1, a[9:0]}; // implicit leading 1 for A
      mant_b = {1'b1, b[9:0]}; // implicit leading 1 for B

      // Align exponents by shifting mantissas
      
      if (exp_a > exp_b) begin
          exp_diff = exp_a - exp_b;
          mant_b_shifted = mant_b >> exp_diff;
          mant_a_shifted = mant_a;
      end else begin
          exp_diff = exp_b - exp_a;
          mant_a_shifted = mant_a >> exp_diff;
          mant_b_shifted = mant_b;
      end

      // Subtract mantissas
      if (mant_a_shifted >= mant_b_shifted) begin
          mant_result = mant_a_shifted - mant_b_shifted;
          result_sign = sign_a;  // result takes the sign of the larger number
      end else begin
          mant_result = mant_b_shifted - mant_a_shifted;
          result_sign = sign_b;
      end

      // Normalize result
      if (mant_result[10]) begin
          // No normalization needed
          exp_result = exp_a > exp_b ? exp_a : exp_b;
      end else begin
          // Normalize by shifting mantissa left
          exp_result = (exp_a > exp_b ? exp_a : exp_b) - 1;
          mant_result = mant_result << 1;
      end

      // Pack result back into 16-bit floating-point format
      return {result_sign, exp_result, mant_result[9:0]};
    end
    //MUL
    else begin
      // Extract sign, exponent, and fraction for both inputs
      bit sign_a, sign_b, sign_result;
      bit [6:0] exponent_a, exponent_b, exponent_result;
      bit [10:0] fraction_a, fraction_b, fraction_result;
      
      // Declare intermediate variables for mantissa multiplication and exponent addition
      bit [21:0] mantissa_mul;    // Intermediate result of mantissa multiplication
      bit [7:0]  exponent_sum;    // Intermediate result of exponent addition

      // Special constants for bias correction (15 for half precision)
      int bias = 63;

      // Split the inputs into sign, exponent, and fraction
      sign_a      = a[17];
      exponent_a  = a[16:10];
      fraction_a  = {1'b1, a[9:0]}; // Implicit 1 in IEEE format

      sign_b      = b[17];
      exponent_b  = b[16:10];
      fraction_b  = {1'b1, b[9:0]}; // Implicit 1 in IEEE format

      // Determine the sign of the result
      sign_result = sign_a ^ sign_b;

      // Perform mantissa (fraction) multiplication (22-bit product)
      mantissa_mul = fraction_a * fraction_b;

      // Add the exponents and subtract the bias
      exponent_sum = exponent_a + exponent_b - bias;

      // Normalize the result
      if (mantissa_mul[21]) begin
          // If there is an overflow in the mantissa, shift right and adjust exponent
          fraction_result = mantissa_mul[21:11]; // Normalized mantissa
          exponent_result = exponent_sum + 1;
      end else begin
          // Otherwise, take the mantissa as is
          fraction_result = mantissa_mul[20:10]; // Normalized mantissa
          exponent_result = exponent_sum;
      end

      // Combine the sign, exponent, and fraction to get the final result
      return {sign_result, exponent_result[4:0], fraction_result[9:0]};
    end

  endfunction



endclass
             
`endif
