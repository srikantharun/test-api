`ifndef IFDW_DECOMPRESSION_SEQ_ITEM
`define IFDW_DECOMPRESSION_SEQ_ITEM

/*
Decompression sequence item
this class creates a decompression sequence, the following way:
it receives/randomizes sequence length, then decides how many zero lines there will be, and at which indexes
next it creates the uncompressed data - putting zeroes at the zero indexes, and for the rest randomizing data, in a way that will ensure zeroes appear enoguh inside the lines themselves (64 byte data lines will also contain zero bytes)
so that FVC compression will be viable
after having all of the input data ready, we move to the compression.
the function goes over the data lines, deciding on every iteration what is the right compression scheme. if it's the same as the previous one, we add the data line to a queue and continue.
if we reach a new compression scheme - we first compress the previously accumulated data using the previous compression scheme. this is the general algorithm.
in the end we do the same one last time for the leftover data.
the first line of compressed data is the overall header - just the length
after that we have sunheaders - one for each compression, conatining compression type, uncompressed length and compressed length, and then lines with the following data, according to every compression scheme
*/
class ifdw_decompression_seq_item extends uvm_sequence_item;
  `uvm_object_utils(ifdw_decompression_seq_item)

  parameter pword = aic_common_pkg::AIC_PWORD_SIZE;  // just 64
  // User Rand variables
  rand bit[15:0]    m_stream_length;  // can only go up to 4096
  rand int unsigned m_num_zeros_pctg; // number of zeros PW percentage
  rand int unsigned m_zeros_pctg_within_a_pw; // number of zeros PW percentage
  rand int unsigned m_int4_pctg; // number of zeros PW percentage
  rand bit          m_stream_header_err;
  rand bit          m_comp_len_err;
  rand bit          m_uncomp_len_err;
  
  // Private non-user rand variables

  protected rand int unsigned         m_num_zeros; // in PWORD
  protected rand int unsigned         m_num_zeros_indexes[$];

 
  // All related to compressed Data
  axis_data_t  m_full_pword_q[$];  // uncompressed data, queue of 512 bit words (PWORDS)
  axis_data_t  m_compressed_pword_q[$];  // compressed data, queue of 512 bit words (PWORDS)
  int unsigned zero_bytes_count[int];
  decomp_substream_header_t headers_q[int];  // this is a associative array containing all of the headers, for convenience and for coverage
  
  constraint C_LINEAR_LENGTH { // allowed/possible uncompressed data length is 0 < L < 4096
    m_stream_length > 0;
    m_stream_length <= 4096;
  }

  constraint C_NUM_ZEROS_PCTG {
    soft m_num_zeros_pctg dist { [3:5]:/40, [6:7]:/30, [8:9]:/20, 10:= 10};  // percentage of data lines that are zero
    soft m_zeros_pctg_within_a_pw dist { [26:30]:/40, [31:35]:/30, [36:40]:/20, [41:45]:/ 10};  // inside non zero data lines, percentage of zero bytes
  }

  constraint C_INT4_PERCENTAGE {  // int4 compression percantage, there are no real limitations on int4 compression
    soft m_int4_pctg == 50;
  }

  constraint C_NUM_ZEROS {
    soft m_num_zeros == (m_stream_length * m_num_zeros_pctg) / 100;
  }

  constraint C_NUM_ZERO_INDEXES {  // create a list of unique indexes, these will contain zero values
    soft m_num_zeros_indexes.size() == m_num_zeros;
    foreach (m_num_zeros_indexes[i]) {
      m_num_zeros_indexes[i] < m_stream_length;
    }
    unique {m_num_zeros_indexes};
  }

  constraint C_STREAM_HEADER_ERR {
    soft m_stream_header_err == 0;
  }

  constraint C_COMP_LEN_ERR {
    soft m_comp_len_err == 0;
  }

  constraint C_UNCOMP_LEN_ERR {
    soft m_uncomp_len_err == 0;
  }

  constraint C_SOLVER {
    solve m_stream_length before m_num_zeros_pctg;
    solve m_num_zeros_pctg before m_num_zeros;
    solve m_num_zeros before m_num_zeros_indexes;
  }

  function new (string name = "ifdw_decompression_seq_item");
    super.new (name);
  endfunction

  virtual function bit check_scheme_length(compression_scheme_t scheme, int allowed_length);
    // recieve scheme, go over all the sub headers and check if we have anything that's lower then the allowed length
    // this is mainly used to make sure we didn't accidentaly create a FVC scheme that's too short - under 6 compressed lines.
    decomp_substream_header_t header;

    foreach (headers_q[i]) begin
      if (i==0) continue;  // this is the general header
      header = decomp_substream_header_t'(headers_q[i]);
      if (header.compression_scheme == scheme && header.compressed_stream_length < allowed_length) begin
        `uvm_info(get_name(), $sformatf("check_scheme_length: got value below %0f", allowed_length), UVM_HIGH)
        return 0;
      end
    end
    `uvm_info(get_name(), $sformatf("check_scheme_length: all values above %0f", allowed_length), UVM_HIGH)
    return 1;
  endfunction

  virtual function void generate_pword_queue();
    // This function goes over the pword_q, and on all entries that aren't full 0, sprinkles in zeroes inside the data, so that we can have FVC compression
    bit[aic_common_pkg::AIC_HT_AXI_DATA_WIDTH-1:0] current_pword;
    int zeroes_count;

    m_num_zeros_indexes.sort(); // sort for further convenience
    for (int queue_index=0; queue_index < m_stream_length; queue_index++) begin
      if (queue_index inside {m_num_zeros_indexes}) begin  // if inside the zero data indexes queue, just push zeroes
        m_full_pword_q.push_back('0);
        `uvm_info(get_name(), $sformatf("generate_pword_queue: wrote 0 to index %0d", queue_index), UVM_HIGH)
      end else begin // else generate data
        current_pword = 0;
        zeroes_count = 0;
        for (int i=0; i<pword; i++) begin
          // if we hit under the zero percentage, we generate a zero byte, otherwise, we generate a nonzero value
          if ($urandom_range(1, 100) < m_zeros_pctg_within_a_pw) begin
            current_pword[i*8 +: 8] = 0;
            zeroes_count += 1;
          end else
            current_pword[i*8 +: 8] = $urandom_range(1,255);  // random non zero data
        end
        m_full_pword_q.push_back(current_pword);
        zero_bytes_count[queue_index] = zeroes_count;
        `uvm_info(get_name(), $sformatf("generate_pword_queue: wrote 0x%0x to index %0d", current_pword, queue_index), UVM_HIGH)
      end
    end
    `uvm_info(get_name(), $sformatf("generate_pword_queue: generated %0d lines of data!", m_full_pword_q.size()), UVM_LOW)
  endfunction

  virtual function decomp_substream_header_t set_lengths(decomp_substream_header_t input_subheader);
    // in case of compression/decompression errors, they will be added here
    decomp_substream_header_t output_subheader;
    output_subheader.compression_scheme         = input_subheader.compression_scheme;
    output_subheader.compressed_stream_length   = input_subheader.compressed_stream_length;
    output_subheader.uncompressed_stream_length = input_subheader.uncompressed_stream_length;
    if (m_comp_len_err) begin
      output_subheader.compressed_stream_length   = $urandom_range(0,100) > 50 ? 0: $urandom_range(MAX_STREAM_LENGTH+1,MAX_STREAM_LENGTH+10);
    end
    if (m_uncomp_len_err) begin 
      output_subheader.uncompressed_stream_length = $urandom_range(0,100) > 50 ? 0: $urandom_range(MAX_STREAM_LENGTH+1,MAX_STREAM_LENGTH+10);
    end
    return output_subheader;
  endfunction

  virtual function void write_header();
    // the header only specifies length, so that's the only thing we're writing
    decomp_stream_header_t header;

    header.stream_length = m_stream_length;
    if (m_stream_header_err) begin  // generate a faulty length, if we turns length err on!
      if ($urandom_range(0,1)) header.stream_length = 0;
      else header.stream_length = $urandom_range(4097,5000);
    end
    m_compressed_pword_q.push_back(header); // first word is always the header!
    headers_q[m_compressed_pword_q.size()-1] = (decomp_substream_header_t'(header)); // for coverage! (the length - 1 of decomp_q is where the sunheader is located in the q)
    `uvm_info(get_name(), $sformatf("write_header: wrote 0x%0x! m_compressed_pword_q size: %0d", m_stream_length, m_compressed_pword_q.size()), UVM_HIGH)
  endfunction

  virtual function int search_closest_index(int index);
  // Performs a binary tree search on the zeroes list and returns the closest index to our current one
    int left, right, mid, result;
    left = 0;
    right = m_num_zeros_indexes.size() - 1;
    result = -1; // Default result if no such element is found

    // simple cases
    if (index > m_num_zeros_indexes[right]) return -1;
    if (index == m_num_zeros_indexes[right]) return right;
    if (index == m_num_zeros_indexes[left]) return left;

    // otherwise, binary search!
    while (left <= right) begin
      mid = (left + right) / 2;
      if (index == m_num_zeros_indexes[mid]) begin
        return m_num_zeros_indexes[mid]; // Return index if exact match is found
      end else if (index > m_num_zeros_indexes[mid]) begin
        left = mid + 1; // Search in the right half
      end else begin
        result = m_num_zeros_indexes[mid];  // Track potential closest index greater than or equal
        right = mid - 1; // Search in the left half
      end
    end

    return result; // Return the closest index with value >= index
  endfunction

  virtual function bit far_enough_from_zrle(int index, int current_fvc_length=0);
    // this function checks if the current word is far enough from a word that will be compressed by zrle (so it's value is 0), to make sure there's enough potential data to compress
    bit far_enough = 1;  // we begin by assuming it's possible
    int closest_zero_index;

    closest_zero_index = search_closest_index(index);  // binary search to find closest index
    if (index == closest_zero_index) begin
      far_enough = 0;
    end else if (index < closest_zero_index) begin  // if there is a zero word close, check that it's still possible to achieve a certain amount of FVC compressed words
      far_enough = (current_fvc_length + (closest_zero_index-index) > MIN_FVC_COMPRESSED_NUM) ? 1 : 0;
    end
    `uvm_info(get_name(), $sformatf("far_enough_from_zrle: far_enough: %0x, index: %0d, closest_zero_index: %0d", far_enough, index, closest_zero_index), UVM_HIGH)
    return far_enough;
  endfunction
  
  virtual function bit is_fvc_scheme(int current_index, int current_fvc_length=0);
    // this function checks if the current data is good for FVC scheme - enough zero bytes, and a good possibility to add more FVC data next
    // there isn't really a 'storng' requirement on FVC scheme. we just want to make some amount of smart decision on that.
    int current_zero_bytes_count;
    if (! zero_bytes_count.exists(current_index)) `uvm_fatal(get_name(), $sformatf("is_fvc_scheme: index %0d not found in zero_bytes_count!", current_index))
    current_zero_bytes_count =  zero_bytes_count[current_index];
    if (current_zero_bytes_count == pword) `uvm_fatal(get_name(), $sformatf("is_fvc_scheme: index %0d has a full zero word, shouldn't got here!", current_index))
    // ti qualify for FVC, we want
    if ((current_zero_bytes_count > 8 || current_fvc_length > 1) &&  // at least 8 bytes of 0 in the word
        ((m_stream_length - current_index + current_fvc_length) > MIN_FVC_UNCOMPRESSED_NUM) &&  // we want it to be possible to reach a certain FVC compression length
        far_enough_from_zrle(current_index, current_fvc_length)) return 1; // make sure that closest zrle isn't in the way
    return 0;
  endfunction

  virtual function compression_scheme_t check_new_state(int current_index, int current_fvc_length=0);  // returns the appropriate compression scheme for the corrent data line
    axis_data_t current_data = m_full_pword_q[current_index];
    compression_scheme_t state;

    if (current_data == 0) begin  // simplest case: if the whole block is 0, it's ZRLE
      state = ZRLE;
    end else if (is_fvc_scheme(current_index, current_fvc_length)) begin  // if everything is suitable in this case, it's FVC
      state = FVC;
    end else if ($urandom_range(1, 100) < m_int4_pctg) begin  // there's no real indication for INT4, so it's just randomized
      state = INT4;
    end else begin  // default case is NO_COMP
      state = NO_COMP;
    end
    `uvm_info(get_name(), $sformatf("check_new_state: state for index %0d is %s", current_index, state.name()), UVM_HIGH)
    return state;
  endfunction

  virtual function axis_data_t create_compressed_line(bit[7:0] compressed_data_queue[$], bit ignore_error=0);
    // move a queue of 64 entries of 8 bits, to one line of 512 bits
    axis_data_t result;
    int current_byte;
    if (compressed_data_queue.size() != pword && !ignore_error) `uvm_fatal(get_name(), $sformatf("create_compressed_line: bad compressed_data_queue length: %0d!", compressed_data_queue))
    while (compressed_data_queue.size() > 0) begin
      result[current_byte*8 +: 8] = compressed_data_queue.pop_front();
      current_byte++;
    end
    return result;
  endfunction

  virtual function void compress_zrle_data(int zrle_length);
    // ZRLE case is simple - only subheader is created, compressed length doesn't matter, only uncompressed
    decomp_substream_header_t subheader;
    int original_compressed_data_len = m_compressed_pword_q.size();

    subheader.compressed_stream_length = 0;
    subheader.uncompressed_stream_length = zrle_length;
    subheader.compression_scheme = ZRLE;
    subheader = set_lengths(subheader);
    m_compressed_pword_q.push_back(subheader);  // Add ZRLE Header
    headers_q[m_compressed_pword_q.size()-1] = subheader; // for coverage! (the length - 1 of decomp_q is where the sunheader is located in the q)
    `uvm_info(get_name(), $sformatf("compress_zrle_data: wrote 0x%0x! m_compressed_pword_q size: %0d", subheader, m_compressed_pword_q.size()), UVM_HIGH)
    `uvm_info(get_name(), $sformatf("compress_zrle_data done! m_compressed_pword_q original size: %0d, m_compressed_pword_q new size: %0d, wrote %0d words.", original_compressed_data_len, m_compressed_pword_q.size(), m_compressed_pword_q.size()-original_compressed_data_len), UVM_LOW)
  endfunction

  virtual function void compress_no_comp_data(axis_data_t data_q[$]);
    // NO_COMP case is simple - compressed and uncompressed lengths are equal
    decomp_substream_header_t subheader;
    int original_compressed_data_len = m_compressed_pword_q.size();

    subheader.compressed_stream_length = data_q.size();
    subheader.uncompressed_stream_length = data_q.size();
    subheader.compression_scheme = NO_COMP;
    subheader = set_lengths(subheader);

    m_compressed_pword_q.push_back(subheader);  // Add Header
    headers_q[m_compressed_pword_q.size()-1] = subheader; // for coverage! (the length - 1 of decomp_q is where the sunheader is located in the q)
    `uvm_info(get_name(), $sformatf("compress_no_comp_data: wrote 0x%0x! m_compressed_pword_q size: %0d", subheader, m_compressed_pword_q.size()), UVM_HIGH)
    // now push in the data
    foreach (data_q[i]) begin
      m_compressed_pword_q.push_back(data_q[i]);
      `uvm_info(get_name(), $sformatf("compress_no_comp_data: wrote 0x%0x! m_compressed_pword_q size: %0d", data_q[i], m_compressed_pword_q.size()), UVM_HIGH)
    end
    `uvm_info(get_name(), $sformatf("compress_no_comp_data done! m_compressed_pword_q original size: %0d, m_compressed_pword_q new size: %0d, wrote %0d words.", original_compressed_data_len, m_compressed_pword_q.size(), m_compressed_pword_q.size()-original_compressed_data_len), UVM_LOW)
  endfunction

  virtual function bit compress_fvc_data(axis_data_t data_q[$]);
    /* FVC case:
    iterate over the uncompressed data:
    - form a mask
    - form a list of the non masked data (everythings thats not 0)
    - concat them together
    - push all of that into a bigger list
    - if that list reaches 64 bytes, write it to the output!
    - in the end, write the leftovers
    this is achieved by iterating over the input data, filling a compression list, at the end generating a headline, and writing all of that to the compression_q
    */
    decomp_substream_header_t subheader;
    axis_data_t compressed_data[$];
    axis_data_t current_compressed_line;
    bit[pword-1:0] current_mask;
    bit[7:0] current_compressed_line_bytes[$]; // a queue of bytes, for convenience of writing compression
    bit[7:0] compressed_line_bytes_running[$];
    int original_compressed_data_len = m_compressed_pword_q.size();

    foreach (data_q[i]) begin
      axis_data_t current_uncompressed_line = data_q[i]; // for clarity
      // iterate over the current 512 bits/64 bytes to build a mask and fill the data
      for (int current_byte = 0; current_byte < pword; current_byte++) begin
        if (current_uncompressed_line[current_byte*8 +: 8] == 0) begin
          current_mask[current_byte] = 0;
        end else begin
          current_mask[current_byte] = 1;
          current_compressed_line_bytes.push_back(current_uncompressed_line[current_byte*8 +: 8]);
        end
      end

      for (int current_byte = pword/8; current_byte > 0; current_byte--) begin
        current_compressed_line_bytes.push_front(current_mask[(current_byte-1)*8 +: 8]); // push the mask bytes to the front!
      end

      while (current_compressed_line_bytes.size() > 0) begin
        compressed_line_bytes_running.push_back(current_compressed_line_bytes.pop_front());  // moving into a larger dataset, to know when to write out
        if (compressed_line_bytes_running.size() == pword) begin  // we've reached 512 bits!
          current_compressed_line = create_compressed_line(compressed_line_bytes_running); // empties compressed_line_bytes_running into current_compressed_line
          compressed_line_bytes_running.delete();  // need to empty it. function doesnt really empty it.
          compressed_data.push_back(current_compressed_line);
          `uvm_info(get_name(), $sformatf("compress_fvc_data: wrote 0x%0x! compressed_data size: %0d", current_compressed_line, compressed_data.size()), UVM_HIGH)
          current_compressed_line = 0; // just in case
        end
      end
    end

    if (compressed_line_bytes_running.size() != 0) begin  // lets get rid of the leftovers!
      current_compressed_line = 0; // just in case
      current_compressed_line = create_compressed_line(compressed_line_bytes_running, 1); // empties compressed_line_bytes_running into current_compressed_line
      compressed_data.push_back(current_compressed_line);
      `uvm_info(get_name(), $sformatf("compress_fvc_data: wrote 0x%0x! compressed_data size: %0d", current_compressed_line, compressed_data.size()), UVM_HIGH)
    end
    // compression is done, lets write the data!
    subheader.compressed_stream_length = compressed_data.size();
    subheader.uncompressed_stream_length = data_q.size();
    subheader.compression_scheme = FVC;
    subheader = set_lengths(subheader);

    if (subheader.compressed_stream_length < MIN_FVC_COMPRESSED_NUM) begin
      `uvm_info(get_name(), $sformatf("compress_fvc_data: FVC compressed size - %0d, lower then threshold of %0d. redoing with NO_COMP. uncomp data size - %0d", subheader.compressed_stream_length, MIN_FVC_COMPRESSED_NUM, data_q.size()), UVM_LOW)
      return 1;
    end

    m_compressed_pword_q.push_back(subheader);  // now push everything in!
    headers_q[m_compressed_pword_q.size()-1] = subheader; // for coverage! (the length - 1 of decomp_q is where the sunheader is located in the q)
    `uvm_info(get_name(), $sformatf("compress_fvc_data: wrote 0x%0x! m_compressed_pword_q size: %0d", subheader, m_compressed_pword_q.size()), UVM_HIGH)
    while (compressed_data.size() > 0) begin
      m_compressed_pword_q.push_back(compressed_data.pop_front());
      `uvm_info(get_name(), $sformatf("compress_fvc_data: wrote 0x%0x! m_compressed_pword_q size: %0d", m_compressed_pword_q[$], m_compressed_pword_q.size()), UVM_HIGH)  // last place in m_compressed_pword_q is the word we just wrote!
    end
    `uvm_info(get_name(), $sformatf("compress_fvc_data done! m_compressed_pword_q original size: %0d, m_compressed_pword_q new size: %0d, wrote %0d words.", original_compressed_data_len, m_compressed_pword_q.size(), m_compressed_pword_q.size()-original_compressed_data_len), UVM_LOW)
    return 0;
  endfunction

  virtual function void compress_int4_data(axis_data_t data_q[$], int int4_start_index);
    /* INT4 compression - every byte is transformed into 4 bit, this is done by cutting the 4 LSB bits.
    in addition to doing that, and then writing to the compressed data stream, we also have to treat the original, uncompressed data,
    this is because INT4 compression loses data - when it's decompressed, the 4 LSB bit are just zeroes*/
    decomp_substream_header_t subheader;
    axis_data_t current_compressed_line;
    bit[3:0] compressed_int_q[$];
    int original_compressed_data_len = m_compressed_pword_q.size();

    // we know the compression length from the beggining, since we just take half the data. it will be half the original data + 1 if it's uneven
    subheader.compressed_stream_length = (data_q.size()/2) + (data_q.size()%2);
    subheader.uncompressed_stream_length = data_q.size();
    subheader.compression_scheme = INT4;
    subheader = set_lengths(subheader);

    m_compressed_pword_q.push_back(subheader);  // Add Header
    headers_q[m_compressed_pword_q.size()-1] = subheader; // for coverage! (the length - 1 of decomp_q is where the sunheader is located in the q)
    `uvm_info(get_name(), $sformatf("compress_int4_data: wrote 0x%0x! m_compressed_pword_q size: %0d", subheader, m_compressed_pword_q.size()), UVM_HIGH)
    // now push in the data
    foreach (data_q[i]) begin
      bit[3:0] compressed_int;
      for (int current_byte = 0; current_byte < pword; current_byte++) begin
        bit[7:0] uncompressed_int = data_q[i][current_byte*8 +: 8]; // we take away a byte every time
        compressed_int = uncompressed_int[7:4];  // this is the compression!
        m_full_pword_q[int4_start_index+i][current_byte*8 +: 8] = {compressed_int, 4'b0000};  // replacing the original value with the decompressed one!
        compressed_int_q.push_back(compressed_int);  // pushing the compressed word into the compressed queue!
      end
      if (compressed_int_q.size() == 2*pword) begin  // since it's half the size, it's twice the length!
        int j=0;
        while (compressed_int_q.size() > 0) begin
          current_compressed_line[j*4 +: 4] = compressed_int_q.pop_front();
          j++;
        end
        m_compressed_pword_q.push_back(current_compressed_line);
        `uvm_info(get_name(), $sformatf("compress_int4_data: wrote 0x%0x! m_compressed_pword_q size: %0d", current_compressed_line, m_compressed_pword_q.size()), UVM_HIGH)
        current_compressed_line = 0; // just in case
      end
    end

    if (compressed_int_q.size() != 0) begin  // lets get rid of the leftovers!
      int j=0;
      while (compressed_int_q.size() > 0) begin
        current_compressed_line[j*4 +: 4] = compressed_int_q.pop_front();
        j++;
      end
      m_compressed_pword_q.push_back(current_compressed_line);
      `uvm_info(get_name(), $sformatf("compress_int4_data: wrote 0x%0x! m_compressed_pword_q size: %0d", current_compressed_line, m_compressed_pword_q.size()), UVM_HIGH)
    end
    `uvm_info(get_name(), $sformatf("compress_int4_data done! m_compressed_pword_q original size: %0d, m_compressed_pword_q new size: %0d, wrote %0d words.", original_compressed_data_len, m_compressed_pword_q.size(), m_compressed_pword_q.size()-original_compressed_data_len), UVM_LOW)
  endfunction

  virtual function void compress_data(compression_scheme_t state, axis_data_t data_q[$], int int4_start_index=0);
    // compressed/uncompressed length is measured in pwords - so 512 bits of data.
    bit FVC_fail;
    case (state)
      ZRLE     : compress_zrle_data(data_q.size());
      FVC      : FVC_fail = compress_fvc_data(data_q);
      INT4     : compress_int4_data(data_q, int4_start_index);
      NO_COMP  : compress_no_comp_data(data_q);
      default  : `uvm_fatal(get_name(), $sformatf("compress_data: no valid scheme given!"))
    endcase
    if (FVC_fail) compress_no_comp_data(data_q);  // IF FVC compression was to short, just no comp the same data.
  endfunction

  virtual function void generate_compressed_data();
    compression_scheme_t old_state, new_state;
    axis_data_t current_data_q[$];
    int current_fvc_length;  // counts how much fvc we have, to calculate how much we still want to have
    int int4_start_index;  // we need to adjust int4 input data for decompression as well

    // Init queues
    m_compressed_pword_q.delete();
    // write the header
    write_header();
    old_state = check_new_state(0);  // initialize with the very first state, so first write will be correct as well
    foreach (m_full_pword_q[i]) begin
      new_state = i==0 ? old_state : check_new_state(i, current_fvc_length);  // need to this to avoid a case where old_state gets no_comp, and the first iteration getting int4/vice versa
      current_fvc_length = (new_state == FVC) ? current_fvc_length+1 : 0; // if we're still rolling with FVC, increment by 1, otherwise, 0
      if (new_state != old_state) begin  // if we're moving to a new state, wrap up the previous one - create subheader and all.
        compress_data(old_state, current_data_q, int4_start_index);
        old_state = new_state;
        if (new_state == INT4) int4_start_index = i;
        current_data_q.delete();
      end
      current_data_q.push_back(m_full_pword_q[i]);
    end

    if (current_data_q.size() > 0) begin  // after the last data word, we need to make sure we empty the buffer!
      compress_data(old_state, current_data_q, int4_start_index);
      old_state = new_state;
      current_data_q.delete();
    end
    `uvm_info(get_name(), $sformatf("generate_compressed_data done! input stream size %0d, wrote %0d words.", m_full_pword_q.size(), m_compressed_pword_q.size()), UVM_LOW)
  endfunction

  virtual function ifdw_decompression_seq_item do_clone();
    ifdw_decompression_seq_item item;
    if(!$cast(item, this.clone()))
      `uvm_fatal(get_full_name(), "Clone failed")
    return item;
  endfunction

  virtual function void do_copy(uvm_object rhs);
    ifdw_decompression_seq_item seq_rhs;

    if(rhs == null)
      `uvm_fatal(get_full_name(), "do_copy from null ptr");

    if(!$cast(seq_rhs, rhs))
      `uvm_fatal(get_full_name(), "do_copy cast failed");

    super.do_copy(rhs);
    this.m_stream_length = seq_rhs.m_stream_length;
    this.m_compressed_pword_q.delete();
    foreach (seq_rhs.m_compressed_pword_q[i]) begin
      this.m_compressed_pword_q.push_back(seq_rhs.m_compressed_pword_q[i]);
    end
    this.m_full_pword_q.delete();
    foreach (seq_rhs.m_full_pword_q[i]) begin
      this.m_full_pword_q.push_back(seq_rhs.m_full_pword_q[i]);
    end
    this.headers_q.delete();
    foreach (seq_rhs.headers_q[i]) begin
      this.headers_q[i] = seq_rhs.headers_q[i];
    end
    this.m_stream_header_err = seq_rhs.m_stream_header_err;
    this.m_comp_len_err      = seq_rhs.m_comp_len_err;
    this.m_uncomp_len_err    = seq_rhs.m_uncomp_len_err;
  endfunction

  virtual function string convert2string();
    string s = super.convert2string();
    s = {s, $sformatf("\n----------- IFDW DECOMPRESSION ITEM ----------------") };
    s = {s, $sformatf("\n Stream Length (PW)   : %0d", m_stream_length)};
    s = {s, $sformatf("\n Stream Header Error  : %0d", m_stream_header_err)};
    s = {s, $sformatf("\n Comp Length   Error  : %0d", m_comp_len_err)};
    s = {s, $sformatf("\n Uncomp Length Error  : %0d", m_uncomp_len_err)};
    s = {s, $sformatf("\n ZRLE Count (PW)      : %0d", m_num_zeros)};
    s = {s, $sformatf("\n ZRLE Indexes         : %p", m_num_zeros_indexes)};
    foreach (m_full_pword_q[i]) begin
      s = {s, $sformatf("\n Data Stream Uncomp (PW) : [%0d] 0x%128x", i, m_full_pword_q[i])};
      if (zero_bytes_count.exists(i)) begin  // if it's not zero data
        s = {s, $sformatf(" zero_bytes_count: %0d", zero_bytes_count[i])};
      end
    end
    foreach (m_compressed_pword_q[i]) begin
      if (i==0) begin
        s = {s, $sformatf("\n Data Stream Comp (PW) : [%0d] %p", i, decomp_stream_header_t'(m_compressed_pword_q[i]))};
      end else if (headers_q.exists(i)) begin // this means it's a subheader!
        s = {s, $sformatf("\n Data Stream Comp (PW) : [%0d] %p", i, decomp_substream_header_t'(m_compressed_pword_q[i]))};
      end else begin
        s = {s, $sformatf("\n Data Stream Comp (PW) : [%0d] 0x%128x", i, m_compressed_pword_q[i])};
      end
    end
    s = {s, $sformatf("\n---------------------------------------------") };
    return s;
  endfunction

  function void post_randomize();
    // this is the main function!
    super.post_randomize();
    // empty all queues before start!
    m_full_pword_q.delete();
    m_compressed_pword_q.delete();
    zero_bytes_count.delete();
    headers_q.delete();
    generate_pword_queue();
    generate_compressed_data();
  endfunction
endclass

`endif
