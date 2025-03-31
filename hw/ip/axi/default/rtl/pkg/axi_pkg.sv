// (C) Copyright 2024 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Wolfgang Roenninger <wolfgang.roenninger@axelera.ai>
// Authors:
// - Andreas Kurth <akurth@iis.ee.ethz.ch>
// - Florian Zaruba <zarubaf@iis.ee.ethz.ch>
// - Wolfgang Roenninger <wroennin@iis.ee.ethz.ch>
// - Fabian Schuiki <fschuiki@iis.ee.ethz.ch>
// - Matheus Cavalcante <matheusd@iis.ee.ethz.ch>


`ifndef AXI_PKG_SV
`define AXI_PKG_SV
//! AXI Package
/// Contains all necessary type definitions, constants, and generally useful functions.
///
package axi_pkg;

  /// AXI Transaction Burst Width.
  parameter int unsigned AXI_BURST_WIDTH = 2;
  /// AXI Transaction Response Width.
  parameter int unsigned AXI_RESP_WIDTH = 2;
  /// AXI Transaction Cacheability Width.
  parameter int unsigned AXI_CACHE_WIDTH = 4;
  /// AXI Transaction Protection Width.
  parameter int unsigned AXI_PROT_WIDTH = 3;
  /// AXI Transaction Quality of Service Width.
  parameter int unsigned AXI_QOS_WIDTH = 4;
  /// AXI Transaction Region Width.
  parameter int unsigned AXI_REGION_WIDTH = 4;
  /// AXI Transaction Length Width.
  parameter int unsigned AXI_LEN_WIDTH = 8;
  /// AXI Transaction Size Width.
  parameter int unsigned AXI_SIZE_WIDTH = 3;
  /// AXI Lock Width.
  /// AXI5 Atomic Operation Width.
  parameter int unsigned AXI_ATOP_WIDTH = 6;
  /// AXI5 Non-Secure Address Identifier.
  parameter int unsigned AXI_NSAID_WIDTH = 4;

  /// AXI Transaction Burst Type.
  typedef logic [AXI_BURST_WIDTH-1:0]  axi_burst_t;
  /// AXI Transaction Response Type.
  typedef logic [AXI_RESP_WIDTH-1:0]   axi_resp_t;
  /// AXI Transaction Cacheability Type.
  typedef logic [AXI_CACHE_WIDTH-1:0]  axi_cache_t;
  /// AXI Transaction Protection Type.
  typedef logic [AXI_PROT_WIDTH-1:0]   axi_prot_t;
  /// AXI Transaction Quality of Service Type.
  typedef logic [AXI_QOS_WIDTH-1:0]    axi_qos_t;
  /// AXI Transaction Region Type.
  typedef logic [AXI_REGION_WIDTH-1:0] axi_region_t;
  /// AXI Transaction Length Type.
  typedef logic [AXI_LEN_WIDTH-1:0]    axi_len_t;
  /// AXI Transaction Size Type.
  typedef logic [AXI_SIZE_WIDTH-1:0]   axi_size_t;
  /// AXI5 Atomic Operation Type.
  typedef logic [AXI_ATOP_WIDTH-1:0]   axi_atop_t;
  /// AXI5 Non-Secure Address Identifier.
  typedef logic [AXI_NSAID_WIDTH-1:0]  axi_nsaid_t;

  /// In a fixed burst:
  /// - The address is the same for every transfer in the burst.
  /// - The byte lanes that are valid are constant for all beats in the burst.  However, within
  ///   those byte lanes, the actual bytes that have `wstrb` asserted can differ for each beat in
  ///   the burst.
  /// This burst type is used for repeated accesses to the same location such as when loading or
  /// emptying a FIFO.
  parameter axi_burst_t AXI_BURST_FIXED = 2'b00;
  /// In an incrementing burst, the address for each transfer in the burst is an increment of the
  /// address for the previous transfer.  The increment value depends on the size of the transfer.
  /// For example, the address for each transfer in a burst with a size of 4 bytes is the previous
  /// address plus four.
  /// This burst type is used for accesses to normal sequential memory.
  parameter axi_burst_t AXI_BURST_INCR  = 2'b01;
  /// A wrapping burst is similar to an incrementing burst, except that the address wraps around to
  /// a lower address if an upper address limit is reached.
  /// The following restrictions apply to wrapping bursts:
  /// - The start address must be aligned to the size of each transfer.
  /// - The length of the burst must be 2, 4, 8, or 16 transfers.
  parameter axi_burst_t AXI_BURST_WRAP  = 2'b10;

  /// An enum for the burst type
  typedef enum axi_burst_t {
    BurstFixed = AXI_BURST_FIXED,
    BurstIncr  = AXI_BURST_INCR,
    BurstWrap  = AXI_BURST_WRAP
  } axi_burst_e;

  /// Normal access success.  Indicates that a normal access has been successful. Can also indicate
  /// that an exclusive access has failed.
  parameter axi_resp_t AXI_RESP_OKAY   = 2'b00;
  /// Exclusive access okay.  Indicates that either the read or write portion of an exclusive access
  /// has been successful.
  parameter axi_resp_t AXI_RESP_EXOKAY = 2'b01;
  /// Slave error.  Used when the access has reached the slave successfully, but the slave wishes to
  /// return an error condition to the originating master.
  parameter axi_resp_t AXI_RESP_SLVERR = 2'b10;
  /// Decode error.  Generated, typically by an interconnect component, to indicate that there is no
  /// slave at the transaction address.
  parameter axi_resp_t AXI_RESP_DECERR = 2'b11;

  /// An enum for the AXI response type
  typedef enum axi_resp_t {
    RespOkay   = AXI_RESP_OKAY,
    RespExOkay = AXI_RESP_EXOKAY,
    RespSlvErr = AXI_RESP_SLVERR,
    RespDecErr = AXI_RESP_DECERR
  } axi_resp_e;

  /// When this bit is asserted, the interconnect, or any component, can delay the transaction
  /// reaching its final destination for any number of cycles.
  parameter axi_cache_t CACHE_BUFFERABLE = 4'b0001;
  /// When HIGH, Modifiable indicates that the characteristics of the transaction can be modified.
  /// When Modifiable is LOW, the transaction is Non-modifiable.
  parameter axi_cache_t CACHE_MODIFIABLE = 4'b0010;
  /// When this bit is asserted, read allocation of the transaction is recommended but is not
  /// mandatory.
  parameter axi_cache_t CACHE_RD_ALLOC   = 4'b0100;
  /// When this bit is asserted, write allocation of the transaction is recommended but is not
  /// mandatory.
  parameter axi_cache_t CACHE_WR_ALLOC   = 4'b1000;

  /// An enum for the AXI chache type
  typedef enum axi_cache_t {
    CacheBufferable = CACHE_BUFFERABLE,
    CacheModifiable = CACHE_MODIFIABLE,
    CacheRdAllocate = CACHE_RD_ALLOC,
    CacheWRAllocate = CACHE_WR_ALLOC
  } axi_cache_e;

  // Number of bytes in AXI transfer
  // 1 Bytes in AXI transfer
  parameter axi_size_t AXI_BYTES_1   = 3'b000;
  // 2 Bytes in AXI transfer
  parameter axi_size_t AXI_BYTES_2   = 3'b001;
  // 4 Bytes in AXI transfer
  parameter axi_size_t AXI_BYTES_4   = 3'b010;
  // 8 Bytes in AXI transfer
  parameter axi_size_t AXI_BYTES_8   = 3'b011;
  // 16 Bytes in AXI transfer
  parameter axi_size_t AXI_BYTES_16  = 3'b100;
  // 32 Bytes in AXI transfer
  parameter axi_size_t AXI_BYTES_32  = 3'b101;
  // 64 Bytes in AXI transfer
  parameter axi_size_t AXI_BYTES_64  = 3'b110;
  // 128 Bytes in AXI transfer
  parameter axi_size_t AXI_BYTES_128 = 3'b111;

  /// An enum for the AXI size
  typedef enum axi_size_t {
    Bytes001 = AXI_BYTES_1,
    Bytes002 = AXI_BYTES_2,
    Bytes004 = AXI_BYTES_4,
    Bytes008 = AXI_BYTES_8,
    Bytes016 = AXI_BYTES_16,
    Bytes032 = AXI_BYTES_32,
    Bytes064 = AXI_BYTES_64,
    Bytes128 = AXI_BYTES_128
  } axi_size_e;

  /// Maximum number of bytes per burst, as specified by `size` (see Table A3-2).
  function automatic shortint unsigned axi_num_bytes(axi_size_t size);
    return 16'(unsigned'(1) << size);
  endfunction

  /// An overly long address type.
  /// It lets us define functions that work generically for shorter addresses.  We rely on the
  /// synthesizer to optimize the unused bits away.
  typedef logic [127:0] axi_largest_addr_t;

  /// Private function to be used to caclulate an aligned address
  /// This is written in a way to also able to be used in calculation of the wrap boundary
  ///
  function automatic axi_largest_addr_t _axi_aligned_addr(
    axi_largest_addr_t addr,
    axi_size_t         size,
    axi_size_t         len_factor
  );
    logic [AXI_SIZE_WIDTH:0] mask_length;
    mask_length = size + len_factor;

    return axi_largest_addr_t'(addr >> mask_length) << mask_length;
  endfunction

  /// Aligned address of burst (see A3-51).
  function automatic axi_largest_addr_t axi_aligned_addr(
    axi_largest_addr_t addr,
    axi_size_t         size
  );
    return _axi_aligned_addr(addr, size, axi_size_t'(0));
  endfunction

  /// Warp boundary of a `AXI_BURST_WRAP` transfer (see A3-51).
  /// This is the lowest address accessed within a wrapping burst.
  /// This address is aligned to the size and length of the burst.
  /// The length of a `AXI_BURST_WRAP` has to be 2, 4, 8, or 16 transfers.
  function automatic axi_largest_addr_t axi_wrap_boundary(
    axi_largest_addr_t addr,
    axi_size_t         size,
    axi_len_t          len
  );
    axi_largest_addr_t wrap_addr;

    ////////////////
    // Assertions //
    ////////////////
    `ifndef SYNTHESIS
    `ifdef ASSERTIONS_ON
      if (!$isunknown(len)) begin
        assume (
            len == axi_len_t'(4'b0001) ||
            len == axi_len_t'(4'b0011) ||
            len == axi_len_t'(4'b0111) ||
            len == axi_len_t'(4'b1111)
        ) else $error("AXI AXI_BURST_WRAP with not allowed len of: 0x%0h", len);
      end
    `endif
    `endif

    // In A3-51 the wrap boundary is defined as:
    // `Wrap_Boundary = (INT(Start_Address / (Number_Bytes × Burst_Length))) ×
    //    (Number_Bytes × Burst_Length)`
    // Whereas the aligned address is defined as:
    // `Aligned_Address = (INT(Start_Address / Number_Bytes)) × Number_Bytes`
    // This leads to the wrap boundary using the same calculation as the aligned address, difference
    // being the additional dependency on the burst length. The addition in the case statement
    // is equal to the multiplication with `Burst_Length` as a shift (used by `aligned_addr`) is
    // equivalent with multiplication and division by a power of two, which conveniently are the
    // only allowed values for `len` of a `AXI_BURST_WRAP`.
    unique case (len)
      // multiply `Number_Bytes` by `2`
      axi_len_t'(4'b0001): wrap_addr = _axi_aligned_addr(addr, size, axi_size_t'(1));
      // multiply `Number_Bytes` by `4`
      axi_len_t'(4'b0011): wrap_addr = _axi_aligned_addr(addr, size, axi_size_t'(2));
      // multiply `Number_Bytes` by `8`
      axi_len_t'(4'b0111): wrap_addr = _axi_aligned_addr(addr, size, axi_size_t'(3));
      // multiply `Number_Bytes` by `16`
      axi_len_t'(4'b1111): wrap_addr = _axi_aligned_addr(addr, size, axi_size_t'(4));
      default: wrap_addr = axi_largest_addr_t'(0);
    endcase
    return wrap_addr;
  endfunction

  /// Address of beat (see A3-51).
  function automatic axi_largest_addr_t axi_beat_addr(
    axi_largest_addr_t addr,
    axi_size_t         size,
    axi_len_t          len,
    axi_burst_t        burst,
    axi_len_t          i_beat
  );
    axi_largest_addr_t ret_addr;
    axi_largest_addr_t wrp_bond;
    axi_largest_addr_t tnx_size;

    ret_addr = addr;
    wrp_bond = '0;
    tnx_size = '0;

    // Early return if we have the first beat or are a fixed Burst
    if ((i_beat == axi_len_t'(0)) || (burst  == AXI_BURST_FIXED)) return ret_addr;

    // From A3-51:
    // For an INCR burst, and for a WRAP burst for which the address has not wrapped, this
    // equation determines the address of any transfer after the first transfer in a burst:
    // `Address_N = Aligned_Address + (N - 1) × Number_Bytes` (N counts from 1 to len!)
    ret_addr = axi_aligned_addr(addr, size) + (i_beat << size);
    // From A3-51:
    // For a WRAP burst, if Address_N = Wrap_Boundary + (Number_Bytes × Burst_Length), then:
    // * Use this equation for the current transfer:
    //     `Address_N = Wrap_Boundary`
    // * Use this equation for any subsequent transfers:
    //     `Address_N = Start_Address + ((N - 1) × Number_Bytes) - (Number_Bytes × Burst_Length)`
    // This means that the address calculation of a `AXI_BURST_WRAP` fundamentally works the same
    // as for a `AXI_BURST_INCR`, the difference is when the calculated address increments
    // over the wrap threshold, the address wraps around by subtracting the accessed address
    // space from the normal `AXI_BURST_INCR` address. The lower wrap boundary is equivalent to
    // The wrap trigger condition minus the container size (`num_bytes(size) * (len + 1)`).
    if (burst == AXI_BURST_WRAP) begin
      // The transfer siz is defines as 'Size * Length'
      tnx_size = axi_largest_addr_t'((len + 1) << size);
      // do not trigger the function if there is no wrapping burst, to prevent assumptions firing
      wrp_bond = axi_wrap_boundary(addr, size, len);
      if (ret_addr >= wrp_bond + tnx_size) begin
        ret_addr = ret_addr - tnx_size;
      end
    end

    return ret_addr;
  endfunction

  /// Indicate that a transfer is crossing the 4 Kb boundary
  ///
  function automatic logic axi_burst_crosses_4kb_boundary(
    /// Address of the transfer
    axi_largest_addr_t addr,
    /// Size of the transfer
    axi_size_t         size,
    /// Lenth of the Transfer
    axi_len_t          len,
    /// Burst type of the transfer
    axi_burst_t        burst
  );
    axi_largest_addr_t size_aligned_addr;
    size_aligned_addr = axi_aligned_addr(
      .addr(addr),
      .size(size)
    );

    // By definition fixed and wrap can't cross it
    if (burst inside {BurstFixed, BurstWrap}) return 1'b0;

    return ((size_aligned_addr % axi_largest_addr_t'(4096)) + axi_largest_addr_t'((len + 1) << size)) > axi_largest_addr_t'(4096);
  endfunction

  /// Is the bufferable bit set?
  function automatic logic axi_bufferable_bit_set(axi_cache_t cache);
    return |(cache & CACHE_BUFFERABLE);
  endfunction

  /// Is the modifiable bit set?
  function automatic logic axi_modifiable_bit_set(axi_cache_t cache);
    return |(cache & CACHE_MODIFIABLE);
  endfunction

  /// Memory Type.
  typedef enum logic [3:0] {
    DeviceNonBufferable,
    DeviceBufferable,
    NormalNonCachableNonBufferable,
    NormalNonCachableBufferable,
    WriteThroughNoAllocate,
    WriteThroughReadAllocate,
    WriteThroughWriteAllocate,
    WriteThroughReadAndWriteAllocate,
    WriteBackNoAllocate,
    WriteBackReadAllocate,
    WriteBackWriteAllocate,
    WriteBackReadAndWriteAllocate
  } axi_mem_type_e;

  /// Create an `AR_CACHE` field from a `axi_mem_type_e` type.
  function automatic axi_cache_t axi_get_arcache(axi_mem_type_e mtype);
    unique case (mtype)
      DeviceNonBufferable:              return 4'b0000;
      DeviceBufferable:                 return 4'b0001;
      NormalNonCachableNonBufferable:   return 4'b0010;
      NormalNonCachableBufferable:      return 4'b0011;
      WriteThroughNoAllocate:           return 4'b1010;
      WriteThroughReadAllocate:         return 4'b1110;
      WriteThroughWriteAllocate:        return 4'b1010;
      WriteThroughReadAndWriteAllocate: return 4'b1110;
      WriteBackNoAllocate:              return 4'b1011;
      WriteBackReadAllocate:            return 4'b1111;
      WriteBackWriteAllocate:           return 4'b1011;
      WriteBackReadAndWriteAllocate:    return 4'b1111;
      default:                          return 4'b0000;
    endcase // mtype
  endfunction

  /// Create an `AW_CACHE` field from a `axi_mem_type_e` type.
  function automatic axi_cache_t axi_get_awcache(axi_mem_type_e mtype);
    unique case (mtype)
      DeviceNonBufferable:              return 4'b0000;
      DeviceBufferable:                 return 4'b0001;
      NormalNonCachableNonBufferable:   return 4'b0010;
      NormalNonCachableBufferable:      return 4'b0011;
      WriteThroughNoAllocate:           return 4'b0110;
      WriteThroughReadAllocate:         return 4'b0110;
      WriteThroughWriteAllocate:        return 4'b1110;
      WriteThroughReadAndWriteAllocate: return 4'b1110;
      WriteBackNoAllocate:              return 4'b0111;
      WriteBackReadAllocate:            return 4'b0111;
      WriteBackWriteAllocate:           return 4'b1111;
      WriteBackReadAndWriteAllocate:    return 4'b1111;
      default:                          return 4'b0000;
    endcase // mtype
  endfunction

  /// RESP precedence: DECERR > SLVERR > OKAY > EXOKAY.  This is not defined in the AXI standard but
  /// depends on the implementation.  We consistently use the precedence above.  Rationale:
  /// - EXOKAY means an exclusive access was successful, whereas OKAY means it was not.  Thus, if
  ///   OKAY and EXOKAY are to be merged, OKAY precedes because the exclusive access was not fully
  ///   successful.
  /// - Both DECERR and SLVERR mean (part of) a transaction were unsuccessful, whereas OKAY means an
  ///   entire transaction was successful.  Thus both DECERR and SLVERR precede OKAY.
  /// - DECERR means (part of) a transactions could not be routed to a slave component, whereas
  ///   SLVERR means the transaction reached a slave component but lead to an error condition there.
  ///   Thus DECERR precedes SLVERR because DECERR happens earlier in the handling of a transaction.
  function automatic axi_resp_e axi_resp_precedence(axi_resp_e resp_a, axi_resp_e resp_b);
    unique case (resp_a)
      RespOkay: begin
        // Any response except EXOKAY precedes OKAY.
        if (resp_b == RespExOkay) begin
          return resp_a;
        end else begin
          return resp_b;
        end
      end
      RespExOkay: begin
        // Any response precedes EXOKAY.
        return resp_b;
      end
      RespSlvErr: begin
        // Only DECERR precedes SLVERR.
        if (resp_b == RespDecErr) begin
          return resp_b;
        end else begin
          return resp_a;
        end
      end
      RespDecErr: begin
        // No response precedes DECERR.
        return resp_a;
      end
      default: return resp_a;
    endcase
  endfunction

  /// ATOP[5:0]
  ///
  /// - Sends a single data value with an address.
  /// - The target swaps the value at the addressed location with the data value that is supplied in
  ///   the transaction.
  /// - The original data value at the addressed location is returned.
  /// - Outbound data size is 1, 2, 4, or 8 bytes.
  /// - Inbound data size is the same as the outbound data size.
  parameter axi_atop_t AXI_ATOP_ATOMICSWAP = 6'b110000;
  /// - Sends two data values, the compare value and the swap value, to the addressed location.
  ///   The compare and swap values are of equal size.
  /// - The data value at the addressed location is checked against the compare value:
  ///   - If the values match, the swap value is written to the addressed location.
  ///   - If the values do not match, the swap value is not written to the addressed location.
  /// - The original data value at the addressed location is returned.
  /// - Outbound data size is 2, 4, 8, 16, or 32 bytes.
  /// - Inbound data size is half of the outbound data size because the outbound data contains both
  ///   compare and swap values, whereas the inbound data has only the original data value.
  parameter axi_atop_t AXI_ATOP_ATOMICCMP = 6'b110001;
  /// ATOP[5:4]
  ///
  /// Perform no atomic operation.
  parameter logic [1:0] AXI_ATOP_NONE = 2'b00;
  /// - Sends a single data value with an address and the atomic operation to be performed.
  /// - The target performs the operation using the sent data and value at the addressed location as
  ///   operands.
  /// - The result is stored in the address location.
  /// - A single response is given without data.
  /// - Outbound data size is 1, 2, 4, or 8 bytes.
  parameter logic [1:0] AXI_ATOP_ATOMICSTORE = 2'b01;
  /// Sends a single data value with an address and the atomic operation to be performed.
  /// - The original data value at the addressed location is returned.
  /// - The target performs the operation using the sent data and value at the addressed location as
  ///   operands.
  /// - The result is stored in the address location.
  /// - Outbound data size is 1, 2, 4, or 8 bytes.
  /// - Inbound data size is the same as the outbound data size.
  parameter logic [1:0] AXI_ATOP_ATOMICLOAD  = 2'b10;
  /// ATOP[3]
  ///
  /// For AtomicStore and AtomicLoad transactions `AWATOP[3]` indicates the endianness that is
  /// required for the atomic operation.  The value of `AWATOP[3]` applies to arithmetic operations
  /// only and is ignored for bitwise logical operations.
  /// When deasserted, this bit indicates that the operation is little-endian.
  parameter logic AXI_ATOP_LITTLE_END  = 1'b0;
  /// When asserted, this bit indicates that the operation is big-endian.
  parameter logic AXI_ATOP_BIG_END     = 1'b1;
  /// ATOP[2:0]
  ///
  /// The value in memory is added to the sent data and the result stored in memory.
  parameter logic [2:0] AXI_ATOP_ADD   = 3'b000;
  /// Every set bit in the sent data clears the corresponding bit of the data in memory.
  parameter logic [2:0] AXI_ATOP_CLR   = 3'b001;
  /// Bitwise exclusive OR of the sent data and value in memory.
  parameter logic [2:0] AXI_ATOP_EOR   = 3'b010;
  /// Every set bit in the sent data sets the corresponding bit of the data in memory.
  parameter logic [2:0] AXI_ATOP_SET   = 3'b011;
  /// The value stored in memory is the maximum of the existing value and sent data. This operation
  /// assumes signed data.
  parameter logic [2:0] AXI_ATOP_SMAX  = 3'b100;
  /// The value stored in memory is the minimum of the existing value and sent data. This operation
  /// assumes signed data.
  parameter logic [2:0] AXI_ATOP_SMIN  = 3'b101;
  /// The value stored in memory is the maximum of the existing value and sent data. This operation
  /// assumes unsigned data.
  parameter logic [2:0] AXI_ATOP_UMAX  = 3'b110;
  /// The value stored in memory is the minimum of the existing value and sent data. This operation
  /// assumes unsigned data.
  parameter logic [2:0] AXI_ATOP_UMIN  = 3'b111;
  // ATOP[5] == 1'b1 indicated that an atomic transaction has a read response
  // Ussage eg: if (req_i.aw.atop[axi_pkg::AXI_ATOP_R_RESP_IDX]) begin
  parameter int unsigned AXI_ATOP_R_RESP_IDX = 32'd5;

endpackage

`endif
