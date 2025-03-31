// (C) Copyright Axelera AI 2023
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: AI Core LS IFD-ODR Compression Scheme
//   Function Coverage
//
// Owner: Rafael Frangulian <rafael.frangulian@axelera.ai>
// -------------------------------------------------

// Compression Scheme Coverage
//  typedef enum bit[1:0] { NO_COMP, FVC, ZRLE, INT4 } compression_scheme_t;
//  typedef enum bit[1:0] { INVALID_STREAM_HEADER, INVALID_SCHEME_HEADER, INVALID_COMP_SIZE, INVALID_UNCOMP_SIZE } compression_error_t;

covergroup compression_cg (string cg_name) with function sample(bit is_subheader, compression_scheme_t comp, compression_error_t comp_err, bit has_err, int clen, int ulen);
  option.per_instance = 1'b1;
  option.name = cg_name;

  // Note: back2back schemes not applicable. The compression schemes are optimized to just combine the compressed lengths instead
  // using 2 compression schemes back to back
  cp_compression_scheme: coverpoint comp iff (is_subheader) {  // transition between schemes
    bins NO_COMP_TO_FVC    = (NO_COMP   => FVC);
    bins NO_COMP_TO_ZRLE   = (NO_COMP   => ZRLE);
    bins NO_COMP_TO_INT4   = (NO_COMP   => INT4);
    bins FVC_TO_NO_COMP    = (FVC  => NO_COMP);
    bins FVC_TO_ZRLE       = (FVC  => ZRLE);
    bins FVC_TO_INT4       = (FVC  => INT4);
    bins ZRLE_TO_NO_COMP   = (ZRLE => NO_COMP);
    bins ZRLE_TO_FVC       = (ZRLE => FVC);
    bins ZRLE_TO_INT4      = (ZRLE => INT4);
    bins INT4_TO_NO_COMP   = (INT4 => NO_COMP);
    bins INT4_TO_FVC       = (INT4 => FVC);
    bins INT4_TO_ZRLE      = (INT4 => ZRLE);
  }

  cp_compression_error: coverpoint comp_err iff (is_subheader && has_err) {  // different types of errors
    bins INVALID_STREAM_HEADER = {INVALID_STREAM_HEADER};
    bins INVALID_COMP_SIZE     = {INVALID_COMP_SIZE};
    bins INVALID_UNCOMP_SIZE   = {INVALID_UNCOMP_SIZE};
  }

  cp_subheader_compressed_len: coverpoint clen iff (is_subheader) {  // compressed length for a subheader
    bins LEN_MINIMUM   = {[1   :1024]};
    bins LEN_MID_LOW   = {[1025:2048]};
    bins LEN_MID_HIGH  = {[2049:3072]};
    bins LEN_MAXIMUM   = {[3078:4096]};
  }

  cp_subheader_uncompressed_len: coverpoint ulen iff (is_subheader) {  // ucompressed length for a subheader
    bins LEN_MINIMUM   = {[1   :1024]};
    bins LEN_MID_LOW   = {[1025:2048]};
    bins LEN_MID_HIGH  = {[2049:3072]};
    bins LEN_MAXIMUM   = {[3078:4096]};
  }

  cp_total_uncompressed_len: coverpoint ulen iff (!is_subheader) {  // total uncompressed length
    bins LEN_MINIMUM   = {[1   :1024]};
    bins LEN_MID_LOW   = {[1025:2048]};
    bins LEN_MID_HIGH  = {[2049:3072]};
    bins LEN_MAXIMUM   = {[3078:4096]};
  }

endgroup
