#include "Hector.h"
#include <stdint.h>

class IAU_PIXEL_DP {

public:
  uint32_t acc[8];
  bool csr_signed_operation_i;
  bool csr_saturated_add_i;
  bool vector_mode;
  uint8_t opcode;
  uint32_t i_pixel_data;

  void debug(void) {
    Hector::show("acc", this->acc);
  }

  uint32_t alu_max(uint32_t src0, uint32_t src1) {
    if(this->csr_signed_operation_i) {
      if(((src0 ^ src1) >> 31) == 1) {
        if(src0 >> 31 == 0) {
          return src0;
        } else {
          return src1;
        }
      } else {
        if(src0 > src1){
          return src0;
        } else {
          return src1;
        }
      }
    } else {
      if(src0 > src1) {
        return src0;
      } else {
        return src1;
      }
    }
  }

  uint32_t alu_min(uint32_t src0, uint32_t src1) {
    if(this->csr_signed_operation_i) {
      if(((src0 ^ src1) >> 31) == 1) {
        if(src0 >> 31 == 0) {
          return src1;
        } else {
          return src0;
        }
      } else {
        if(src0 > src1){
          return src1;
        } else {
          return src0;
        }
      }
    } else {
      if(src0 < src1) {
        return src0;
      } else {
        return src1;
      }
    }
  }

  uint32_t alu_sum(uint32_t src0, uint32_t src1) {
    uint32_t result;
    result = src0+src1;
    if(this->csr_saturated_add_i){
      if(this->csr_signed_operation_i) {
        if(((~src0 & ~src1) >> 31) == 1 && (result>>31 == 1)) {
          result = 0x7FFFFFFF;
        }
        if(((src0 & src1) >> 31) == 1 && (result>>31 == 0)) {
          result = 0x80000000;
        }
      } else {
        if(result < src0 && result < src1)
        result = 0xFFFFFFFF;
      }
    }
    return result;
  }

  uint32_t iau_alu (uint32_t src0, uint32_t src1) {
    switch(this->opcode) {
      //case 0: return src0;
      case 1: return src0;
      case 2: return alu_max(src0, src1);
      case 3: return alu_min(src0, src1);
      case 4: return this->alu_sum(src0, src1);
    }
    return src0;
  }

  void get_input(
    bool     csr_signed_operation_i,
    uint32_t i_pixel_data
  ) {
    uint32_t sign;

    this->csr_signed_operation_i = csr_signed_operation_i;

    if (csr_signed_operation_i && (((i_pixel_data >> 25) & 0x00000001) == 1)) {
      sign = 0xFC000000;
    } else {
      sign = 0x00000000;
    }
    this->i_pixel_data = (i_pixel_data & 0x03FFFFFF) | sign;

  }

  uint32_t get_src_value(uint8_t src, bool instr_src_stream) {
    uint8_t index = src & 0x7;
    if (instr_src_stream == 0) {
      return this->acc[index];
    } else {
      return this->i_pixel_data;
    }
  }

  void process_data(
    bool     csr_saturated_add_i,

    bool     vector_mode,
    uint8_t  instr_opcode,
    bool     instr_src_stream[2],
    uint8_t  instr_src_acc_reg[2],

    bool     instr_dst_used,
    bool     instr_dst_stream,
    uint8_t  instr_dst_acc_reg,

    bool     exe_instr,

    uint32_t (&o_pixel_data)
    ) {
    uint32_t src0, src1, result;
    uint8_t index;

    index = instr_dst_acc_reg & 0x7;

    this->csr_saturated_add_i = csr_saturated_add_i;
    this->vector_mode = vector_mode;
    this->opcode = instr_opcode;

    src0 = this->get_src_value(instr_src_acc_reg[0], instr_src_stream[0]);
    src1 = this->get_src_value(instr_src_acc_reg[1], instr_src_stream[1]);
    result = this->iau_alu(src0, src1);
    if((instr_dst_used == 1) && (exe_instr == 1)){
      if((instr_dst_stream == 0) && (this->opcode != 0)){
        this->acc[index] = result;
      } else {
        o_pixel_data = result;
      }
    }


    Hector::show("src0", src0);
    Hector::show("src1", src1);
    Hector::show("result", result);
  }
};

int DPV_wrapper () {
IAU_PIXEL_DP iau_pixel_dp;

bool     csr_signed_operation_i;
bool     csr_saturated_add_i;

bool     vector_mode;
uint8_t  instr_opcode;
bool     instr_src_stream[2];
uint8_t  instr_src_acc_reg[2];

bool     instr_dst_used;
bool     instr_dst_stream;
uint8_t  instr_dst_acc_reg;

bool     exe_instr;

uint32_t i_pixel_data;
uint32_t o_pixel_data;

Hector::registerInput ("csr_signed_operation_i", csr_signed_operation_i);
Hector::registerInput ("csr_saturated_add_i", csr_saturated_add_i);

Hector::registerInput ("vector_mode", vector_mode);
Hector::registerInput ("instr_opcode", instr_opcode);
Hector::registerInput ("instr_src_stream", instr_src_stream);
Hector::registerInput ("instr_src_acc_reg", instr_src_acc_reg);

Hector::registerInput ("instr_dst_used", instr_dst_used);
Hector::registerInput ("instr_dst_stream", instr_dst_stream);
Hector::registerInput ("instr_dst_acc_reg", instr_dst_acc_reg);

Hector::registerInput ("exe_instr", exe_instr);

Hector::registerInput ("i_pixel_data", i_pixel_data);
Hector::registerOutput ("o_pixel_data", o_pixel_data);



Hector::beginCapture();
  iau_pixel_dp.debug();
  iau_pixel_dp.get_input(
    csr_signed_operation_i,
    i_pixel_data
  );
  iau_pixel_dp.process_data(
    csr_saturated_add_i,
    vector_mode,
    instr_opcode,
    instr_src_stream,
    instr_src_acc_reg,
    instr_dst_used,
    instr_dst_stream,
    instr_dst_acc_reg,
    exe_instr,
    o_pixel_data
  );

Hector::endCapture();
return 0;
}
