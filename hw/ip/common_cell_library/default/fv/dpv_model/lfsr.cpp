#include "Hector.h"
#include "stdint.h"

class LFSR16 {
private:
  uint16_t flipGranularity = 8;
public:
  void get_next(uint16_t seed, bool flip_enable, uint8_t mask_select, uint16_t mask_and, uint16_t mask_or, uint16_t &state_o, uint16_t &data_o) {
    uint16_t lfsr;
    uint16_t data_rot;
    uint16_t data_masked;
    uint16_t c = seed;
    uint16_t bit = (c ^ (c >> 1) ^ (c >> 3) ^ (c >> 12)) & 1;
    lfsr = (c >> 1) | (bit << 15);

    if(flip_enable) {
      data_rot = lfsr >> this->flipGranularity | lfsr << this->flipGranularity;
    } else {
      data_rot = lfsr;
    }
    switch(mask_select){
      case 1: data_masked = data_rot & mask_and; break;
      case 2: data_masked =  data_rot | mask_or; break;
      default: data_masked = data_rot; break;
    }
    state_o = lfsr;
    data_o = data_masked;
    Hector::show("lfsr", lfsr);
    Hector::show("data_rot", data_rot);
    Hector::show("data_masked", data_masked);
  }
};


void DPV_wrapper ()
{
   uint16_t seed;
   uint16_t state_o;
   bool flip_enable_i;
   uint8_t mask_select_i;
   uint16_t mask_and_i;
   uint16_t mask_or_i;
   uint16_t data_o;
   LFSR16 myObj;
   //LFSR16 myObj(seed);
   Hector::registerInput("seed", seed);
   Hector::registerInput("flip_enable_i", flip_enable_i);
   Hector::registerInput("mask_select_i", mask_select_i);
   Hector::registerInput("mask_and_i", mask_and_i);
   Hector::registerInput("mask_or_i", mask_or_i);
   Hector::registerOutput("state_o", state_o);
   Hector::registerOutput("data_o", data_o);
   Hector::beginCapture();
   //state_o = myObj.get_next();
   myObj.get_next(seed, flip_enable_i, mask_select_i, mask_and_i, mask_or_i, state_o, data_o);
   Hector::endCapture();
    
}
