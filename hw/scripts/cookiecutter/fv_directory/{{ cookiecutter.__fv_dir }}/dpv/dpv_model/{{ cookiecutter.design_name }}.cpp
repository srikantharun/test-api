#include "Hector.h"
#include <stdint.h>


// Create the C++ model
// You can use classes or functions


// DPV Wrapper - mandatory to interconnect the model and the RTL
int DPV_wrapper () {
  // Declare your objects or variables used as ports
  // Example: uint32_t in_tdata_i[DEF_PWORD_SIZE];
  //          uint32_t out_tdata_o[DEF_PWORD_SIZE];
  // Or: cmd_struct dpcmd_tdata_i; - Where cmd_struct is a abstract structure of CMD
  
  // Specify which signals are inputs or outputs
  // Hector::registerInput ("in_tdata_i", in_tdata_i);
  // Hector::registerOutput ("out_tvalid_o", out_tvalid_o);
  //Hector::registerOutput ("out_tdata_o", out_tdata_o);

  Hector::beginCapture();
    // Sequence of steps to run your model
    // Calling functions or methods of your class
  
  Hector::endCapture();
  return 0;
}
