# This script has the reference for address generation. it receives the command recipe (it's either LINEAR or 4DIM FALLBACK), and output a list of addresses, masks, pad values
import json
import sys
import os

cmd_file_path = "cmd.json"
addresses_output_path = "output.txt"
pword_len = 64
vtrsp_mode_dict = {0:"OFF", 1:"INT8", 2:"FP16", 3:"FP32"}
vtrsp_creation_recipe_path = "vtrsp_rescipe.json"

class IFD_ODR_CMD:
  # create all necessary fields. all that's not mandatory will be zeroed.
  def __init__(
      self,
      cmd_type,
      mem_baseaddr=0,
      length=0,
      compression=0,
      pad_val=0,
      intra_pad_val=0,
      mem_offset=0,
      ring_buf_size=0,
      num_dim=0,
      vect_dim=0,
      vtrsp_mode=0,
      pad_mode=0,
      format=0,
      mask_start=0,
      mask_end=0,
      mem_bsize=0,
      dim_offset_a=0,
      dim_width_a=0,
      mem_stride_a=0,
      inner_length_a=0,
      inner_stride_a=0,
      outer_length_a=0,
      outer_stride_a=0,
      dim_offset_b=0,
      dim_width_b=0,
      mem_stride_b=0,
      inner_length_b=0,
      inner_stride_b=0,
      outer_length_b=0,
      outer_stride_b=0,
      dim_offset_c=0,
      dim_width_c=0,
      mem_stride_c=0,
      inner_length_c=0,
      inner_stride_c=0,
      outer_length_c=0,
      outer_stride_c=0,
      dim_offset_d=0,
      dim_width_d=0,
      mem_stride_d=0,
      inner_length_d=0,
      inner_stride_d=0,
      outer_length_d=0,
      outer_stride_d=0
      ):
    self.cmd_type = cmd_type
    self.mem_baseaddr = mem_baseaddr
    self.length = length
    self.compression = compression
    self.pad_val = pad_val
    self.intra_pad_val = intra_pad_val
    self.mem_offset = mem_offset
    self.ring_buf_size = ring_buf_size
    self.num_dim = num_dim
    self.vect_dim = vect_dim
    self.vtrsp_mode = vtrsp_mode
    self.pad_mode = pad_mode
    self.format = format
    self.mask_start = mask_start
    self.mask_end = mask_end
    self.mem_bsize = mem_bsize

    # dim a parameters
    self.dim_offset_a = dim_offset_a
    self.dim_width_a = dim_width_a
    self.mem_stride_a = mem_stride_a
    self.inner_length_a = inner_length_a
    self.inner_stride_a = inner_stride_a
    self.outer_length_a = outer_length_a
    self.outer_stride_a = outer_stride_a

    # dim b parameters
    self.dim_offset_b = dim_offset_b
    self.dim_width_b = dim_width_b
    self.mem_stride_b = mem_stride_b
    self.inner_length_b = inner_length_b
    self.inner_stride_b = inner_stride_b
    self.outer_length_b = outer_length_b
    self.outer_stride_b = outer_stride_b

    # dim c parameters
    self.dim_offset_c = dim_offset_c
    self.dim_width_c = dim_width_c
    self.mem_stride_c = mem_stride_c
    self.inner_length_c = inner_length_c
    self.inner_stride_c = inner_stride_c
    self.outer_length_c = outer_length_c
    self.outer_stride_c = outer_stride_c

    # dim d parameters
    self.dim_offset_d = dim_offset_d
    self.dim_width_d = dim_width_d
    self.mem_stride_d = mem_stride_d
    self.inner_length_d = inner_length_d
    self.inner_stride_d = inner_stride_d
    self.outer_length_d = outer_length_d
    self.outer_stride_d = outer_stride_d

  def __str__(self):
    return (
        f'{{"dim_offset_a": {self.dim_offset_a}, "dim_offset_b": {self.dim_offset_b}, "dim_offset_c": {self.dim_offset_c}, "dim_offset_d": {self.dim_offset_d}, "dim_width_a": {self.dim_width_a}, '
        f'"dim_width_b": {self.dim_width_b}, "dim_width_c": {self.dim_width_c}, "dim_width_d": {self.dim_width_d}, "mem_stride_a": {self.mem_stride_a}, "mem_stride_b": {self.mem_stride_b}, '
        f'"mem_stride_c": {self.mem_stride_c}, "mem_stride_d": {self.mem_stride_d}, "inner_length_a": {self.inner_length_a}, "inner_length_b": {self.inner_length_b}, "inner_length_c": {self.inner_length_c}, '
        f'"inner_length_d": {self.inner_length_d}, "inner_stride_a": {self.inner_stride_a}, "inner_stride_b": {self.inner_stride_b}, "inner_stride_c": {self.inner_stride_c}, "inner_stride_d": {self.inner_stride_d}, '
        f'"outer_length_a": {self.outer_length_a}, "outer_length_b": {self.outer_length_b}, "outer_length_c": {self.outer_length_c}, "outer_length_d": {self.outer_length_d}, "outer_stride_a": {self.outer_stride_a}, '
        f'"outer_stride_b": {self.outer_stride_b}, "outer_stride_c": {self.outer_stride_c}, "outer_stride_d": {self.outer_stride_d}, "mem_baseaddr": {self.mem_baseaddr}, "pad_val": {self.pad_val}, "mask_start": {self.mask_start}, '
        f'"mask_end": {self.mask_end}, "mem_offset": {self.mem_offset}, "ring_buf_size": {self.ring_buf_size}, "vect_dim": {self.vect_dim}, "vtrsp_mode": {self.vtrsp_mode}, "pad_mode": {self.pad_mode}, "format": {self.format}, '
        f'"mem_bsize": {self.mem_bsize}, "compression": {self.compression}}}' 
    )
  

# -- Auxiliary functions:
def ringbuffer_remap(absolute_buffer_offset, ring_buf_size):
    # compute ring buffer folding
    return absolute_buffer_offset % ring_buf_size

# this is the main reference function!
def create_dp_command_stream(
    cmd,  # this function should only get linear or 4 dim commands!
    use_offset_as_physical_address: bool = False
):
  mem_baseaddr = cmd.mem_baseaddr  # lets start with the simple case, we use baseaddr and not offset!

  if cmd.cmd_type == "LINEAR":
      dp_ctrl_strm = [
          (
              mem_baseaddr + i * pword_len,
              False,
              [True for _ in range(pword_len)],
              0,
              0
          )
          for i in range(cmd.length)
      ]
      return dp_ctrl_strm, False, cmd.compression # return - ctrl stream, vtrsp mode, compression

  # Static Constants
  PWORD_len = pword_len  # number of elements in PWORD

  

  # ring buffer enabled iff size != 0
  ring_buffer_enable = cmd.ring_buf_size != 0

  # segmentation fault check enabled iff size != 0
  seg_fault_check_enable = cmd.mem_bsize != 0

  # -- Address Stream Generation (including PWORD Padding) --
  # (datapath control stream)
  dp_ctrl_strm = []

  # Outer 2D loop (scan grid)
  for outer_idx_a in range(cmd.outer_length_a):
      for outer_idx_b in range(cmd.outer_length_b):
          # Outer C loop (PWORD alignment)
          for outer_idx_c in range(cmd.outer_length_c):
              # Extra outer loop (no 2D equivalent)
              for outer_idx_d in range(cmd.outer_length_d):
                  # Inner 2D loop (kernel/outpatch)
                  for inner_idx_a in range(cmd.inner_length_a):
                      for inner_idx_b in range(cmd.inner_length_b):
                          # Extra inner loop (no 2D equivalent)
                          for inner_idx_c in range(cmd.inner_length_c):
                              # Extra inner loop (no 2D equivalent)
                              for inner_idx_d in range(cmd.inner_length_d):
                                  # coordinate computation
                                  # NOTE: multiplications can be implemented with incremental multiplication instead of full multiplier
                                  # IMPL: does not need to exceed dim_width 16-bit -> limit bit width
                                  # IMPL: = 16b*8b + 16b*8b + 16b = (limit result to 17b?) -> cooord limited to -65535 to 65535?
                                  # IMPL: needs signed for padding
                                  coord_a = (
                                      (inner_idx_a * cmd.inner_stride_a)
                                      + (outer_idx_a * cmd.outer_stride_a)
                                      + cmd.dim_offset_a
                                  )  # dim_offset_a = -p_t + off_a
                                  coord_b = (
                                      (inner_idx_b * cmd.inner_stride_b)
                                      + (outer_idx_b * cmd.outer_stride_b)
                                      + cmd.dim_offset_b
                                  )  # dim_offset_b = -p_l + off_b
                                  coord_c = (
                                      (inner_idx_c * cmd.inner_stride_c)
                                      + (outer_idx_c * cmd.outer_stride_c)
                                      + cmd.dim_offset_c
                                  )  # dim_offset_c = -p_l + off_c
                                  coord_d = (
                                      (inner_idx_d * cmd.inner_stride_d)
                                      + (outer_idx_d * cmd.outer_stride_d)
                                      + cmd.dim_offset_d
                                  )  # dim_offset_d = -p_l + off_d

                                  # PAD/DROP on vector level (aka PWORD)
                                  # is coordinate in data structure (IFD: pad, ODR: drop)
                                  # Comparators:
                                  # NOTE: MUST WORK FOR DIM=0!! see https://git.axelera.ai/dev/rd/IntraCoreDataFlow/-/issues/12#note_4587
                                  # NOTE: vectorized dimension can not be edge-padded, see https://git.axelera.ai/ai-hw-team/triton/-/issues/1063#note_51060
                                  u_a = coord_a < 0
                                  o_a = (
                                      coord_a > cmd.dim_width_a - 1
                                  )  # NOTE: most work correctly for dim_width_a == 0
                                  u_b = coord_b < 0
                                  o_b = (
                                      coord_b > cmd.dim_width_b - 1
                                  )  # NOTE: most work correctly for dim_width_b == 0
                                  u_c = coord_c < 0
                                  o_c = (
                                      coord_c > cmd.dim_width_c - 1
                                  )  # NOTE: most work correctly for dim_width_c == 0
                                  u_d = coord_d < 0
                                  o_d = (
                                      coord_d > cmd.dim_width_d - 1
                                  )  # NOTE: most work correctly for dim_width_d == 0
                                  under_lst = [u_a, u_b, u_c, u_d]
                                  over_lst = [o_a, o_b, o_c, o_d]
                                  # Edge Padding (Replicate-Padding)
                                  if cmd.pad_mode:
                                      if u_a and cmd.vect_dim != 0:
                                          coord_a = 0
                                      if o_a and cmd.vect_dim != 0:
                                          coord_a = cmd.dim_width_a - 1
                                      if u_b and cmd.vect_dim != 1:
                                          coord_b = 0
                                      if o_b and cmd.vect_dim != 1:
                                          coord_b = cmd.dim_width_b - 1
                                      if u_c and cmd.vect_dim != 2:
                                          coord_c = 0
                                      if o_c and cmd.vect_dim != 2:
                                          coord_c = cmd.dim_width_c - 1
                                      if u_d and cmd.vect_dim != 3:
                                          coord_d = 0
                                      if o_d and cmd.vect_dim != 3:
                                          coord_d = cmd.dim_width_d - 1
                                      # drop values if vectorized dimension is out of boundaries (ODR)
                                      # NOTE: padding values are overridden by intra_pw_mask (IFD)
                                      pad_drop = under_lst[cmd.vect_dim] or over_lst[cmd.vect_dim]
                                  # Default padding
                                  else:
                                      pad_drop = u_a or o_a or u_b or o_b or u_c or o_c or u_d or o_d

                                  # PAD/DROP within vector   (aka within PWORD = STRB)
                                  # NOTE: intra_pw_mask is applied based only on vectorized dimension, see https://git.axelera.ai/ai-hw-team/triton/-/issues/1063#note_51060
                                  curr_mask_start = 0
                                  curr_mask_end = PWORD_len
                                  # select vectorized dimension
                                  coords_lst = [coord_a, coord_b, coord_c, coord_d]
                                  dim_widths_lst = [
                                      cmd.dim_width_a,
                                      cmd.dim_width_b,
                                      cmd.dim_width_c,
                                      cmd.dim_width_d,
                                  ]
                                  vect_coord = coords_lst[cmd.vect_dim]
                                  vect_dim_width = dim_widths_lst[cmd.vect_dim]
                                  # apply sub-PW padding mask if at boundaries
                                  if vect_coord == 0:
                                      if cmd.format == 1:  # shifting for int16 format mask, need to return it to 64 bits, so we limit to 7 bits
                                          curr_mask_start = ((cmd.mask_start << 1) & 0x7F)
                                      else:
                                          curr_mask_start = cmd.mask_start
                                  if vect_coord == vect_dim_width - 1:
                                      if cmd.format == 1:  # shifting for int16 format mask
                                          curr_mask_end = ((cmd.mask_end << 1) & 0x7F)
                                      else:
                                          curr_mask_end = cmd.mask_end
                                  # apply blocking padding mask if out of boundaries
                                  if under_lst[cmd.vect_dim] or over_lst[cmd.vect_dim]:
                                      curr_mask_start = 0
                                      curr_mask_end = 0
                                  # convert to bitmask
                                  intra_pw_mask_bf = [False] * PWORD_len
                                  for cidx in range(curr_mask_start, curr_mask_end):
                                      intra_pw_mask_bf[cidx] = True

                                  # Address Translation (offset)
                                  # everyhing in bytes
                                  # -> Memory ordering is no longer relevant

                                  # compute buffers offset from coordinates
                                  # NOTE: for mem_stride_x*coord_x can also be implemented with incremental multiplication instead of full multiplier [not trivial]
                                  # IMPL:               =          32b*17b     +          32b*17b     +          32b*17b     +          32b*17b     + 32b
                                  #  MULT: 32b x 16b only taking 35:0 bits at output
                                  #  Since we are PWORD aligned 5:0 bits mem_stride_x/offset input is 0
                                  absolute_buffer_offet = (
                                      cmd.mem_stride_a * coord_a
                                      + cmd.mem_stride_b * coord_b
                                      + cmd.mem_stride_c * coord_c
                                      + cmd.mem_stride_d * coord_d
                                      + cmd.mem_offset
                                  )

                                  # Ring buffers support
                                  if ring_buffer_enable:
                                      # see https://git.axelera.ai/dev/rd/IntraCoreDataFlow/-/issues/16
                                      buffer_offset = ringbuffer_remap(absolute_buffer_offet, cmd.ring_buf_size)
                                  else:
                                      buffer_offset = absolute_buffer_offet

                                  # Compute global address
                                  # IMPL: 36b = 36b + 36b
                                  addr = mem_baseaddr + buffer_offset
                                  # Address validity check
                                  if seg_fault_check_enable:
                                      # do not check if pad/drop
                                      if not pad_drop:
                                          assert (
                                              mem_baseaddr <= addr and addr < mem_baseaddr + cmd.mem_bsize
                                          ), f"Segmentation Fault in AddrGen for coord (a,b,c,d) = '{(coord_a, coord_b, coord_c, coord_d)}' => addr=base+off={mem_baseaddr}+{buffer_offset}={addr}"

                                  # DP ctrl cmd:
                                  # (addr_offset, pad (no loading), intra_c_mask)
                                  dp_ctrl_strm.append(
                                      (addr if not pad_drop else None, pad_drop, intra_pw_mask_bf, cmd.pad_val, cmd.intra_pad_val),
                                  )

  return dp_ctrl_strm, cmd.vtrsp_mode, False


# write output to file
def write_output(output_path, cmd_hw, data_list):
  vtrsp_creation_recipe = dict()  # create this dictionary, to write it later to another file, that will be used for vtrsp creation
  vtrsp_creation_recipe["vtrsp_mode"] = vtrsp_mode_dict[cmd_hw.vtrsp_mode]
  vtrsp_creation_recipe["vtrsp_addresses"] = []
  vtrsp_creation_recipe["vtrsp_masks"] = []
  vtrsp_creation_recipe["vtrsp_padding"] = []
  with open(output_path, 'w') as output_file:
    output_file.write(str(cmd_hw)+'\n')  # writing the header - info about the source cmd
    for idx, entry in enumerate(data_list):
        # Extract values from each entry
        addr = entry[0] if entry[0] is not None else 0  # Set to 0 if None
        pad_drop = entry[1]
        mask = entry[2][::-1]
        pad_val = entry[3]
        intra_pad_val = entry[4]

        # Convert addr to 8-digit hexadecimal
        addr_hex = f"{addr:08X}"

        # Convert mask list of booleans to a 64-bit hexadecimal value
        mask_bits = ''.join(['1' if bit else '0' for bit in mask])
        mask_hex = f"{int(mask_bits, 2):016X}"

        # Convert pad_drop to 1 or 0 (boolean to bit)
        pad_bit = 1 if pad_drop else 0

        # Convert pad_val to 4-digit hexadecimal
        pad_val_hex = f"{pad_val & 0xFFFF:04X}"

        # Convert intra_pad_val to 4-digit hexadecimal
        intra_pad_val_hex = f"{intra_pad_val & 0xFFFF:04X}"

        # Print the formatted output
        output_file.write(f"#{idx} addr: {addr_hex} msk: {mask_hex} pad: {pad_bit} pad_val: {pad_val_hex}\n")

        vtrsp_creation_recipe["vtrsp_addresses"].append(addr)
        vtrsp_creation_recipe["vtrsp_masks"].append(mask_bits)
        vtrsp_creation_recipe["vtrsp_padding"].append(intra_pad_val_hex)
  with open(vtrsp_creation_recipe_path, 'w') as file:
    json.dump(vtrsp_creation_recipe, file, indent=2)

def create_linear_cmd(command_json):
  cmd_type = command_json['cmd_type']  # No default value here
  mem_baseaddr = command_json.get('mem_baseaddr', 0)
  length = command_json.get('length', 0)
  compression = command_json.get('compression', 0)
  cmd_hw = IFD_ODR_CMD(
    cmd_type = cmd_type,
    mem_baseaddr=mem_baseaddr,
    length=length,
    compression=compression
  )
  return cmd_hw

def create_four_dim_cmd(command_json):
  """
  Simple idea, testbench gives us what's necessary for the command we're running, and we're expanding the rest with default values!
  """
  cmd_type = command_json['cmd_type']  # No default value here
  mem_baseaddr = command_json.get('mem_baseaddr', 0)
  pad_val = command_json.get('pad_val', 0)
  intra_pad_val = command_json.get('intra_pad_val', 0)
  mem_offset = command_json.get('mem_offset', 0)
  ring_buf_size = command_json.get('ring_buf_size', 0)
  num_dim = command_json.get('num_dim', 0)
  vect_dim = command_json.get('vect_dim', 0)
  vtrsp_mode = command_json.get('vtrsp_mode', 0)
  pad_mode = command_json.get('pad_mode', 0)
  format = command_json.get('format', 0)
  mask_start = command_json.get('mask_start', 0)
  mask_end = command_json.get('mask_end', 0)
  mem_bsize = command_json.get('mem_bsize', 0)

  dim_width_a = command_json.get('dim_width_a', 1)
  dim_width_b = command_json.get('dim_width_b', 1)
  dim_width_c = command_json.get('dim_width_c', 1)
  dim_width_d = command_json.get('dim_width_d', 1)

  dim_offset_a = command_json.get('dim_offset_a', 0)
  dim_offset_b = command_json.get('dim_offset_b', 0)
  dim_offset_c = command_json.get('dim_offset_c', 0)
  dim_offset_d = command_json.get('dim_offset_d', 0)

  inner_length_a = command_json.get('inner_length_a', 1)
  inner_length_b = command_json.get('inner_length_b', 1)
  inner_length_c = command_json.get('inner_length_c', 1)
  inner_length_d = command_json.get('inner_length_d', 1)

  outer_length_a = command_json.get('outer_length_a', 1)
  outer_length_b = command_json.get('outer_length_b', 1)
  outer_length_c = command_json.get('outer_length_c', 1)
  outer_length_d = command_json.get('outer_length_d', 1)

  mem_stride_a = command_json.get('mem_stride_a', 0)
  mem_stride_b = command_json.get('mem_stride_b', 0)
  mem_stride_c = command_json.get('mem_stride_c', 0)
  mem_stride_d = command_json.get('mem_stride_d', 0)

  inner_stride_a = command_json.get('inner_stride_a', 1)
  inner_stride_b = command_json.get('inner_stride_b', 1)
  inner_stride_c = command_json.get('inner_stride_c', 1)
  inner_stride_d = command_json.get('inner_stride_d', 1)

  outer_stride_a = command_json.get('outer_stride_a', 1)
  outer_stride_b = command_json.get('outer_stride_b', 1)
  outer_stride_c = command_json.get('outer_stride_c', 1)
  outer_stride_d = command_json.get('outer_stride_d', 1)

  cmd_hw = IFD_ODR_CMD(
    cmd_type = cmd_type,
    mem_baseaddr=mem_baseaddr,
    pad_val = pad_val,
    intra_pad_val = intra_pad_val,
    mem_offset = mem_offset,
    ring_buf_size = ring_buf_size,
    num_dim = num_dim,
    vect_dim = vect_dim,
    vtrsp_mode = vtrsp_mode,
    pad_mode = pad_mode,
    format = format,
    mask_start = mask_start,
    mask_end = mask_end,
    mem_bsize = mem_bsize,

    # dim width parameters
    dim_width_a = dim_width_a,
    dim_width_b = dim_width_b,
    dim_width_c = dim_width_c,
    dim_width_d = dim_width_d,

    # dim offset parameters
    dim_offset_a = dim_offset_a,
    dim_offset_b = dim_offset_b,
    dim_offset_c = dim_offset_c,
    dim_offset_d = dim_offset_d,

    # inner length parameters
    inner_length_a = inner_length_a,
    inner_length_b = inner_length_b,
    inner_length_c = inner_length_c,
    inner_length_d = inner_length_d,

    # outer length parameters
    outer_length_a = outer_length_a,
    outer_length_b = outer_length_b,
    outer_length_c = outer_length_c,
    outer_length_d = outer_length_d,

    # mem stride parameters
    mem_stride_a = mem_stride_a,
    mem_stride_b = mem_stride_b,
    mem_stride_c = mem_stride_c,
    mem_stride_d = mem_stride_d,

    # inner stride parameters
    inner_stride_a = inner_stride_a,
    inner_stride_b = inner_stride_b,
    inner_stride_c = inner_stride_c,
    inner_stride_d = inner_stride_d,

    # outer stride parameters
    outer_stride_a = outer_stride_a,
    outer_stride_b = outer_stride_b,
    outer_stride_c = outer_stride_c,
    outer_stride_d = outer_stride_d
  )
  return cmd_hw


def read_json_config(file_path):
  # Open and read the JSON file
  with open(file_path, 'r') as file:
    # Load the JSON content
    command_json = json.load(file)

    # Extract values if they exist
    cmd_type = command_json['cmd_type']  # No default value here
    if cmd_type == "LINEAR":
      return create_linear_cmd(command_json)
    else:
      return create_four_dim_cmd(command_json)


if __name__ == "__main__":
  # Check if exactly two arguments are provided
  if len(sys.argv) != 3:
    print("Usage: python script_name.py <input json file> <output_file>")
    sys.exit(1)  # Exit the script with an error code
  cmd_file_path = sys.argv[1]
  addresses_output_path = sys.argv[2]
  vtrsp_creation_recipe_path = os.path.join(os.path.dirname(addresses_output_path), "vtrsp_recipe.json")  # will be same folder as output, but different name
  unpacked_cmd = read_json_config(cmd_file_path)
  [dp_ctrl_strm, vtrsp_mode, compression] = create_dp_command_stream(unpacked_cmd)
  write_output(addresses_output_path, unpacked_cmd, dp_ctrl_strm)
  print(f"REFERENCE MODEL: done generating cmd addresses with final legnth {len(dp_ctrl_strm)}")

