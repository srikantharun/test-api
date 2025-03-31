local root_path = os.getenv("REPO_ROOT") .. "/sw/scripts/nvim/fw_trace_utils/lua/?/init.lua"
local module_path = os.getenv("REPO_ROOT") .. "/sw/scripts/nvim/fw_trace_utils/lua/?.lua"

package.path = package.path .. ";" .. root_path .. ";" .. module_path

require("fw_trace_utils").setup(_G.fw_trace_utils_info)
