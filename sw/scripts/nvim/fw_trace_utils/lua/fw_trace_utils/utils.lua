local a = vim.api
local M = {}

function M.set_local_and_global_option_in_tab(name, value)
  a.nvim_set_option_value(name, value, { scope = "global" })
  for _, window in ipairs(a.nvim_tabpage_list_wins(0)) do
    a.nvim_set_option_value(name, value, { win = window })
  end
end

function M.run_bash(command)
  local handle = io.popen(command)
  if handle then
    local result = handle:read("*a")
    handle:close()
    return result
  end
  return ""
end

function M.string_split(inputstr, sep)
  if sep == nil then
    sep = "%s"
  end
  local t = {}
  for str in string.gmatch(inputstr, "([^" .. sep .. "]+)") do
    table.insert(t, str)
  end
  return t
end

function M.get_source(address, bin_path)
  local file_path = nil
  local file_line = nil
  if address then
    local stdout = M.run_bash("addr2line -e " .. bin_path .. " " .. address)
    stdout = string.gsub(stdout, "\n", "")
    file_path, file_line = unpack(M.string_split(stdout, ":"))
  end
  return file_path, file_line
end

function M.read_json_file(path)
  local f = io.open(path, "r")
  if f == nil then
    vim.notify("Failed to open " .. path, vim.log.levels.ERROR)
    return nil
  end
  local content = f:read("*all")
  return vim.json.decode(content, { luanil = { object = true, array = true } })
end

function M.convert_table_string_key_to_number(t)
  local t2 = {}
  for key, val in pairs(t) do
    t2[tonumber(key)] = val
  end
  t = t2
  return t
end

return M
