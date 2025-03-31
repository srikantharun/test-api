local a = vim.api
local controlbar = require("fw_trace_utils.controlbar")
local loclist = require("fw_trace_utils.loclist")
local dump = require("fw_trace_utils.dump")
local sources = require("fw_trace_utils.sources")
local disassembly = require("fw_trace_utils.disassembly")
local utils = require("fw_trace_utils.utils")

local M = {}
local L = {}
local hart_info = {
  __index = function(table, key)
    return table[vim.t.hart_id][key]
  end,
  __newindex = function(table, key, value)
    table[vim.t.hart_id][key] = value
  end,
}

local default_keymaps = {
  prev_func = "[l",
  next_func = "]l",
  jump_to_main = "]m",
  reload = nil,
  quit = nil,
  function_calls = "C",
  source_code = "S",
  toggle_sync_cores = nil,
}

local enable_glyphs = false
local initial_jump_line = nil

----------------------------------------------------------------
-- functions
----------------------------------------------------------------
local function get_dump_address_and_time()
  local address_and_time = nil
  a.nvim_win_call(hart_info.dump_win, function()
    local cur_line = vim.fn.getcurpos()[2]
    address_and_time = hart_info.line_number_to_address_and_time[cur_line]
  end)
  return address_and_time
end

local function move_disassembly_cursor()
  local address = get_dump_address_and_time()[1]
  if address then
    local line_number = hart_info.disassembly_address_to_line_number[address]
    disassembly.move_cursor(hart_info.disassembly_win, line_number)
  end
end

local function update_source()
  if hart_info.source_win then
    local address = get_dump_address_and_time()[1]
    local file_path, file_line = utils.get_source(address, hart_info.bin_path)
    hart_info.source_buf = sources.open(hart_info.source_win, file_path, file_line)
    hart_info.src_path = file_path
    hart_info.src_line = file_line
  end
end

local function move_dump_cursor_update_all(dump_line, dump_column, do_sync_cores)
  local dump_win = hart_info.dump_win
  if dump_line >= 0 then
    dump.move_cursor(dump_win, dump_line, dump_column)
    hart_info.dump_prev_line = dump_line
  else
    local cur_line = vim.fn.getcurpos()[2]
    dump_line = cur_line
  end
  move_disassembly_cursor()
  update_source()
  loclist.update_selected_entry(dump_win, dump_line)
  if do_sync_cores and vim.g.fw_trace_utils_sync_cores then
    L.sync_cores()
  end
end

local function toggle_source_win()
  if not hart_info.source_win then
    a.nvim_win_call(hart_info.dump_win, function()
      vim.opt.splitright = false
      vim.cmd("vsplit")
      hart_info.source_win = a.nvim_get_current_win()
    end)
    update_source()
  else
    a.nvim_win_close(hart_info.source_win, false)
    hart_info.source_win = nil
  end
  local reduced = hart_info.source_win and true or false
  controlbar.draw(hart_info.dump_win, reduced, enable_glyphs)
end

local function jump_to_main()
  local main_calls
  for name, calls in pairs(hart_info.function_calls) do
    if string.match(name, "^main$") or string.match(name, "_main$") then
      main_calls = calls
      break
    end
  end
  if main_calls then
    local start_line = main_calls[1].start_line + 1
    move_dump_cursor_update_all(start_line, hart_info.inst_addr_col, true)
  end
  a.nvim_set_current_win(hart_info.dump_win)
end

local function toggle_loclist()
  hart_info.is_loclist_opened = not hart_info.is_loclist_opened
  if hart_info.is_loclist_opened then
    loclist.open(hart_info.dump_win)
  else
    loclist.close(hart_info.dump_win)
  end
end

local function exec_win_cmd(winnr, cmd)
  a.nvim_win_call(winnr, function()
    pcall(vim.cmd, cmd)
  end)
end

-- TODO: complexity is a O(n) which might be slow on big files,
-- if this is the case we could use dichotomy for O(log(n)) complexity
local function get_dump_line_from_time(time)
  local line_number = 1
  for ln, addr_time in ipairs(hart_info.line_number_to_address_and_time) do
    local t = addr_time[2]
    if t then
      if t == time then
        line_number = ln
        break
      end
      if t > time then
        break
      end
      line_number = ln
    end
  end
  return line_number
end

-- TODO: this function assumes 1 hart_id per tab
function L.sync_cores()
  local time = get_dump_address_and_time()[2]
  if time == nil then
    return
  end
  local cur_tabpage = a.nvim_get_current_tabpage()
  for _, tabpage in pairs(a.nvim_list_tabpages()) do
    if tabpage ~= cur_tabpage then
      a.nvim_set_current_tabpage(tabpage)
      local dump_line = get_dump_line_from_time(time)
      move_dump_cursor_update_all(dump_line, 0, false)
    end
  end
  a.nvim_set_current_tabpage(cur_tabpage)
end

local function toggle_sync_cores()
  vim.g.fw_trace_utils_sync_cores = not vim.g.fw_trace_utils_sync_cores
  if vim.g.fw_trace_utils_sync_cores then
    a.nvim_set_hl(0, "CursorLine", { link = "DiffText" })
    L.sync_cores()
  else
    a.nvim_set_hl(0, "CursorLine", { link = "DiffAdd" })
  end
end

_G._fw_trace_utils = {
  prev_func = function()
    exec_win_cmd(hart_info.dump_win, "silent lprev")
  end,
  next_func = function()
    exec_win_cmd(hart_info.dump_win, "silent lnext")
  end,
  main = jump_to_main,
  reload = function()
    vim.cmd("!echo " .. hart_info.dump_prev_line .. " > .fw_trace_utils_reload")
    vim.cmd("qa")
  end,
  quit = function()
    vim.cmd("qa")
  end,
  function_calls = toggle_loclist,
  source_code = function()
    -- update_source_buf_from_current_word_address(true)
    toggle_source_win()
  end,
  toggle_sync_cores = toggle_sync_cores,
}

local function init_loclist(function_calls)
  local fn_call_loclist = {}
  for fname, calls in pairs(function_calls) do
    for _, call in pairs(calls) do
      -- set real line numbers
      table.insert(fn_call_loclist, {
        bufnr = hart_info.dump_buf,
        lnum = call.start_line + 1,
        col = hart_info.inst_addr_col + 1,
        text = fname,
      })
    end
  end

  loclist.set(hart_info.dump_win, fn_call_loclist)
end

local function set_ui()
  -- Open dump file in central window
  hart_info.dump_win = a.nvim_get_current_win()
  hart_info.dump_buf = dump.open(hart_info.dump_win, hart_info.inst_dump_path, hart_info.function_calls)
  controlbar.draw(hart_info.dump_win, false, enable_glyphs)

  -- Open disassembly on the right
  vim.opt.splitright = true
  vim.cmd("vsplit")
  hart_info.disassembly_win = a.nvim_get_current_win()
  hart_info.disassembly_buf = disassembly.open(hart_info.disassembly_win, hart_info.disassembly_path)

  -- Set location list
  init_loclist(hart_info.function_calls)

  -- Jump to main / jump_line
  if initial_jump_line == nil then
    jump_to_main()
  else
    move_dump_cursor_update_all(initial_jump_line, hart_info.inst_addr_col, true)
    a.nvim_set_current_win(hart_info.dump_win)
  end

  -- cursorline
  ---- override custom autocommand that only set cusorline in current window
  pcall(a.nvim_clear_autocmds, { group = "CursorLine" })
  utils.set_local_and_global_option_in_tab("cursorline", true)
  ---- change cursor highlight
  a.nvim_set_hl(0, "CursorLine", { link = "DiffAdd" })
  -- don't display tabs etc
  utils.set_local_and_global_option_in_tab("list", false)
end

local function exec_user_config()
  package.path = os.getenv("HOME") .. "/.config/?.lua;" .. package.path
  local has_cfg, keymaps = pcall(require, "fw_trace_utils.config")
  if has_cfg then
    keymaps = keymaps or {}
    keymaps = vim.tbl_deep_extend("keep", keymaps, default_keymaps)
  else
    keymaps = default_keymaps
  end

  -- NOTE: Mappings are now window-wide
  for k, _ in pairs(_G._fw_trace_utils) do
    if keymaps[k] then
      pcall(vim.keymap.del, "n", keymaps[k])
      vim.keymap.set("n", keymaps[k], _G._fw_trace_utils[k])
    end
  end
end

local function set_commands()
  -- fast update on CursorHold
  vim.opt.updatetime = 100

  -- move disassembly and source: automatic
  a.nvim_create_autocmd("CursorHold", {
    buffer = hart_info.dump_buf,
    callback = function()
      local cur_line = vim.fn.getcurpos()[2]
      if cur_line ~= hart_info.dump_prev_line then
        hart_info.dump_prev_line = cur_line
        move_dump_cursor_update_all(-1, -1, true)
      end
    end,
  })

  a.nvim_create_autocmd("WinClosed", {
    callback = function(opts)
      local winnr = tonumber(opts.file)
      if hart_info.source_win and (hart_info.source_win == winnr) then
        hart_info.source_win = nil
      end
    end,
  })
end

----------------------------------------------------------------
-- execution
----------------------------------------------------------------
function M.setup(fw_trace_utils_info)
  enable_glyphs = fw_trace_utils_info.enable_glyphs
  initial_jump_line = fw_trace_utils_info.initial_jump_line

  vim.cmd("silent !rm -f .fw_trace_utils_reload")

  setmetatable(hart_info, hart_info)

  for tab_nb, json_file in ipairs(fw_trace_utils_info.hart_info) do
    local info = utils.read_json_file(json_file)
    if info == nil then
      return
    end

    info.line_number_to_address_and_time =
      utils.convert_table_string_key_to_number(info.line_number_to_address_and_time)

    -- add new tab
    if tab_nb >= 2 then
      vim.cmd("tabedit")
    end
    -- set tab/hart_id info
    -- Use rawset to avoid triggering '__newindex'
    rawset(hart_info, info.hart_id, info)
    vim.t.hart_id = info.hart_id
    vim.t.tabname = "hart_id #" .. info.hart_id
    -- change appearance and setup winbar
    set_ui()
    -- set autocommands and mappings
    set_commands()
  end

  -- Read user configuration
  -- If lazy.nvim is used, process mappings once all plugins have been setup
  if pcall(require, "lazy") then
    vim.api.nvim_create_autocmd("User", {
      pattern = "*",
      callback = function(ev)
        if ev.file == "VeryLazy" then
          exec_user_config()
        end
      end,
    })
  else
    exec_user_config()
  end

  vim.cmd("mode") -- fix display artifacts with the controlbar
end

return M
