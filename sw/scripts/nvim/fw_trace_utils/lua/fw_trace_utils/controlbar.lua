local utils = require("fw_trace_utils.utils")
local a = vim.api
local M = {}

local winbar_elems = {
  {
    func = "prev_func",
    icon = "󰒫",
    text = "Prev call",
    hl = "Function",
  },
  {
    func = "next_func",
    icon = "󰒬",
    text = "Next call",
    hl = "Function",
  },
  {
    func = "main",
    icon = "",
    text = "Main",
    hl = "Function",
  },
  {
    func = "function_calls",
    icon = "󰓌",
    text = "List calls",
    hl = "Special",
  },
  {
    func = "source_code",
    icon = "󰈮",
    text = "Source code",
    hl = "Special",
  },
  {
    func = "toggle_sync_cores",
    icon = "♻",
    text = "Sync Cores",
    hl = "Identifier",
  },
  {
    func = "reload",
    icon = "🔃",
    text = "Reload",
    hl = "Statement",
  },
  {
    func = "quit",
    icon = "",
    text = "Quit",
    hl = "Statement",
  },
}

local function display_text(element, reduced_mode, display_icons)
  local text
  if reduced_mode then
    text = display_icons and element.icon or string.gmatch(element.text, "[^%s]+")()
  else
    text = element.text
    if display_icons then
      text = element.icon .. " " .. text
    end
  end

  return text
end

function M.draw(winnr, reduced_mode, enable_glyphs)
  local bar = ""
  for _, elem in ipairs(winbar_elems) do
    bar = bar
      .. ("  %%#%s#%%0@v:lua._fw_trace_utils.%s@%s%%#0#"):format(
        elem.hl,
        elem.func,
        display_text(elem, reduced_mode, enable_glyphs)
      )
  end

  bar = "%=" .. bar .. "%="

  a.nvim_win_set_option(winnr, "winbar", bar)
end

return M
