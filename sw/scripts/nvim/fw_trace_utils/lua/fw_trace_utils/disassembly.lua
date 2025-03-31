local a = vim.api
local M = {}

-- Open disassembly buffer and sets some sensible options
-- returns the corresponding buffer number
function M.open(winnr, file_path)
  local bufnr = nil
  a.nvim_win_call(winnr, function()
    vim.cmd("view " .. file_path)
    bufnr = a.nvim_get_current_buf()
  end)
  return bufnr
end

-- Move disassembly window's cursor to "line"
function M.move_cursor(winnr, line)
  local line = line or 1
  a.nvim_win_call(winnr, function()
    vim.fn.setcursorcharpos(line, 1)
    vim.cmd("normal zz") -- center screen around cursor
  end)
end

return M
