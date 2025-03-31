local a = vim.api
local M = {
  empty_buffer = nil, -- Empty scratch buffer displayed when there is no source
}

local function file_exists(name)
  local f = io.open(name, "r")
  if f then
    io.close(f)
    return true
  else
    return false
  end
end

-- Open a new buffer containing the file to display
-- Returns the buffer number
function M.open(winnr, file_path, file_line)
  local bufnr = nil
  if not file_path or not file_exists(file_path) then
    if not M.empty_buffer then
      M.empty_buffer = a.nvim_create_buf(false, true)
    end
    bufnr = M.empty_buffer
    a.nvim_win_set_buf(winnr, bufnr)
  else
    a.nvim_win_call(winnr, function()
      vim.cmd("view " .. file_path)
      bufnr = a.nvim_get_current_buf()
      -- If precedent source buffer was empty, "edit" opens the new file in it
      if bufnr == M.empty_buffer then
        M.empty_buffer = nil
      end
      a.nvim_exec_autocmds("BufRead", { buffer = bufnr })
    end)
  end
  M.move_cursor(winnr, file_line, 1)
  return bufnr
end

-- Move cursor to a specific position and center the buffer around it
function M.move_cursor(winnr, line, col)
  local line = line or 1
  local col = col or 1

  a.nvim_win_call(winnr, function()
    vim.fn.setcursorcharpos(line, col)
    vim.cmd("normal zz")
  end)
end

return M
