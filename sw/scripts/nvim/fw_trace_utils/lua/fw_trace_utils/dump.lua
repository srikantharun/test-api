local a = vim.api
local M = {}

-- Open dump buffer and sets some sensible options
-- returns the corresponding buffer number
function M.open(winnr, file_path, function_calls)
  local bufnr = nil
  a.nvim_win_call(winnr, function()
    vim.cmd("view " .. file_path)
    bufnr = a.nvim_get_current_buf()
    -- add virtual text, folds, etc
    a.nvim_set_option_value("foldenable", false, {})
    a.nvim_set_option_value("foldmethod", "manual", {})
    vim.cmd("normal zE") -- removes all preexisting folds
    M.set_decorations(bufnr, function_calls)
    a.nvim_set_option_value("foldenable", true, {})
    a.nvim_set_option_value("foldcolumn", "auto:9", {}) -- fold column on the left side
    vim.cmd("normal zR") -- open all folds
  end)
  return bufnr
end

-- Set virtual text and folds based on function call list
function M.set_decorations(bufnr, function_calls)
  local namespace = a.nvim_create_namespace("fw_trace_utils")
  for fname, calls in pairs(function_calls) do
    for _, call in pairs(calls) do
      -- virtual text (lines are 0-indexed)
      a.nvim_buf_set_extmark(bufnr, namespace, call.start_line, 0, {
        virt_text = { { fname, "Function" } },
      })

      a.nvim_buf_set_extmark(bufnr, namespace, call.end_line, 0, {
        virt_text = { { fname .. " took " .. call.time, "Keyword" } },
      })
      -- folds (lines are 1-indexed)
      if (call.start_line + 2) < call.end_line then
        vim.cmd(call.start_line + 2 .. "," .. call.end_line .. "fold")
      end
    end
  end
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
