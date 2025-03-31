local a = vim.api
local M = {
  loclist = {}
}

-- Init a selected window's loclist
function M.set(winnr, list)
  local loclist = list
  -- sort entries by line
  table.sort(loclist, function(i, j)
    return (i.lnum < j.lnum)
  end)

  vim.fn.setloclist(winnr, loclist)

  -- avoid calling vim.fn.getloclist, which is slow on big files
  M.loclist[winnr] = loclist
end

-- Update a loclist's selected entry based on cursor line
function M.update_selected_entry(winnr, curline)
  local selected_entry = 1
  for i, entry in ipairs(M.loclist[winnr]) do
    if entry.lnum <= curline then
      selected_entry = i
    else
      break
    end
  end
  vim.fn.setloclist(winnr, {}, "a", { idx = selected_entry })
end

-- Open a window's loclist and sets some sensible defaults
function M.open(winnr)
  a.nvim_win_call(winnr, function()
    vim.cmd("lopen")
    a.nvim_win_set_option(winnr, "scrolloff", 0)
  end)
end

-- Close a window's loclist
function M.close(winnr)
  a.nvim_win_call(winnr, function()
    vim.cmd("lclose")
  end)
end

return M
