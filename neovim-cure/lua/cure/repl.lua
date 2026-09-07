local M = {}

--- Find the appropriate Cure REPL command.
---@return string[]
function M.get_repl_cmd()
  if vim.fn.executable("cure") == 1 then
    return { "cure", "repl" }
  end

  local cwd = vim.fn.getcwd()
  local local_cure = cwd .. "/cure"
  if vim.fn.executable(local_cure) == 1 then
    return { local_cure, "repl" }
  end

  if vim.fn.executable("mix") == 1 then
    return { "mix", "cure.repl" }
  end

  return { "cure", "repl" }
end

--- Open Cure interactive REPL in a split terminal window
---@param opts table|nil
function M.open(opts)
  opts = opts or {}
  local cmd = M.get_repl_cmd()

  -- Split direction
  local split_cmd = opts.split or "botright 12split"
  vim.cmd(split_cmd)

  local buf = vim.api.nvim_create_buf(false, true)
  vim.api.nvim_win_set_buf(0, buf)

  vim.fn.termopen(cmd)
  vim.cmd("startinsert")
end

return M
