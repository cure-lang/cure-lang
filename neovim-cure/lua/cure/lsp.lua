local M = {}

--- Find the appropriate Cure LSP executable command.
---@param custom_cmd string[]|nil
---@return string[]
function M.get_lsp_cmd(custom_cmd)
  if custom_cmd and #custom_cmd > 0 then
    return custom_cmd
  end

  -- Check if cure-lsp is in PATH
  if vim.fn.executable("cure-lsp") == 1 then
    return { "cure-lsp" }
  end

  -- Check if ./cure-lsp exists in root directory
  local cwd = vim.fn.getcwd()
  local local_lsp = cwd .. "/cure-lsp"
  if vim.fn.executable(local_lsp) == 1 then
    return { local_lsp }
  end

  -- Fallback to mix task if mix is available
  if vim.fn.executable("mix") == 1 then
    return { "mix", "cure.lsp" }
  end

  return { "cure-lsp" }
end

local root_markers = { "Cure.toml", "mix.exs", ".git" }

--- Project root for `bufnr`: the nearest directory with a Cure.toml, mix.exs
--- or .git, so every file of a project shares one server.
---@param bufnr integer
---@return string
function M.root_dir(bufnr)
  local fname = vim.api.nvim_buf_get_name(bufnr)
  local found = vim.fs.find(root_markers, { path = vim.fs.dirname(fname), upward = true })[1]
  if found then
    return vim.fs.dirname(found)
  end
  return vim.fs.dirname(fname) or vim.fn.getcwd()
end

--- Start or attach LSP to a buffer. `vim.lsp.start` reuses the running client
--- with the same name and root, so this is safe to call for every buffer.
---@param bufnr integer
---@param config table
function M.attach(bufnr, config)
  bufnr = bufnr or vim.api.nvim_get_current_buf()

  -- Use Neovim 0.8+ vim.lsp.start API
  if vim.lsp and vim.lsp.start then
    vim.lsp.start({
      name = "cure-lsp",
      cmd = M.get_lsp_cmd(config.cmd),
      root_dir = M.root_dir(bufnr),
      settings = config.settings or {},
      capabilities = config.capabilities,
      on_attach = config.on_attach,
    }, {
      bufnr = bufnr,
    })
  end
end

return M
