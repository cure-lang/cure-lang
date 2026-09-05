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

--- Start or attach LSP to a buffer
---@param bufnr integer
---@param config table
function M.attach(bufnr, config)
  bufnr = bufnr or vim.api.nvim_get_current_buf()

  local cmd = M.get_lsp_cmd(config.cmd)

  -- Use Neovim 0.8+ vim.lsp.start API
  if vim.lsp and vim.lsp.start then
    vim.lsp.start({
      name = "cure-lsp",
      cmd = cmd,
      root_dir = vim.fs.dirname(vim.api.nvim_buf_get_name(bufnr)) or vim.fn.getcwd(),
      filetypes = { "cure" },
      settings = config.settings or {},
    }, {
      bufnr = bufnr,
    })
  end
end

--- Register nvim-lspconfig rule if nvim-lspconfig is present
---@param config table
function M.setup_lspconfig(config)
  local status, lspconfig = pcall(require, "lspconfig")
  if not status then
    return
  end

  local configs = require("lspconfig.configs")
  if not configs.cure then
    configs.cure = {
      default_config = {
        cmd = M.get_lsp_cmd(config.cmd),
        filetypes = { "cure" },
        root_dir = function(fname)
          return vim.fs.dirname(fname) or vim.fn.getcwd()
        end,
        settings = config.settings or {},
      },
    }
  end

  if config.auto_attach ~= false then
    lspconfig.cure.setup({})
  end
end

return M
