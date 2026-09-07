local M = {}

local lsp = require("cure.lsp")
local mcp = require("cure.mcp")
local repl = require("cure.repl")

local default_config = {
  lsp = {
    enabled = true,
    cmd = nil,
    auto_attach = true,
    settings = {},
  },
  mcp = {
    enabled = true,
    cmd = nil,
    auto_start = true,
  },
  formatting = {
    format_on_save = false,
  },
  keymaps = {
    enabled = true,
    prefix = "<leader>c",
  },
}

M.config = {}

--- Main setup entrypoint for cure.nvim
---@param user_opts table|nil
function M.setup(user_opts)
  M.config = vim.tbl_deep_extend("force", default_config, user_opts or {})

  -- Configure LSP
  if M.config.lsp.enabled then
    lsp.setup_lspconfig(M.config.lsp)
  end

  -- Auto-start MCP server if configured
  if M.config.mcp.enabled and M.config.mcp.auto_start then
    mcp.start_server(M.config.mcp)
  end

  -- Register global user commands
  M.register_user_commands()

  -- Format on save autocommand if enabled
  if M.config.formatting.format_on_save then
    vim.api.nvim_create_autocmd("BufWritePre", {
      pattern = "*.cure",
      callback = function()
        vim.lsp.buf.format({ async = false })
      end,
    })
  end
end

--- Register user commands
function M.register_user_commands()
  vim.api.nvim_create_user_command("CureFmt", function()
    vim.lsp.buf.format({ async = true })
  end, { desc = "Format current Cure buffer using Cure LSP" })

  vim.api.nvim_create_user_command("CureCompile", function()
    local fname = vim.api.nvim_buf_get_name(0)
    if fname == "" then
      vim.notify("Buffer has no filename to compile", vim.log.levels.WARN)
      return
    end
    vim.cmd("make " .. vim.fn.shellescape(fname))
  end, { desc = "Compile current Cure buffer" })

  vim.api.nvim_create_user_command("CureRepl", function()
    repl.open()
  end, { desc = "Open Cure interactive REPL in split terminal" })

  vim.api.nvim_create_user_command("CureMcpDocs", function(opts)
    mcp.get_docs(opts.args)
  end, { nargs = "?", desc = "Get stdlib documentation via Cure MCP" })

  vim.api.nvim_create_user_command("CureMcpHelp", function(opts)
    mcp.get_help(opts.args)
  end, { nargs = "?", desc = "Get syntax topic help via Cure MCP" })

  vim.api.nvim_create_user_command("CureMcpCheck", function()
    mcp.type_check_buffer()
  end, { desc = "Type-check current buffer via Cure MCP" })

  vim.api.nvim_create_user_command("CureMcpParse", function()
    mcp.parse_buffer()
  end, { desc = "View MetaAST summary via Cure MCP" })
end

--- Buffer-local setup for Cure buffers
---@param bufnr integer
function M.setup_buffer_commands(bufnr)
  bufnr = bufnr or 0

  if M.config.lsp and M.config.lsp.enabled and M.config.lsp.auto_attach ~= false then
    lsp.attach(bufnr, M.config.lsp)
  end

  if M.config.keymaps and M.config.keymaps.enabled then
    local p = M.config.keymaps.prefix or "<leader>c"
    local opts = { noremap = true, silent = true, buffer = bufnr }

    vim.keymap.set("n", p .. "f", "<cmd>CureFmt<cr>", vim.tbl_extend("force", opts, { desc = "Format Cure File" }))
    vim.keymap.set("n", p .. "r", "<cmd>CureRepl<cr>", vim.tbl_extend("force", opts, { desc = "Open Cure REPL" }))
    vim.keymap.set("n", p .. "d", "<cmd>CureMcpDocs<cr>", vim.tbl_extend("force", opts, { desc = "Cure MCP Docs" }))
    vim.keymap.set("n", p .. "h", "<cmd>CureMcpHelp<cr>", vim.tbl_extend("force", opts, { desc = "Cure MCP Help" }))
    vim.keymap.set("n", p .. "c", "<cmd>CureMcpCheck<cr>", vim.tbl_extend("force", opts, { desc = "Cure MCP Check" }))
    vim.keymap.set("n", p .. "p", "<cmd>CureMcpParse<cr>", vim.tbl_extend("force", opts, { desc = "Cure MCP Parse" }))
  end
end

-- Export helper submodules
M.lsp = lsp
M.mcp = mcp
M.repl = repl

return M
