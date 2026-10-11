local M = {}

local lsp = require("cure.lsp")
local mcp = require("cure.mcp")
local repl = require("cure.repl")
local treesitter = require("cure.treesitter")

local default_config = {
  lsp = {
    enabled = true,
    cmd = nil,
    auto_attach = true,
    settings = {},
    capabilities = nil,
    on_attach = nil,
  },
  treesitter = {
    enabled = true,
    -- Compile tree-sitter-cure/src/parser.c with $CC/cc when the parser is
    -- missing or older than the grammar.
    auto_install = true,
    grammar_dir = nil,
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

local bootstrapped = false

--- Filetype detection, highlight links and global commands. Sourced from
--- `plugin/cure.lua`, and again from `setup()` because plugin managers that
--- add `neovim-cure/` to the runtimepath late (lazy.nvim) never source
--- `plugin/` or `ftdetect/` there.
function M.bootstrap()
  if bootstrapped then
    return
  end
  bootstrapped = true

  vim.filetype.add({ extension = { cure = "cure" } })

  treesitter.set_highlights()
  vim.api.nvim_create_autocmd("ColorScheme", {
    group = vim.api.nvim_create_augroup("cure_highlights", { clear = true }),
    callback = treesitter.set_highlights,
  })

  vim.api.nvim_create_user_command("CureTSBuild", function()
    treesitter.build(M.treesitter_config())
  end, { desc = "Build the Cure tree-sitter parser from tree-sitter-cure/" })
end

--- Main setup entrypoint for cure.nvim
---@param user_opts table|nil
function M.setup(user_opts)
  M.config = vim.tbl_deep_extend("force", default_config, user_opts or {})
  M.bootstrap()

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

--- Tree-sitter options, falling back to the defaults when `setup()` has not
--- been called: highlighting does not need it.
---@return table
function M.treesitter_config()
  return M.config.treesitter or default_config.treesitter
end

--- Buffer-local setup for Cure buffers
---@param bufnr integer
function M.setup_buffer_commands(bufnr)
  bufnr = (bufnr == nil or bufnr == 0) and vim.api.nvim_get_current_buf() or bufnr

  treesitter.attach(bufnr, M.treesitter_config())

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
M.treesitter = treesitter

return M
