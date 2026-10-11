# neovim-cure 🚀

Comprehensive, modern Neovim plugin for the [Cure programming language](https://github.com/cure-lang/cure-lang).

Features first-class support for **Cure 0.34+**, including **LSP** (Language Server Protocol) and **MCP** (Model Context Protocol) integration.

---

## ⚡ Features

- 🌳 **Tree-sitter Highlighting**: Uses the grammar in [`tree-sitter-cure/`](../tree-sitter-cure) and the same highlight queries as the Zed extension. The parser is compiled from the repository on first use (needs a C compiler); without one the plugin falls back to the Vim syntax file.
- 🎨 **Vim Syntax Fallback**: Regex highlighting for Cure keywords (`mod`, `fn`, `type`, `rec`, `actor`, `sup`, `app`, `fsm`, dependent types, quantitative modes, Melquiades operator `<-|`/`✉`, string interpolation, and comments).
- 📐 **Indentation & Filetype Detection**: Smart indentation rules for Cure's layout-sensitive structure.
- ⚡ **LSP Integration**: Automatic integration with `cure-lsp` (diagnostics, auto-completion, hover signatures, formatting, semantic tokens, inlay hints, definition lookup).
- 🤖 **Model Context Protocol (MCP)**: Native stdio JSON-RPC client connecting Neovim to Cure's MCP server:
  - `:CureMcpDocs [module]` — Floating documentation window for standard library modules (`Std.List`, `Std.Math`, `Std.Otp`, etc.).
  - `:CureMcpHelp [topic]` — Syntax guide floating windows (`functions`, `types`, `fsm`, `interfaces`, `records`, `pattern_matching`).
  - `:CureMcpCheck` — Fast dependent type check of the active buffer via MCP.
  - `:CureMcpParse` — Interactive MetaAST structure preview.
  - Exported configs for Neovim AI tools (CodeCompanion, Avante).
- 💻 **Interactive REPL**: Launch `cure repl` directly in an integrated Neovim split terminal (`:CureRepl`).

---

## 📦 Installation

The plugin lives in the `neovim-cure/` directory of the Cure repository, next
to the tree-sitter grammar it builds. Install the repository and put that
directory on the runtimepath.

### Using [lazy.nvim](https://github.com/folke/lazy.nvim)

```lua
{
  "cure-lang/cure-lang",
  name = "cure",
  lazy = false,
  config = function(plugin)
    vim.opt.rtp:append(plugin.dir .. "/neovim-cure")
    require("cure").setup({
      lsp = {
        enabled = true,
        auto_attach = true,
      },
      mcp = {
        enabled = true,
        auto_start = true,
      },
      keymaps = {
        enabled = true,
        prefix = "<leader>c",
      },
    })
  end,
}
```

For a local checkout, replace the first line with
`dir = "/path/to/cure-lang"`.

### Using [vim-plug](https://github.com/junegunn/vim-plug)

```vim
Plug 'cure-lang/cure-lang', { 'rtp': 'neovim-cure' }
```

and call `require('cure').setup()` from your config.

---

## 🌳 Tree-sitter

Highlighting uses tree-sitter on Neovim 0.11+; older versions keep the Vim
syntax file. The first time a `.cure` file is opened, the plugin compiles
`tree-sitter-cure/src/parser.c` with `$CC` (or `cc`, `gcc`, `clang`) into
`neovim-cure/parser/cure.so`, and recompiles it when the grammar changes.
Run `:CureTSBuild` to build it by hand. A rebuilt parser takes effect after
restarting Neovim.

```lua
require("cure").setup({
  treesitter = {
    enabled = true,       -- false keeps the Vim syntax file
    auto_install = true,  -- false: only build with :CureTSBuild
  },
})
```

Highlighting works without calling `setup()`. nvim-treesitter is not needed.

---

## ⚡ LSP

The plugin starts `cure-lsp` itself with `vim.lsp.start`, one client per
project (the nearest directory with a `Cure.toml`, `mix.exs` or `.git`). It
looks for `cure-lsp` on `PATH`, then in the current directory; set `lsp.cmd`
to point elsewhere. Don't also configure `cure` through nvim-lspconfig, or
each buffer gets two clients.

```lua
require("cure").setup({
  lsp = {
    cmd = { "/path/to/cure-lang/cure-lsp" },
    capabilities = require("cmp_nvim_lsp").default_capabilities(), -- optional
    on_attach = function(client, bufnr) end,                     -- optional
  },
})
```

---

## 🛠️ Commands & Keymaps

| Command | Keymap | Description |
|---|---|---|
| `:CureFmt` | `<leader>cf` | Format current buffer using `cure-lsp` |
| `:CureRepl` | `<leader>cr` | Launch Cure interactive REPL in split terminal |
| `:CureMcpDocs [mod]` | `<leader>cd` | Open floating window with Stdlib module docs |
| `:CureMcpHelp [topic]` | `<leader>ch` | Open floating window with syntax topic help |
| `:CureMcpCheck` | `<leader>cc` | Type-check active buffer using Cure MCP |
| `:CureMcpParse` | `<leader>cp` | Inspect MetaAST summary of current buffer |
| `:CureCompile` | — | Compile active file using `cure compile` |
| `:CureTSBuild` | — | Build the tree-sitter parser from `tree-sitter-cure/` |

---

## 🧠 AI / LLM Tool Integration (MCP)

Cure exposes an MCP server over stdio via `cure mcp`. You can pass Cure's MCP server configuration directly to Neovim AI clients like **CodeCompanion**:

```lua
local cure_mcp = require("cure.mcp").get_codecompanion_tool_config()

require("codecompanion").setup({
  -- Use cure_mcp in tools configuration
})
```

---

## 📄 License

Apache-2.0 / MIT.
