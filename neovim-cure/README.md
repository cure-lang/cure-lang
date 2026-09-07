# neovim-cure 🚀

Comprehensive, modern Neovim plugin for the [Cure programming language](https://github.com/cure-lang/cure).

Features first-class support for **Cure 0.34+**, including **LSP** (Language Server Protocol) and **MCP** (Model Context Protocol) integration.

---

## ⚡ Features

- 🎨 **Syntax Highlighting**: Complete grammar highlighting for Cure keywords (`mod`, `fn`, `type`, `rec`, `actor`, `sup`, `app`, `fsm`, dependent types, quantitative modes, Melquiades operator `<-|`/`✉`, string interpolation, and comments).
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

### Using [lazy.nvim](https://github.com/folke/lazy.nvim)

```lua
{
  "cure-lang/neovim-cure",
  -- Or for local development:
  -- dir = "/path/to/cure/neovim-cure",
  ft = "cure",
  dependencies = {
    "neovim/nvim-lspconfig", -- Optional but recommended
  },
  config = function()
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

### Using [packer.nvim](https://github.com/wbthomason/packer.nvim)

```lua
use {
  'cure-lang/neovim-cure',
  ft = {'cure'},
  config = function()
    require('cure').setup()
  end
}
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
