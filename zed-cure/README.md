# zed-cure 🚀

Official [Zed](https://zed.dev) editor extension for the [Cure programming language](https://github.com/cure-lang/cure).

Provides high-performance language support, tree-sitter syntax queries, `cure-lsp` diagnostics, and Model Context Protocol (MCP) context server integration for Cure **0.34+**.

---

## ✨ Features

- 🎨 **Tree-sitter Syntax Highlighting**: Clean highlighting for Cure modules, dependent types, quantitative annotations (`erased`, `linear`, `affine`), OTP containers (`actor`, `sup`, `app`, `fsm`), Melquiades operator (`<-|`/`✉`), strings, atoms, and comments.
- ⚡ **Language Server Protocol (LSP)**: Automatic discovery and connection to `cure-lsp` over stdio (diagnostics, auto-completion, hover signatures, formatting, symbol outline).
- 🤖 **Model Context Protocol (MCP)**: Native integration with Zed's Assistant via `cure-mcp`. Registers Cure MCP context server (`cure mcp`) for AI capabilities directly in Zed!
- 📐 **Indentation & Bracket Matching**: Smart indentation rules and auto-closing bracket pairs for `.cure` files.
- 🌳 **Code Outline**: Symbol tree outline support for Cure modules, functions, records, sum types, actors, and FSMs.

---

## 🛠️ Development & Local Installation in Zed

1. Clone or navigate to the extension directory:
   ```bash
   cd zed-cure
   ```

2. Install as a dev extension in Zed:
   - Open Zed (`zed .`)
   - Open the command palette (`Ctrl+Shift+P` / `Cmd+Shift+P`)
   - Select `zed: install dev extension`
   - Select the `zed-cure` directory.

---

## 📄 License

Apache-2.0 / MIT.
