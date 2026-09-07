# VS Code Extension for Cure 🚀

Official Visual Studio Code extension for the [Cure programming language](https://github.com/cure-lang/cure).

Provides language support, LSP diagnostics, MCP AI integration, and REPL support for Cure **0.34+**.

---

## ✨ Features

- 🎨 **Syntax Highlighting**: Complete TextMate grammar covering Cure's module syntax, dependent types, quantitative annotations (`erased`, `linear`, `affine`), OTP constructs (`actor`, `sup`, `app`, `fsm`), Melquiades operator (`<-|`/`✉`), string interpolation, atoms, numbers, and comments.
- ⚡ **Language Server Protocol (LSP)**: Automatic connection to `cure-lsp` over stdio:
  - Real-time compile diagnostics
  - Signature help & hover tooltips
  - Code completion
  - Auto-formatting on save
- 🤖 **Model Context Protocol (MCP)**: Deep MCP stdio integration:
  - **Cure MCP: View Stdlib Documentation** (`cure.mcp.getDocs`) — View rich documentation for `Std.List`, `Std.Math`, `Std.Otp`, etc.
  - **Cure MCP: View Syntax Help Topic** (`cure.mcp.getHelp`) — View topic guides (`functions`, `types`, `fsm`, `records`).
  - **Cure MCP: Type-Check Current Document** (`cure.mcp.typeCheck`) — Perform fast dependent type check via MCP.
  - **Cure MCP: View MetaAST Summary** (`cure.mcp.parse`) — Preview full AST structure.
- 💻 **Interactive REPL**: Launch `cure repl` in a VS Code integrated terminal (`Cure: Open Interactive REPL`).
- 💡 **Snippets**: Handy code snippets for modules, functions, sum types, records, actors, and FSMs.

---

## 🛠️ Commands

| Command | Title | Description |
|---|---|---|
| `cure.restartLsp` | Cure: Restart LSP Server | Restarts the background `cure-lsp` server |
| `cure.openRepl` | Cure: Open Interactive REPL | Launches `cure repl` in an integrated terminal |
| `cure.mcp.getDocs` | Cure MCP: View Stdlib Documentation | Opens webview preview of stdlib module docs |
| `cure.mcp.getHelp` | Cure MCP: View Syntax Help Topic | Opens webview preview of syntax help topics |
| `cure.mcp.typeCheck` | Cure MCP: Type-Check Current Document | Type-checks active document via MCP |
| `cure.mcp.parse` | Cure MCP: View MetaAST Summary | Shows AST summary via MCP |

---

## ⚙️ Configuration Settings

- `cure.lsp.path`: Custom path to `cure-lsp` binary (default: `cure-lsp`).
- `cure.mcp.path`: Custom path to `cure` binary for MCP (default: `cure`).
- `cure.mcp.enabled`: Enable/disable MCP background client (default: `true`).
- `cure.trace.server`: Traces communication between VS Code and LSP server (`off`, `messages`, `verbose`).

---

## 📦 Building & Testing

```bash
cd vscode-cure
npm install
npm run compile
```

To build a `.vsix` package:
```bash
npx vsce package
```
