import * as vscode from 'vscode';
import {
    LanguageClient,
    LanguageClientOptions,
    ServerOptions,
    Executable
} from 'vscode-languageclient/node';
import { CureMcpClient } from './mcpClient';
import { reportMissing, resolveExecutable } from './executables';

let client: LanguageClient | undefined;
let mcpClient: CureMcpClient | undefined;

export function activate(context: vscode.ExtensionContext) {
    console.log('Activating vscode-cure extension...');

    // 1. Setup LSP Client
    startLspClient();

    // 2. Setup MCP Client
    mcpClient = new CureMcpClient();
    context.subscriptions.push(mcpClient);

    const mcpConfig = vscode.workspace.getConfiguration('cure').get<boolean>('mcp.enabled', true);
    if (mcpConfig) {
        mcpClient.start();
    }

    // 3. Register Commands
    context.subscriptions.push(
        vscode.commands.registerCommand('cure.restartLsp', async () => {
            await restartLspClient();
            if (client) {
                vscode.window.showInformationMessage('Cure LSP server restarted.');
            }
        }),

        vscode.commands.registerCommand('cure.openRepl', () => {
            const setting = vscode.workspace.getConfiguration('cure').get<string>('mcp.path', 'cure');
            const cure = resolveExecutable(setting, 'cure');
            if (!cure) {
                reportMissing('cure', 'cure.mcp.path');
                return;
            }
            const terminal = vscode.window.createTerminal('Cure REPL', cure, ['repl']);
            terminal.show();
        }),

        vscode.commands.registerCommand('cure.mcp.getDocs', (moduleName?: string) => {
            mcpClient?.showStdlibDocs(moduleName);
        }),

        vscode.commands.registerCommand('cure.mcp.getHelp', (topic?: string) => {
            mcpClient?.showSyntaxHelp(topic);
        }),

        vscode.commands.registerCommand('cure.mcp.typeCheck', () => {
            mcpClient?.typeCheckCurrentDocument();
        }),

        vscode.commands.registerCommand('cure.mcp.parse', () => {
            mcpClient?.parseCurrentDocument();
        }),

        vscode.workspace.onDidChangeConfiguration(event => {
            if (event.affectsConfiguration('cure.lsp.path')) {
                restartLspClient();
            }
        })
    );
}

function startLspClient() {
    const setting = vscode.workspace.getConfiguration('cure').get<string>('lsp.path', 'cure-lsp');
    const command = resolveExecutable(setting, 'cure-lsp');
    if (!command) {
        reportMissing('cure-lsp', 'cure.lsp.path');
        return;
    }

    const cwd = vscode.workspace.workspaceFolders?.[0]?.uri.fsPath;
    const serverExecutable: Executable = {
        command,
        args: [],
        options: { cwd }
    };

    const serverOptions: ServerOptions = {
        run: serverExecutable,
        debug: serverExecutable
    };

    const clientOptions: LanguageClientOptions = {
        documentSelector: [{ scheme: 'file', language: 'cure' }],
        synchronize: {
            fileEvents: vscode.workspace.createFileSystemWatcher('**/*.cure')
        }
    };

    // The id `cure` makes the client read `cure.trace.server`.
    client = new LanguageClient(
        'cure',
        'Cure Language Server',
        serverOptions,
        clientOptions
    );

    client.start();
}

async function restartLspClient() {
    if (client) {
        const old = client;
        client = undefined;
        await old.stop().catch(() => undefined);
    }
    startLspClient();
}

export function deactivate(): Thenable<void> | undefined {
    if (mcpClient) {
        mcpClient.stop();
    }
    if (!client) {
        return undefined;
    }
    return client.stop();
}
