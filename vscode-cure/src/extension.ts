import * as vscode from 'vscode';
import * as path from 'path';
import {
    LanguageClient,
    LanguageClientOptions,
    ServerOptions,
    Executable
} from 'vscode-languageclient/node';
import { CureMcpClient } from './mcpClient';

let client: LanguageClient | undefined;
let mcpClient: CureMcpClient | undefined;

export function activate(context: vscode.ExtensionContext) {
    console.log('Activating vscode-cure extension...');

    // 1. Setup LSP Client
    setupLspClient(context);

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
            if (client) {
                await client.stop();
                await client.start();
                vscode.window.showInformationMessage('Cure LSP server restarted.');
            }
        }),

        vscode.commands.registerCommand('cure.openRepl', () => {
            const terminal = vscode.window.createTerminal('Cure REPL', 'cure', ['repl']);
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
        })
    );
}

function setupLspClient(context: vscode.ExtensionContext) {
    const config = vscode.workspace.getConfiguration('cure');
    const customLspPath = config.get<string>('lsp.path', 'cure-lsp');

    const workspaceFolders = vscode.workspace.workspaceFolders;
    const cwd = workspaceFolders && workspaceFolders.length > 0 ? workspaceFolders[0].uri.fsPath : process.cwd();

    let command = customLspPath;
    let args: string[] = [];

    // Fallback checks for local executable binary
    if (command === 'cure-lsp') {
        const localLsp = path.join(cwd, 'cure-lsp');
        command = localLsp;
    }

    const serverExecutable: Executable = {
        command,
        args,
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

    client = new LanguageClient(
        'cureLanguageServer',
        'Cure Language Server',
        serverOptions,
        clientOptions
    );

    client.start();
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
