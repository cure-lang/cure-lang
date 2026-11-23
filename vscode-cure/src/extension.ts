import * as vscode from 'vscode';
import {
    LanguageClient,
    LanguageClientOptions,
    ServerOptions,
    Executable,
    State
} from 'vscode-languageclient/node';
import { CureMcpClient } from './mcpClient';
import { reportMissing, resolveExecutable } from './executables';
import { GoalProvider } from './goalView';
import { GoalRequests } from './goalRequests';

let client: LanguageClient | undefined;
let mcpClient: CureMcpClient | undefined;
let provider: GoalProvider | undefined;
let view: vscode.TreeView<unknown> | undefined;
let requests: GoalRequests | undefined;
let lifecycle: Promise<void> = Promise.resolve();
let disposed = false;
let restartGeneration = 0;

export async function activate(context: vscode.ExtensionContext) {
    console.log('Activating vscode-cure extension...');

    disposed = false;
    provider = new GoalProvider();
    requests = new GoalRequests(state => provider?.update(state));
    view = vscode.window.createTreeView('cure.goals', { treeDataProvider: provider });
    context.subscriptions.push(provider, view, requests);
    const refresh = () => refreshGoals();
    context.subscriptions.push(
        vscode.window.onDidChangeActiveTextEditor(refresh),
        vscode.window.onDidChangeTextEditorSelection(event => {
            if (event.textEditor === vscode.window.activeTextEditor) { refresh(); }
        }),
        vscode.workspace.onDidChangeTextDocument(event => {
            if (event.document === vscode.window.activeTextEditor?.document) { refresh(); }
        }),
        vscode.workspace.onDidSaveTextDocument(document => {
            if (document.languageId === 'cure') { refresh(); }
        }),
        vscode.workspace.onDidCloseTextDocument(document => {
            if (requests && document.uri.toString() === provider?.observe().query?.uri) { requests.clear(); }
        }),
        { dispose: () => { disposed = true; requests?.dispose(); } }
    );

    // 2. Setup MCP Client
    mcpClient = new CureMcpClient();
    context.subscriptions.push(mcpClient);

    const mcpConfig = vscode.workspace.getConfiguration('cure').get<boolean>('mcp.enabled', true);
    if (mcpConfig) {
        mcpClient.start();
    }

    // 3. Register Commands
    context.subscriptions.push(
        vscode.commands.registerCommand('cure.showGoals', async () => {
            await vscode.commands.executeCommand('cure.goals.focus');
            refreshGoals();
        }),
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
                void restartLspClient();
            }
        })
    );
    await restartLspClient();
    return Object.freeze({
        observeGoals: () => provider?.observe(),
        isGoalViewVisible: () => view?.visible === true
    });
}

function refreshGoals(): void {
    const editor = vscode.window.activeTextEditor;
    if (!editor || editor.document.languageId !== 'cure' || editor.document.isClosed ||
        editor.document.uri.scheme !== 'file') {
        requests?.select();
        return;
    }
    const position = editor.selection.active;
    requests?.select({
        uri: editor.document.uri.toString(), version: editor.document.version,
        line: position.line, character: position.character
    });
}

async function startLspClient(generation: number): Promise<void> {
    if (disposed) { return; }
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
    };

    // The id `cure` makes the client read `cure.trace.server`.
    client = new LanguageClient(
        'cure',
        'Cure Language Server',
        serverOptions,
        clientOptions
    );

    const started = client;
    const stateListener = started.onDidChangeState(event => {
        if (client === started && event.newState === State.Stopped) {
            requests?.setTransport();
        }
        if (event.newState === State.Stopped) { stateListener.dispose(); }
    });
    try {
        await started.start();
        if (disposed || generation !== restartGeneration) { await started.stop(); return; }
        requests?.setTransport({
            request(query) {
                const cancellation = new vscode.CancellationTokenSource();
                // LanguageClient 9 flushes pending didChange notifications itself.
                const promise = started.sendRequest('cure/proofState', {
                    textDocument: { uri: query.uri }, version: query.version,
                    position: { line: query.line, character: query.character }
                }, cancellation.token);
                void promise.finally(() => cancellation.dispose()).catch(() => undefined);
                return { promise, cancel: () => cancellation.cancel() };
            }
        });
        refreshGoals();
    } catch (error) {
        requests?.setTransport();
        console.error('Cure language server failed to start', error);
        await started.dispose();
        if (client === started) { client = undefined; }
    }
}

function restartLspClient(): Promise<void> {
    const generation = ++restartGeneration;
    requests?.setTransport();
    lifecycle = lifecycle.catch(() => undefined).then(async () => {
        if (client) {
            const old = client;
            client = undefined;
            await old.dispose();
        }
        if (generation === restartGeneration) { await startLspClient(generation); }
    });
    return lifecycle;
}

export async function deactivate(): Promise<void> {
    disposed = true;
    requests?.dispose();
    if (mcpClient) {
        mcpClient.stop();
    }
    await lifecycle.catch(() => undefined);
    const old = client;
    client = undefined;
    await old?.dispose();
}
