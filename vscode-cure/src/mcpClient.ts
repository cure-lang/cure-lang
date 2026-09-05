import * as vscode from 'vscode';
import { spawn, ChildProcess } from 'child_process';
import * as path from 'path';

export class CureMcpClient implements vscode.Disposable {
    private process: ChildProcess | null = null;
    private requestId = 0;
    private pendingRequests = new Map<number, (res: any) => void>();
    private buffer = '';
    private outputChannel: vscode.OutputChannel;

    constructor() {
        this.outputChannel = vscode.window.createOutputChannel('Cure MCP Server');
    }

    public start(): boolean {
        if (this.process) {
            return true;
        }

        const config = vscode.workspace.getConfiguration('cure');
        const customPath = config.get<string>('mcp.path', 'cure');
        const workspaceFolders = vscode.workspace.workspaceFolders;
        const cwd = workspaceFolders && workspaceFolders.length > 0 ? workspaceFolders[0].uri.fsPath : process.cwd();

        let executable = customPath;
        let args: string[] = ['mcp'];

        // Fallback checks
        if (executable === 'cure' && !this.isExecutableInPath(executable)) {
            const localCure = path.join(cwd, 'cure');
            executable = localCure;
        }

        try {
            this.process = spawn(executable, args, { cwd, env: process.env });

            this.process.stdout?.on('data', (chunk: Buffer) => {
                this.buffer += chunk.toString('utf8');
                const lines = this.buffer.split('\n');
                this.buffer = lines.pop() || '';

                for (const line of lines) {
                    if (!line.trim()) continue;
                    try {
                        const message = JSON.parse(line);
                        if (message.id !== undefined && this.pendingRequests.has(message.id)) {
                            const callback = this.pendingRequests.get(message.id)!;
                            this.pendingRequests.delete(message.id);
                            callback(message);
                        }
                    } catch (err) {
                        this.outputChannel.appendLine(`[Parse Error]: ${err} on line: ${line}`);
                    }
                }
            });

            this.process.stderr?.on('data', (data: Buffer) => {
                this.outputChannel.appendLine(`[MCP stderr]: ${data.toString('utf8')}`);
            });

            this.process.on('exit', (code) => {
                this.outputChannel.appendLine(`[MCP Process exited with code ${code}]`);
                this.process = null;
            });

            // Initialize request
            this.sendRequest('initialize', {});
            return true;
        } catch (err) {
            vscode.window.showErrorMessage(`Failed to launch Cure MCP Server: ${err}`);
            return false;
        }
    }

    public stop() {
        if (this.process) {
            this.process.kill();
            this.process = null;
        }
    }

    public sendRequest(method: string, params: any): Promise<any> {
        return new Promise((resolve, reject) => {
            if (!this.process && !this.start()) {
                reject(new Error('MCP process not running'));
                return;
            }

            this.requestId++;
            const id = this.requestId;
            this.pendingRequests.set(id, (response) => {
                if (response.error) {
                    reject(new Error(response.error.message || 'MCP Error'));
                } else {
                    resolve(response.result);
                }
            });

            const payload = JSON.stringify({
                jsonrpc: '2.0',
                id,
                method,
                params
            }) + '\n';

            this.process?.stdin?.write(payload);
        });
    }

    public async callTool(name: string, args: any): Promise<string> {
        const result = await this.sendRequest('tools/call', {
            name,
            arguments: args
        });

        if (result.isError) {
            const errText = (result.content || []).map((c: any) => c.text || '').join('');
            throw new Error(errText || 'Tool execution error');
        }

        return (result.content || []).map((c: any) => c.text || '').join('');
    }

    public async showStdlibDocs(moduleName?: string) {
        if (!moduleName) {
            moduleName = await vscode.window.showInputBox({
                prompt: 'Enter Cure Stdlib Module (e.g. Std.List, Std.Math, Std.Otp)',
                value: 'Std.List'
            });
        }
        if (!moduleName) return;

        try {
            const docs = await this.callTool('get_stdlib_docs', { module: moduleName });
            this.showMarkdownPreview(`Cure Docs: ${moduleName}`, docs);
        } catch (err: any) {
            vscode.window.showErrorMessage(`Cure MCP Error: ${err.message}`);
        }
    }

    public async showSyntaxHelp(topic?: string) {
        if (!topic) {
            const topics = ['functions', 'types', 'fsm', 'interfaces', 'pattern_matching', 'records', 'modules'];
            topic = await vscode.window.showQuickPick(topics, {
                placeHolder: 'Select Cure Syntax Topic'
            });
        }
        if (!topic) return;

        try {
            const help = await this.callTool('get_syntax_help', { topic });
            this.showMarkdownPreview(`Cure Help: ${topic}`, help);
        } catch (err: any) {
            vscode.window.showErrorMessage(`Cure MCP Error: ${err.message}`);
        }
    }

    public async typeCheckCurrentDocument() {
        const editor = vscode.window.activeTextEditor;
        if (!editor) {
            vscode.window.showInformationMessage('No active editor for Cure type check.');
            return;
        }

        const source = editor.document.getText();
        try {
            vscode.window.showInformationMessage('Type checking via Cure MCP...');
            const result = await this.callTool('type_check_cure', { source });
            this.showOutputWindow('Cure Type Check', result);
        } catch (err: any) {
            this.showOutputWindow('Cure Type Check Errors', err.message);
        }
    }

    public async parseCurrentDocument() {
        const editor = vscode.window.activeTextEditor;
        if (!editor) {
            vscode.window.showInformationMessage('No active editor for Cure AST preview.');
            return;
        }

        const source = editor.document.getText();
        try {
            const astSummary = await this.callTool('parse_cure', { source });
            this.showOutputWindow('Cure MetaAST Summary', astSummary);
        } catch (err: any) {
            vscode.window.showErrorMessage(`Cure Parse Error: ${err.message}`);
        }
    }

    private showMarkdownPreview(title: string, markdownContent: string) {
        const panel = vscode.window.createWebviewPanel(
            'cureMcpView',
            title,
            vscode.ViewColumn.Beside,
            { enableScripts: true }
        );

        panel.webview.html = `
            <!DOCTYPE html>
            <html lang="en">
            <head>
                <meta charset="UTF-8">
                <style>
                    body { font-family: var(--vscode-editor-font-family); padding: 20px; line-height: 1.6; color: var(--vscode-editor-foreground); background-color: var(--vscode-editor-background); }
                    pre { background-color: var(--vscode-textCodeBlock-background); padding: 10px; border-radius: 4px; overflow-x: auto; }
                    code { font-family: monospace; }
                </style>
            </head>
            <body>
                <div id="content">
                    <pre>${this.escapeHtml(markdownContent)}</pre>
                </div>
            </body>
            </html>
        `;
    }

    private showOutputWindow(title: string, content: string) {
        this.outputChannel.clear();
        this.outputChannel.appendLine(`=== ${title} ===\n`);
        this.outputChannel.appendLine(content);
        this.outputChannel.show(true);
    }

    private escapeHtml(text: string): string {
        return text.replace(/&/g, '&amp;').replace(/</g, '&lt;').replace(/>/g, '&gt;');
    }

    private isExecutableInPath(exec: string): boolean {
        // Simplified check
        return true;
    }

    public dispose() {
        this.stop();
        this.outputChannel.dispose();
    }
}
