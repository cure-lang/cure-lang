import * as path from 'node:path';
import * as os from 'node:os';
import * as fs from 'node:fs/promises';
import { runTests } from '@vscode/test-electron';

async function main(): Promise<void> {
    const extensionDevelopmentPath = path.resolve(__dirname, '../..');
    const workspace = await fs.mkdtemp(path.join(os.tmpdir(), 'cure-host-'));
    const repo = path.resolve(extensionDevelopmentPath, '..');
    await fs.mkdir(path.join(workspace, '.vscode'));
    await fs.writeFile(path.join(workspace, '.vscode', 'settings.json'), JSON.stringify({
        'cure.mcp.enabled': false,
        'cure.lsp.path': process.env.CURE_TEST_LSP ?? path.join(repo, 'cure-lsp'),
        'security.workspace.trust.enabled': false
    }));
    try {
        await runTests({
            version: process.env.VSCODE_TEST_VERSION ?? '1.95.3',
            extensionDevelopmentPath,
            extensionTestsPath: path.resolve(__dirname, 'hostSuite'),
            extensionTestsEnv: { CURE_HOST_WORKSPACE: workspace, CURE_HOME: repo },
            launchArgs: [workspace, '--disable-extensions', '--disable-workspace-trust',
                '--no-sandbox', '--disable-gpu', '--skip-welcome', '--skip-release-notes']
        });
    } finally {
        await fs.rm(workspace, { recursive: true, force: true });
    }
}
void main().catch(error => { console.error(error); process.exitCode = 1; });
