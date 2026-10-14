import * as vscode from 'vscode';
import * as fs from 'fs';
import * as os from 'os';
import * as path from 'path';

function isExecutable(file: string): boolean {
    try {
        fs.accessSync(file, fs.constants.X_OK);
        return fs.statSync(file).isFile();
    } catch {
        return false;
    }
}

function searchPath(name: string): string | undefined {
    const extensions = process.platform === 'win32'
        ? ['', ...(process.env.PATHEXT || '.EXE;.CMD;.BAT').split(';')]
        : [''];
    for (const dir of (process.env.PATH || '').split(path.delimiter)) {
        if (!dir) continue;
        for (const ext of extensions) {
            const candidate = path.join(dir, name + ext);
            if (isExecutable(candidate)) return candidate;
        }
    }
    return undefined;
}

function expand(setting: string): string {
    const folder = vscode.workspace.workspaceFolders?.[0]?.uri.fsPath ?? '';
    return setting
        .replace(/^~(?=$|[\\/])/, os.homedir())
        .replace(/\$\{workspaceFolder\}/g, folder);
}

/**
 * Resolves the executable for a `cure.*.path` setting. A value other than the
 * default is used as given (after expanding `~` and `${workspaceFolder}`); the
 * default name is looked up on PATH, then at the root of each workspace folder
 * (a checkout of the Cure repository has `cure` and `cure-lsp` there).
 */
export function resolveExecutable(setting: string, defaultName: string): string | undefined {
    const value = expand(setting.trim() || defaultName);
    if (value !== defaultName) {
        if (!value.includes('/') && !value.includes('\\')) return searchPath(value) ?? value;
        return value;
    }

    const onPath = searchPath(defaultName);
    if (onPath) return onPath;

    for (const folder of vscode.workspace.workspaceFolders ?? []) {
        const local = path.join(folder.uri.fsPath, defaultName);
        if (isExecutable(local)) return local;
    }
    return undefined;
}

/** Tells the user that `name` was not found, with a shortcut to `settingKey`. */
export async function reportMissing(name: string, settingKey: string): Promise<void> {
    const action = await vscode.window.showErrorMessage(
        `Cure: could not find \`${name}\`. Put it on PATH or set \`${settingKey}\` to its full path.`,
        'Open Settings'
    );
    if (action) {
        await vscode.commands.executeCommand('workbench.action.openSettings', settingKey);
    }
}
