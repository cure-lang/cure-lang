import * as assert from 'node:assert/strict';
import * as path from 'node:path';
import * as fs from 'node:fs/promises';
import * as vscode from 'vscode';
import { GoalState } from '../goalRequests';

interface Observation { observeGoals(): GoalState; isGoalViewVisible(): boolean; }

async function until(check: () => boolean, description: string): Promise<void> {
    const start = Date.now();
    while (!check()) {
        if (Date.now() - start > 30000) { throw new Error(`Timed out: ${description}`); }
        await new Promise(resolve => setTimeout(resolve, 50));
    }
}

const proof = `mod HostProof
  use Std.Equivalent
  fn theorem(x: Int, y: Int, h: Equivalent(Int, x, y)) -> Equivalent(Int, x, y) = proof chain
    x == y
    because
      have marker = "é𐐀"
      rewrite using h
      exact reflexive(y)
end
`;

export async function run(): Promise<void> {
    const workspace = process.env.CURE_HOST_WORKSPACE!;
    const extension = vscode.extensions.getExtension<Observation>('cure-lang.vscode-cure');
    assert.ok(extension, 'manifest extension is installed in development host');
    const api = await extension.activate();
    assert.ok(extension.isActive);
    const views = extension.packageJSON.contributes.views.explorer as { id: string }[];
    assert.ok(views.some(view => view.id === 'cure.goals'));
    await vscode.commands.executeCommand('cure.showGoals');
    await until(() => api.isGoalViewVisible(), 'native Cure Goals view visible');

    async function open(name: string, text: string): Promise<vscode.TextEditor> {
        const filename = path.join(workspace, name);
        await fs.writeFile(filename, text);
        return vscode.window.showTextDocument(await vscode.workspace.openTextDocument(filename), { preview: false });
    }
    async function cursor(editor: vscode.TextEditor, needle: string, end = false): Promise<void> {
        const visible = await vscode.window.showTextDocument(editor.document, { preview: false });
        const offset = editor.document.getText().indexOf(needle);
        assert.notEqual(offset, -1);
        const position = editor.document.positionAt(offset + (end ? needle.length : 0));
        visible.selection = new vscode.Selection(position, position);
        await until(() => {
            const state = api.observeGoals();
            return state.query?.uri === editor.document.uri.toString() &&
                state.query.version === editor.document.version && state.query.line === position.line &&
                state.query.character === position.character && state.kind !== 'loading' &&
                state.kind !== 'unavailable';
        }, `proof state at ${needle}: ${JSON.stringify(api.observeGoals())}`);
    }
    function target(expected: string): void {
        const state = api.observeGoals();
        assert.equal(state.kind, 'goals', JSON.stringify(state));
        assert.equal(state.goals?.[0]?.goal, expected);
    }

    const editor = await open('proof.cure', proof);
    await cursor(editor, 'rewrite using h');
    target('Equivalent(Int, x, y)');
    assert.ok(api.observeGoals().goals?.[0].context.includes('h : Equivalent(Int, x, y)'));
    await cursor(editor, 'have marker = "é𐐀"', true);
    assert.ok(api.observeGoals().goals?.[0].context.includes('marker : String'), 'UTF-16 multibyte cursor');
    await cursor(editor, 'rewrite using h', true);
    target('Equivalent(Int, y, y)');
    await cursor(editor, 'exact reflexive(y)', true);
    assert.equal(api.observeGoals().kind, 'no-state', 'empty response is not completion');
    await cursor(editor, 'mod HostProof');
    assert.equal(api.observeGoals().kind, 'no-state');

    const failed = proof.replace('exact reflexive(y)', 'exact marker');
    await editor.edit(edit => edit.replace(new vscode.Range(editor.document.positionAt(0),
        editor.document.positionAt(editor.document.getText().length)), failed));
    await cursor(editor, 'exact marker');
    target('Equivalent(Int, y, y)');
    await until(() => vscode.languages.getDiagnostics(editor.document.uri).some(d =>
        d.code === 'E110' || /E110/.test(d.message)),
        'actual E110 refused proof diagnostics');

    const second = await open('nested.cure', `mod HostNested
  fn convert(input: Int) -> Float = 1.0
  fn later(x: Int) -> Float = convert(?argument)
end
`);
    await cursor(second, '?argument');
    target('Int');
    assert.ok(api.observeGoals().goals?.[0].context.includes('x : Int'));
    await cursor(editor, 'rewrite using h');
    target('Equivalent(Int, x, y)');
    await Promise.all([vscode.commands.executeCommand('cure.restartLsp'),
        vscode.commands.executeCommand('cure.restartLsp')]);
    await cursor(editor, 'rewrite using h', true);
    target('Equivalent(Int, y, y)');

    const providerPath = path.join(workspace, 'template_provider.cure');
    const providerSource = `mod HostTemplateProvider
  macro Tactics
    tactic remote_close becomes rewrite using h
end
`;
    await fs.writeFile(providerPath, providerSource);
    const imported = await open('template_consumer.cure', `mod HostTemplateConsumer
  use Std.Equivalent
  use HostTemplateProvider
  fn theorem(x: Int, y: Int, h: Equivalent(Int, x, y)) -> Equivalent(Int, x, y) = proof chain
    x == y
    because
      remote_close
      exact reflexive(y)
end
`);
    await cursor(imported, 'remote_close');
    target('Equivalent(Int, x, y)');
    await cursor(imported, 'remote_close', true);
    target('Equivalent(Int, y, y)');
    const consumerVersion = imported.document.version;

    const providerDocument = await vscode.workspace.openTextDocument(providerPath);
    const providerEdit = new vscode.WorkspaceEdit();
    providerEdit.replace(providerDocument.uri, new vscode.Range(providerDocument.positionAt(0),
        providerDocument.positionAt(providerDocument.getText().length)),
        providerSource.replace('rewrite using h', 'by assumption'));
    assert.equal(await vscode.workspace.applyEdit(providerEdit), true);
    assert.equal(providerDocument.isDirty, true);
    await cursor(imported, 'remote_close');
    target('Equivalent(Int, x, y)');
    await cursor(imported, 'remote_close', true);
    target('Equivalent(Int, y, y)');
    assert.equal(await providerDocument.save(), true);
    await until(() => api.observeGoals().query?.uri === imported.document.uri.toString() &&
        api.observeGoals().query?.version === consumerVersion && api.observeGoals().kind === 'no-state',
        'saved provider invalidates unchanged active consumer');
    assert.equal(imported.document.version, consumerVersion);
    await cursor(imported, 'remote_close');
    target('Equivalent(Int, x, y)');
    await cursor(imported, 'remote_close', true);
    assert.equal(api.observeGoals().kind, 'no-state');

    await fs.writeFile(path.join(workspace, 'computed_provider.cure'), `mod HostComputedProvider
  use Std.Tactic
  use Std.Syntax
  use Std.Bool
  macro Tactics
    tactic imported_close computed by close_goal
  fn close_goal(g: Goal) -> MacroResult = match is_equality(g)
    True() -> expand(Std.Tactic.simplify(g))
    False() -> reject_goal("an equality is required")
end
`);
    const diskConsumer = `mod HostComputedConsumer
  use Std.Equivalent
  fn theorem(x: Int) -> Equivalent(Int, x, x) = reflexive(x)
end
`;
    const computed = await open('computed_consumer.cure', diskConsumer);
    const liveConsumer = `mod HostComputedConsumer
  use Std.Equivalent
  use HostComputedProvider
  fn theorem(x: Int) -> Equivalent(Int, x, x) = proof chain
    x == x
    because imported_close
end
`;
    await computed.edit(edit => edit.replace(new vscode.Range(computed.document.positionAt(0),
        computed.document.positionAt(computed.document.getText().length)), liveConsumer));
    assert.equal(computed.document.isDirty, true);
    await cursor(computed, 'imported_close');
    target('Equivalent(Int, x, x)');
    assert.ok(api.observeGoals().goals?.[0].context.includes('x : Int'));
    await cursor(computed, 'imported_close', true);
    assert.equal(api.observeGoals().kind, 'no-state');
    assert.equal(await fs.readFile(computed.document.uri.fsPath, 'utf8'), diskConsumer,
        'checking the active buffer must never overwrite its saved source');

    const malformed = await open('malformed.cure', 'mod Broken\n fn ( = ???\nend\n');
    await cursor(malformed, '???');
    assert.equal(api.observeGoals().kind, 'no-state');
    await open('plain.txt', 'not Cure');
    await until(() => api.observeGoals().kind === 'no-state' && !api.observeGoals().query, 'non-Cure clears state');
    await vscode.commands.executeCommand('workbench.action.closeAllEditors');
    assert.equal(api.observeGoals().kind, 'no-state');
    console.log('Real Cure Extension Host: activation/view/cursor/edit/E110/imported templates/computed/unsaved consumer/provider save/non-goal/malformed/two-file/multibyte/restart passed');
}
