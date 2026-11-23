const { test } = require('node:test');
const assert = require('node:assert/strict');
const Module = require('node:module');

// Only the native VS Code value types are substituted here; the real provider
// runs unchanged. The separate official Extension Host gate uses no mocks.
const load = Module._load;
Module._load = function(name, ...args) {
    if (name === 'vscode') {
        return {
            EventEmitter: class { event = () => {}; fire() {} dispose() {} },
            TreeItem: class { constructor(label, collapsibleState) { Object.assign(this, { label, collapsibleState }); } },
            TreeItemCollapsibleState: { None: 0, Expanded: 2 }
        };
    }
    return load.call(this, name, ...args);
};
const { GoalProvider } = require('../out/goalView');
Module._load = load;

test('native provider renders targets, named hypotheses and source text only as string tooltips', () => {
    const provider = new GoalProvider();
    provider.update({ kind: 'goals', goals: [{
        function: 'theorem', goal: '<script>𐐀</script>', context: ['x : Int', 'h : P(x)']
    }] });
    const [root] = provider.getChildren();
    assert.equal(root.label, 'Goal 1 — theorem');
    assert.deepEqual(provider.getChildren(root).map(node => node.label),
        ['x : Int', 'h : P(x)', '⊢ <script>𐐀</script>']);
    const target = provider.getChildren(root)[2];
    assert.equal(provider.getTreeItem(target).tooltip, '⊢ <script>𐐀</script>');
    assert.equal(typeof provider.getTreeItem(target).tooltip, 'string');
    const detached = provider.observe();
    detached.goals[0].context[0] = 'mutated';
    assert.equal(provider.observe().goals[0].context[0], 'x : Int');
    provider.dispose();
});

test('native provider keeps loading/error/unavailable/no-state distinct and never claims closure', () => {
    const provider = new GoalProvider();
    const labels = [];
    for (const kind of ['loading', 'error', 'unavailable', 'no-state']) {
        provider.update({ kind });
        const [item] = provider.getChildren();
        labels.push(item.label);
    }
    assert.equal(new Set(labels).size, 4);
    assert.match(labels[3], /not a proof-completion claim/);
    provider.dispose();
});
