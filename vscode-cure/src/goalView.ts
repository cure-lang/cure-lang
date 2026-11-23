import * as vscode from 'vscode';
import { GoalState } from './goalRequests';

interface GoalNode { label: string; children?: GoalNode[]; }

const messages = {
    loading: 'Loading proof state…',
    'no-state': 'No proof state at this position (not a proof-completion claim).',
    unavailable: 'Cure language server is unavailable.',
    error: 'Unable to load proof state.'
};

export class GoalProvider implements vscode.TreeDataProvider<GoalNode>, vscode.Disposable {
    private readonly changed = new vscode.EventEmitter<void>();
    readonly onDidChangeTreeData = this.changed.event;
    private state: GoalState = { kind: 'unavailable' };

    update(state: GoalState): void {
        this.state = state;
        this.changed.fire();
    }

    /** Detached read-only observation; no transport or mutable provider access. */
    observe(): GoalState {
        return JSON.parse(JSON.stringify(this.state)) as GoalState;
    }

    getTreeItem(node: GoalNode): vscode.TreeItem {
        const item = new vscode.TreeItem(node.label, node.children ?
            vscode.TreeItemCollapsibleState.Expanded : vscode.TreeItemCollapsibleState.None);
        // A string tooltip is plain text, not trusted Markdown or source HTML.
        item.tooltip = node.label;
        return item;
    }

    getChildren(node?: GoalNode): GoalNode[] {
        if (node) { return node.children ?? []; }
        if (this.state.kind !== 'goals') {
            return [{ label: this.state.message ?? messages[this.state.kind] }];
        }
        return (this.state.goals ?? []).map((goal, index) => ({
            label: `Goal ${index + 1}${goal.function ? ` — ${goal.function}` : ''}`,
            children: [
                ...goal.context.map(label => ({ label })),
                { label: `⊢ ${goal.goal}` }
            ]
        }));
    }

    dispose(): void { this.changed.dispose(); }
}
