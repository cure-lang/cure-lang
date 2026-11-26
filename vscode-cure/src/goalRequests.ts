export interface GoalQuery {
    uri: string;
    version: number;
    line: number;
    character: number;
}

export interface Goal {
    goal: string;
    context: string[];
    function?: string;
}

export type GoalState = Readonly<{
    kind: 'loading' | 'goals' | 'no-state' | 'unavailable' | 'error';
    message?: string;
    query?: GoalQuery;
    goals?: readonly Goal[];
}>;

export interface GoalTransport {
    request(query: GoalQuery): { promise: Promise<unknown>; cancel(): void };
}

export function decodeGoals(value: unknown, query: GoalQuery): Goal[] {
    if (!value || typeof value !== 'object') {
        throw new Error('Malformed proof-state response');
    }
    const response = value as Record<string, unknown>;
    if ((response.version !== undefined && response.version !== query.version) ||
        (response.uri !== undefined && response.uri !== query.uri)) {
        throw new Error('Proof-state response belongs to another document version');
    }
    if (!Array.isArray(response.goals) || !response.goals.every(goal =>
        goal && typeof goal.goal === 'string' && Array.isArray(goal.context) &&
        goal.context.every((entry: unknown) => typeof entry === 'string') &&
        (goal.function === undefined || typeof goal.function === 'string'))) {
        throw new Error('Malformed proof-state response');
    }
    return response.goals.map(goal => ({ ...goal, context: [...goal.context] }));
}

/** One request per transport generation, even when cancellation does not stop the server. */
export class GoalRequests {
    private epoch = 0;
    private generation = 0;
    private desired?: { query: GoalQuery; epoch: number; generation: number };
    private active?: { cancel(): void };
    private timer?: ReturnType<typeof setTimeout>;
    private transport?: GoalTransport;
    private disposed = false;

    constructor(private readonly publish: (state: GoalState) => void, private readonly delay = 100) {}

    setTransport(transport?: GoalTransport): void {
        this.generation++;
        this.active?.cancel();
        // A replaced/disposed server may never settle its old request promise.
        // It must not hold the new transport's queue hostage.
        this.active = undefined;
        this.transport = transport;
        this.clear(transport ? 'no-state' : 'unavailable');
    }

    select(query?: GoalQuery): void {
        if (this.disposed) { return; }
        this.epoch++;
        this.active?.cancel();
        clearTimeout(this.timer);
        this.timer = undefined;
        this.desired = query ? { query: { ...query }, epoch: this.epoch, generation: this.generation } : undefined;
        if (!query) {
            this.publish({ kind: 'no-state', message: 'Select a Cure document to inspect proof goals.' });
        } else if (!this.transport) {
            this.publish({ kind: 'unavailable', query, message: 'Cure language server is unavailable.' });
        } else {
            this.publish({ kind: 'loading', query });
            this.timer = setTimeout(() => { this.timer = undefined; this.pump(); }, this.delay);
        }
    }

    clear(kind: 'no-state' | 'unavailable' = 'no-state'): void {
        this.select();
        if (!this.disposed) { this.publish({ kind }); }
    }

    dispose(): void {
        this.disposed = true;
        this.epoch++;
        this.desired = undefined;
        clearTimeout(this.timer);
        this.active?.cancel();
    }

    private pump(): void {
        if (this.disposed || this.active || this.timer || !this.desired || !this.transport) { return; }
        const wanted = this.desired;
        this.desired = undefined;
        let request: ReturnType<GoalTransport['request']>;
        try {
            request = this.transport.request(wanted.query);
        } catch (error) {
            if (!this.disposed && wanted.epoch === this.epoch && wanted.generation === this.generation) {
                this.publish({ kind: 'error', query: wanted.query, message: String(error) });
            }
            return;
        }
        this.active = request;
        const current = () => !this.disposed && wanted.epoch === this.epoch && wanted.generation === this.generation;
        void request.promise.then(value => {
            if (!current()) { return; }
            const goals = decodeGoals(value, wanted.query);
            this.publish({ kind: goals.length ? 'goals' : 'no-state', goals, query: wanted.query });
        }).catch(error => {
            if (current()) {
                this.publish({ kind: 'error', query: wanted.query, message: String(error) });
            }
        }).finally(() => {
            if (this.active === request) { this.active = undefined; }
            this.pump();
        });
    }
}
