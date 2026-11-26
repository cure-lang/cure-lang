const { test } = require('node:test');
const assert = require('node:assert/strict');
const { GoalRequests, decodeGoals } = require('../out/goalRequests');
const tick = () => new Promise(resolve => setTimeout(resolve, 5));
const query = (version = 1, character = 0, uri = 'file:///one.cure') => ({ uri, version, line: 1, character });
const answer = goal => ({ goals: [{ goal, context: ['x : Int'] }] });

function harness() {
    const states = [], calls = [];
    const requests = new GoalRequests(state => states.push(state), 0);
    const transport = { request(q) {
        let resolve, reject;
        const promise = new Promise((yes, no) => { resolve = yes; reject = no; });
        const call = { q, resolve, reject, cancelled: false };
        calls.push(call);
        return { promise, cancel() { call.cancelled = true; } };
    } };
    requests.setTransport(transport);
    return { states, calls, requests, transport };
}

test('debounces rapid selections and coalesces edits to one in-flight plus newest query', async () => {
    const h = harness();
    h.requests.select(query(1, 1));
    h.requests.select(query(1, 2));
    await tick();
    assert.equal(h.calls.length, 1);
    assert.equal(h.calls[0].q.character, 2);
    h.requests.select(query(2, 3));
    h.requests.select(query(3, 4));
    await tick();
    assert.equal(h.calls.length, 1);
    assert.equal(h.calls[0].cancelled, true);
    h.calls[0].resolve(answer('stale'));
    await tick();
    assert.equal(h.calls.length, 2);
    assert.deepEqual(h.calls[1].q, query(3, 4));
    assert.equal(h.states.some(s => s.goals?.[0]?.goal === 'stale'), false);
    h.calls[1].resolve(answer('Int'));
    await tick();
    assert.equal(h.states.at(-1).goals[0].goal, 'Int');
    h.requests.dispose();
});

test('replacement transport runs while old promise stalls and old finally cannot clear current request', async () => {
    const h = harness();
    const replacement = [];
    h.requests.select(query());
    await tick();
    h.requests.setTransport({ request(q) {
        let resolve;
        const promise = new Promise(yes => { resolve = yes; });
        replacement.push({ q, resolve });
        return { promise, cancel() {} };
    } });
    h.requests.select(query(2));
    await tick();
    assert.equal(h.calls[0].cancelled, true);
    assert.equal(replacement.length, 1, 'new transport cannot wait for old promise');
    h.calls[0].resolve(answer('obsolete'));
    await tick();
    h.requests.select(query(3));
    await tick();
    assert.equal(replacement.length, 1, 'old finally cannot erase current in-flight request');
    replacement[0].resolve(answer('superseded'));
    await tick();
    assert.equal(replacement.length, 2);
    replacement[1].resolve(answer('current'));
    await tick();
    assert.equal(h.states.at(-1).goals[0].goal, 'current');
    assert.equal(h.states.some(s => ['obsolete', 'superseded'].includes(s.goals?.[0]?.goal)), false);
    h.requests.dispose();
});

test('generation-changing synchronous transport exception cannot publish stale error', async () => {
    const h = harness();
    h.requests.setTransport({ request() {
        h.requests.setTransport();
        throw new Error('obsolete synchronous exception');
    } });
    h.requests.select(query());
    await tick();
    assert.equal(h.states.at(-1).kind, 'unavailable');
    assert.equal(h.states.some(s => s.message?.includes('obsolete synchronous exception')), false);
    h.requests.dispose();
});

test('restart generation rejects late answer even for identical URI/version/position', async () => {
    const h = harness();
    h.requests.select(query());
    await tick();
    h.requests.setTransport(h.transport);
    h.requests.select(query());
    h.calls[0].resolve(answer('old generation'));
    await tick();
    await tick();
    assert.equal(h.calls.length, 2);
    h.calls[1].resolve(answer('new generation'));
    await tick();
    assert.equal(h.states.at(-1).goals[0].goal, 'new generation');
    assert.equal(h.states.some(s => s.goals?.[0]?.goal === 'old generation'), false);
    h.requests.dispose();
});

test('switching files, clearing and disposal discard late successes and errors', async () => {
    for (const action of ['switch', 'clear', 'dispose']) {
        const h = harness();
        h.requests.select(query());
        await tick();
        if (action === 'switch') { h.requests.select(query(1, 0, 'file:///two.cure')); }
        else if (action === 'clear') { h.requests.clear(); }
        else { h.requests.dispose(); }
        const size = h.states.length;
        h.calls[0].reject(new Error('late failure'));
        await tick();
        assert.equal(h.states.length, size);
        h.requests.dispose();
    }
});

test('empty is no-state, malformed is error, unavailable is distinct', async () => {
    const h = harness();
    h.requests.select(query());
    await tick();
    h.calls[0].resolve({ goals: [] });
    await tick();
    assert.equal(h.states.at(-1).kind, 'no-state');
    h.requests.select(query(2));
    await tick();
    h.calls[1].resolve({ goals: [{ goal: 'Int', context: '<script>' }] });
    await tick();
    assert.equal(h.states.at(-1).kind, 'error');
    h.requests.setTransport();
    h.requests.select(query(3));
    assert.equal(h.states.at(-1).kind, 'unavailable');
    h.requests.dispose();
});

test('versioned response validation and plain source text preservation', () => {
    const q = query();
    assert.throws(() => decodeGoals({ ...answer('Int'), version: 2 }, q), /version/);
    assert.throws(() => decodeGoals({ ...answer('Int'), uri: 'file:///two.cure' }, q), /version/);
    assert.throws(() => decodeGoals({ goals: [null] }, q), /Malformed/);
    assert.deepEqual(decodeGoals({ goals: [{ goal: '<script>𐐀</script>', context: ['é : Int'] }], version: 1 }, q),
        [{ goal: '<script>𐐀</script>', context: ['é : Int'] }]);
});
