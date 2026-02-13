/**
 * Detailed analysis of backward prover operations
 */
const mde = require('../../lib/engine');
const path = require('path');
const Store = require('../../lib/kernel/store');
const { unify: originalUnify } = require('../../lib/kernel/unify');
const { apply: originalSubApply } = require('../../lib/kernel/substitute');
const { buildIndex } = require('../../lib/engine/prove');

// Per-operation counters
let opStats = {
  getHead: { calls: 0, gets: 0 },
  getFirstArgCtor: { calls: 0, gets: 0 },
  freshenTerm: { calls: 0, gets: 0, interns: 0 },
  freshenClause: { calls: 0, gets: 0, interns: 0 },
  unify: { calls: 0, gets: 0 },
  subApply: { calls: 0, gets: 0 }
};

let currentOp = null;

const realGet = Store.get.bind(Store);
Store.get = h => {
  if (currentOp) opStats[currentOp].gets++;
  return realGet(h);
};

const realIntern = Store.intern.bind(Store);
Store.intern = (t, c) => {
  if (currentOp && opStats[currentOp].interns != null) opStats[currentOp].interns++;
  return realIntern(t, c);
};

function getHead(hash) {
  currentOp = 'getHead';
  opStats.getHead.calls++;
  let h = hash;
  while (h) {
    const node = Store.get(h);
    if (!node) { currentOp = null; return null; }
    if (node.tag === 'atom') { currentOp = null; return node.children[0]; }
    if (node.tag === 'freevar') { currentOp = null; return null; }
    if (node.tag === 'app') h = node.children[0];
    else { currentOp = null; return null; }
  }
  currentOp = null;
  return null;
}

function getFirstArgCtor(hash) {
  currentOp = 'getFirstArgCtor';
  opStats.getFirstArgCtor.calls++;
  let h = hash, firstArg = null;
  while (h) {
    const node = Store.get(h);
    if (!node || node.tag !== 'app') break;
    firstArg = node.children[1];
    h = node.children[0];
  }
  currentOp = null;
  if (!firstArg) return null;

  // getHead will set its own currentOp
  const argHead = getHead(firstArg);
  if (argHead) return argHead;

  currentOp = 'getFirstArgCtor';
  const node = Store.get(firstArg);
  currentOp = null;
  return (node && node.tag === 'freevar') ? '_' : null;
}

function freshenTerm(h, counter, prefix = '') {
  currentOp = 'freshenTerm';
  opStats.freshenTerm.calls++;
  const suffix = '_' + prefix + counter;
  const renamed = new Map();

  function go(hash) {
    const node = Store.get(hash);
    if (!node) return hash;
    if (node.tag === 'freevar') {
      const name = node.children[0];
      if (typeof name === 'string' && name.startsWith('_')) {
        if (!renamed.has(hash)) {
          renamed.set(hash, Store.intern('freevar', [name + suffix]));
        }
        return renamed.get(hash);
      }
      return hash;
    }
    let changed = false;
    const newChildren = node.children.map(c => {
      if (typeof c === 'number') {
        const nc = go(c);
        if (nc !== c) changed = true;
        return nc;
      }
      return c;
    });
    return changed ? Store.intern(node.tag, newChildren) : hash;
  }

  const result = go(h);
  currentOp = null;
  return result;
}

function freshenClause(clause, counter) {
  currentOp = 'freshenClause';
  opStats.freshenClause.calls++;
  const suffix = '_c' + counter;
  const renamed = new Map();

  function go(h) {
    const node = Store.get(h);
    if (!node) return h;
    if (node.tag === 'freevar') {
      const name = node.children[0];
      if (typeof name === 'string' && name.startsWith('_')) {
        if (!renamed.has(h)) {
          renamed.set(h, Store.intern('freevar', [name + suffix]));
        }
        return renamed.get(h);
      }
      return h;
    }
    let changed = false;
    const newChildren = node.children.map(c => {
      if (typeof c === 'number') {
        const nc = go(c);
        if (nc !== c) changed = true;
        return nc;
      }
      return c;
    });
    return changed ? Store.intern(node.tag, newChildren) : h;
  }

  const result = { head: go(clause.hash), premises: clause.premises.map(go) };
  currentOp = null;
  return result;
}

function wrappedUnify(a, b) {
  currentOp = 'unify';
  opStats.unify.calls++;
  const result = originalUnify(a, b);
  currentOp = null;
  return result;
}

function wrappedSubApply(h, theta) {
  currentOp = 'subApply';
  opStats.subApply.calls++;
  const result = originalSubApply(h, theta);
  currentOp = null;
  return result;
}

function instrumentedProve(goal, clauses, types, opts = {}) {
  const maxDepth = opts.maxDepth || 100;
  const idx = opts.index || buildIndex(clauses, types);
  let freshCounter = 0;

  function localGetCandidates(goalHash) {
    const head = getHead(goalHash);
    if (!head) return { types: [], clauses: [] };
    const fa = getFirstArgCtor(goalHash) || '_';
    const ti = idx.types[head] || {};
    const ci = idx.clauses[head] || {};
    return {
      types: [...(ti[fa] || []), ...(fa !== '_' ? ti['_'] || [] : [])],
      clauses: [...(ci[fa] || []), ...(fa !== '_' ? ci['_'] || [] : [])],
    };
  }

  function search(g, theta, depth) {
    if (depth > maxDepth) return null;
    const goalInst = wrappedSubApply(g, theta);
    const { types: candTypes, clauses: candClauses } = localGetCandidates(goalInst);

    for (const [name, typeHash] of candTypes) {
      const freshType = freshenTerm(typeHash, freshCounter++, 'a');
      const newTheta = wrappedUnify(freshType, goalInst);
      if (newTheta !== null) return [...theta, ...newTheta];
    }

    for (const [name, clause] of candClauses) {
      const { head, premises } = freshenClause(clause, freshCounter++);
      const newTheta = wrappedUnify(head, goalInst);
      if (newTheta === null) continue;
      let currentTheta = [...theta, ...newTheta];
      let ok = true;
      for (const premise of premises) {
        const result = search(wrappedSubApply(premise, currentTheta), currentTheta, depth + 1);
        if (result === null) { ok = false; break; }
        currentTheta = result;
      }
      if (ok) return currentTheta;
    }
    return null;
  }

  const result = search(goal, [], 0);
  return { success: result !== null, theta: result };
}

async function main() {
  const calc = await mde.load([path.join(__dirname, '../../calculus/ill/programs/bin.ill')]);
  const idx = buildIndex(calc.clauses, calc.types);

  // Reset
  Object.keys(opStats).forEach(k => {
    opStats[k].calls = 0;
    opStats[k].gets = 0;
    if (opStats[k].interns != null) opStats[k].interns = 0;
  });

  const goal = await mde.parseExpr('plus (o (o (i (o (i e))))) (o (i (i (o (i (i (i e))))))) X');

  console.log('Proving: plus 20 118 X');
  console.log('');

  const result = instrumentedProve(goal, calc.clauses, calc.types, { index: idx, maxDepth: 100 });

  console.log('Success:', result.success);
  console.log('');
  console.log('Operation breakdown:');
  console.log('─'.repeat(60));

  let totalGets = 0;
  let totalCalls = 0;
  const rows = [];

  for (const [op, s] of Object.entries(opStats)) {
    if (s.calls > 0) {
      const avgGets = (s.gets / s.calls).toFixed(1);
      rows.push({ op, calls: s.calls, gets: s.gets, avg: avgGets, interns: s.interns });
      totalGets += s.gets;
      totalCalls += s.calls;
    }
  }

  // Sort by gets descending
  rows.sort((a, b) => b.gets - a.gets);

  for (const r of rows) {
    const pct = ((r.gets / totalGets) * 100).toFixed(1) + '%';
    let line = r.op.padEnd(18) +
               'calls: ' + String(r.calls).padStart(4) +
               '  gets: ' + String(r.gets).padStart(5) +
               '  avg: ' + String(r.avg).padStart(5) +
               '  ' + pct.padStart(6);
    if (r.interns != null && r.interns > 0) {
      line += '  interns: ' + r.interns;
    }
    console.log(line);
  }

  console.log('─'.repeat(60));
  console.log('TOTAL'.padEnd(18) + 'calls: ' + String(totalCalls).padStart(4) + '  gets: ' + String(totalGets).padStart(5));
}

main().catch(console.error);
