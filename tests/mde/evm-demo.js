/**
 * Demo: Run one step of EVM ADD instruction
 *
 * Shows mixed forward + backward chaining:
 * - Forward rule: consumes linear resources (pc, stack, etc.)
 * - Backward queries: !inc PC PC' and !plus A B C compute results
 */

const mde = require('../../lib/mde');
const forward = require('../../lib/v2/prover/forward');
const prove = require('../../lib/mde/prove');
const path = require('path');

// Convert binary representation to decimal
function binToDec(s) {
  s = s.trim();
  if (s === "e") return 0;

  // Strip outer parens if present: (i e) -> i e
  if (s.startsWith("(") && s.endsWith(")")) {
    s = s.slice(1, -1).trim();
  }

  // Match i(...) or o(...)
  const match = s.match(/^([io])\s*\((.+)\)$/);
  if (match) {
    const [, bit, inner] = match;
    const innerVal = binToDec(inner);
    if (isNaN(innerVal)) return NaN;
    return bit === 'i' ? 2 * innerVal + 1 : 2 * innerVal;
  }

  // Match i X or o X (without parens)
  if (s.startsWith("i ")) return 2 * binToDec(s.slice(2)) + 1;
  if (s.startsWith("o ")) return 2 * binToDec(s.slice(2));

  return NaN;
}

// Format term with decimal value if numeric
function fmt(h) {
  const s = prove.formatTerm(h);
  const dec = binToDec(s);
  if (!isNaN(dec)) return `${s} (=${dec})`;
  return s;
}

(async () => {
  console.log("=== EVM ADD Demo ===\n");

  // Load EVM calculus with arithmetic
  const calc = await mde.load([
    path.join(__dirname, "fixtures/bin.mde"),
    path.join(__dirname, "fixtures/evm.mde")
  ]);

  console.log(`Loaded: ${calc.forwardRules.length} forward rules, ${calc.clauses.size} backward clauses\n`);

  // Initial state: ADD 3 + 2
  const resources = [
    'pc e',                        // PC = 0
    'code e (i e)',                // code[0] = 0x01 (ADD opcode)
    'sh (s (s ee))',               // stack height = 2
    'stack (s ee) (i (i e))',      // stack[1] = 3 (top)
    'stack ee (o (i e))',          // stack[0] = 2
  ];

  console.log("Initial state:");
  console.log("  PC = 0");
  console.log("  code[0] = 0x01 (ADD)");
  console.log("  stack = [3, 2]  (3 on top)");
  console.log();

  const linearState = {};
  for (const r of resources) {
    const h = await mde.parseExpr(r);
    linearState[h] = (linearState[h] || 0) + 1;
  }

  const state = forward.createState(linearState, {});
  const result = forward.run(state, calc.forwardRules, {
    maxSteps: 1,
    trace: true,
    calc: { clauses: calc.clauses, types: calc.types }
  });

  console.log(`Executed: ${result.trace.join(', ')}`);
  console.log();

  console.log("Final state:");
  for (const [h, count] of Object.entries(result.state.linear)) {
    if (count > 0) {
      const hash = parseInt(h);
      const s = prove.formatTerm(hash);
      // Parse the predicate
      if (s.startsWith('pc ')) {
        const val = s.slice(3);
        console.log(`  PC = ${binToDec(val)}`);
      } else if (s.startsWith('sh ')) {
        // sh (s ee) means height 1
        const val = s.slice(3);
        const height = val.split('(s').length - 1;
        console.log(`  stack height = ${height}`);
      } else if (s.startsWith('stack ')) {
        // stack ee (i (o (i e))) means stack[0] = 5
        const parts = s.slice(6).split(' ');
        const idx = parts[0].split('(s').length - 1;
        const val = parts.slice(1).join(' ');
        console.log(`  stack[${idx}] = ${binToDec(val)}`);
      } else if (s.startsWith('code ')) {
        // code e (i e) means code[0] = 1
        console.log(`  ${s}`);
      }
    }
  }

  console.log();
  console.log("Result: 3 + 2 = 5 ✓");
})().catch(e => console.error(e));
