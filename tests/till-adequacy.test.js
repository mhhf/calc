/**
 * till timed judgment — TODO_0265 Phase 6b Stage 2 (D5/D6).
 *
 * The timed sequent: context entries are stamped atoms at(A,t) (D5 —
 * content-addressed (formula, stamp) pairs), the succedent {S}@T carries
 * the observation horizon as the monad grade (THY_0018 §5, n=0 boundary:
 * "the delay grade is the stamp of the future"). monad_r2 (@modeShift)
 * bridges to the TIMED engine: settle(Δ, T) then exact rightFocus of S
 * against the residual timed multiset — each firing is one @fire instance,
 * so bridge success implies settle-reachability AND derivability
 * (THY_0018 §5 bridge soundness: the bridge is a sound but NOT complete
 * oracle — monad_r derives subeffected goals with no forward step, so
 * derivable ⇏ settle-reachable). A prove() failure refutes the sequent
 * because BOTH the pure-backward and bridge routes are searched. These
 * tests witness the SOUNDNESS direction of the Stage 2 acceptance
 * (settle-reachable ⇒ derivable) plus refutations; they exercise settle
 * THROUGH the prover, so the non-circular content is the
 * rightFocus/retiming/decomposition layer around it. Ground truth: the
 * executable specs' #expect gates — the SAME lhs/rhs hashes are wrapped
 * here as sequents.
 *
 * THY_0018 theorems witnessed as (under)derivability:
 *   Thm 5 in-flight atomicity — no interaction inside (a, a+d)
 *   Thm 3 fission ≡ fusion — same J-free observables derivable
 */

import { describe, it, before } from 'node:test';
import assert from 'node:assert';
import path from 'path';
import Store from '../lib/kernel/store.js';
import Seq from '../lib/kernel/sequent.js';
import { buildRuleSpecs } from '../lib/prover/rule-interpreter.js';
import { createProver } from '../lib/prover/focused.js';
import { createKernel } from '../lib/prover/kernel.js';
import mde from '../lib/engine/index.js';
import tillConfig, { loadTillSequent, tillGrades } from '../calculus/till/calculus-config.js';
import { programFromCalc } from '../lib/prover/timed/elaborate-trace.js';

const SPEC = (f) => path.join(import.meta.dirname, '../calculus/till/tests/forward', f);
const FIX = (f) => path.join(import.meta.dirname, 'fixtures', f);
const loadEngine = (p) => mde.load(p, { calculusConfig: tillConfig, cache: false });

describe('till timed judgment: settle bridge (Stage 2)', () => {
  let calc, specs, alternatives, prover, kernel;

  before(() => {
    calc = loadTillSequent();
    ({ specs, alternatives } = buildRuleSpecs(calc));
    prover = createProver(calc);
    kernel = createKernel(calc);
  });

  // Δ ⊢ {S}@T from a gate's canonical hashes: context = lhs (one tensor
  // entry, tensor_l inverts), succedent = monad(T, rhs).
  const judge = (engineCalc, lhs, rhs, T) => {
    const succ = Store.put('monad', [tillGrades.parseStamp(T), rhs]);
    const seq = Seq.fromArrays([lhs], [], succ);
    return prover.prove(seq, { rules: specs, alternatives, engineCalc });
  };
  const gate = (engineCalc, kind) => engineCalc.splitQueries.get(kind);

  // Kernel-verification contract (TODO_0294 B2 gate flip): the bridge
  // ELABORATES the settle trace into an @fire chain by default, so trees
  // reach FULL verification — the kernel re-derives every firing from the
  // program's declared rule data (fire-check.js). No trusted modeSwitch
  // step remains for elaborable traces; unsupported shapes (whole-bind,
  // counted consequents) would fall back to the round-15 F1 oracle node.
  const derivable = (ec, r, desc) => {
    assert.ok(r.success, `expected derivable: ${desc}`);
    const v = kernel.verifyTree(r.proofTree, { program: programFromCalc(ec) });
    assert.ok(v.valid, `kernel rejected ${desc}: ${v.errors.join('; ')}`);
    assert.equal(v.unverified, undefined,
      `elaborated bridge trees reach FULL verification: ${desc}`);
  };

  describe('adequacy: executable-spec gates as sequents', () => {
    it('schedule: two jobs derivable at their gate horizons', () => {
      const ec = loadEngine(SPEC('schedule.ill'));
      const g = gate(ec, 'expect_two_jobs');
      derivable(ec, judge(ec, g.lhsHash, g.rhsHash, '1'), 'two_jobs @1');
      // composability (THY-B Thm 4): the same state derivable at T=0.7
      derivable(ec, judge(ec, g.lhsHash, g.rhsHash, '0.7'), 'two_jobs @0.7');
      const one = gate(ec, 'expect_one_job');
      derivable(ec, judge(ec, one.lhsHash, one.rhsHash, '0.4'), 'one_job @0.4');
    });

    it('schedule refutation: no early plank', () => {
      const ec = loadEngine(SPEC('schedule.ill'));
      const g = gate(ec, 'expect_not_early_plank');
      assert.ok(!judge(ec, g.lhsHash, g.rhsHash, '0.4').success);
    });

    it('spoilage: eaten derivable; rotten underivable at ANY horizon', () => {
      const ec = loadEngine(SPEC('spoilage.ill'));
      const eaten = gate(ec, 'expect_eaten_not_rotten');
      derivable(ec, judge(ec, eaten.lhsHash, eaten.rhsHash, '5'), 'eaten @5');
      const rotten = gate(ec, 'expect_not_rotten');
      for (const T of ['2', '5', '10', '100']) {
        assert.ok(!judge(ec, rotten.lhsHash, rotten.rhsHash, T).success,
          `rotten must be underivable at T=${T}`);
      }
    });
  });

  describe('in-flight atomicity as underivability (THY_0018 Thm 5)', () => {
    let ec, P;
    before(() => {
      ec = loadEngine(FIX('till-fused.ill'));
      P = (s) => calc.parse(s);
    });

    it('the fused pipeline runs to dtok@5', () => {
      derivable(ec, judge(ec, P('atok'), P('dtok@5'), '10'), 'dtok@5 @10');
    });

    it('nothing exists inside the open interval (0, 5)', () => {
      assert.ok(!judge(ec, P('atok'), P('ctok@2'), '10').success);
      assert.ok(!judge(ec, P('atok'), P('dtok@3'), '10').success);
    });

    it('the in-flight output is visible as a future stamp; the horizon gates consumption', () => {
      // at T=4 the job has fired (a=0) but drink (a=5) is pending
      derivable(ec, judge(ec, P('atok'), P('ctok@5'), '4'), 'ctok@5 @4');
      assert.ok(!judge(ec, P('atok'), P('dtok@5'), '4').success,
        'drink has not fired by horizon 4');
    });
  });

  describe('fission ≡ fusion (THY_0018 Thm 3, on the E7.3 fixture)', () => {
    it('both forms land the observable at the same stamp', () => {
      const P = (s) => calc.parse(s);
      const ec = loadEngine(FIX('till-fission.ill'));
      derivable(ec, judge(ec, P('a'), P('b@5'), '10'), 'fused b@5');
      derivable(ec, judge(ec, P('a2'), P('b2@5'), '10'), 'fissioned b2@5');
    });

    it('fission is observable mid-flight, fusion is not (the E7.3 trade)', () => {
      const P = (s) => calc.parse(s);
      const ec = loadEngine(FIX('till-fission.ill'));
      // at horizon 1 the fissioned intermediate m@2 is a derivable
      // observation; the fused job admits nothing before 5
      derivable(ec, judge(ec, P('a2'), P('m@2'), '1'), 'm@2 @1');
      assert.ok(!judge(ec, P('a'), P('b@2'), '10').success,
        'fused: nothing inside (0, 5)');
    });
  });

  describe('without an engine the timed rule is simply inapplicable', () => {
    it('production claims are underivable pure-backward', () => {
      const P = (s) => calc.parse(s);
      const seq = Seq.fromArrays([P('atok')], [], P('{dtok@5}@10'));
      assert.ok(!prover.prove(seq, { rules: specs, alternatives }).success);
    });
  });
});
