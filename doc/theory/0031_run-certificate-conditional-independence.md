---
title: "Certified Conditional Independence: Separation on Dynamic Derivation Forests"
created: 2026-09-02
modified: 2026-09-02
summary: "T4-d(iii), the will track's last open theorem, proved at draft grain: wave variables are defined on existence events via ungrounded provenance keys (D1); the dependency graph of a conditioning class is the key-identified union of run graphs, where a draw event operationally consumes and re-emits every evar-carrying fact (value flow IS fact flow), linear contests contribute latent allocation forks, and conditioning enters as three kinds of sites — Z-draws, observed-fact colliders, and MASS-CHILDREN: in restriction semantics a wave whose total posterior weight is not constant across the class (bias, or an unnormalized sort whose draw HAPPENS in only some runs — by contingent existence or by drop) acts as observed soft evidence hung off the draw node itself, and naive d-separation without this discipline is UNSOUND (pinned twice: a contingent wave of total prior mass 2 leaks dependence through its mere existence, and an always-existing wave leaks it through being DROPPED on the diagonal — the same-day adversarial pass's finding, repaired at the root). Separation ⟹ the conditioned mass factorizes exactly, μ(x,y,z) = c·f(x)·g(y), the factors readable as sub-forest (sub-certificate) masses and the split exhibited by the certificate's token partition. The proof runs induction-free through five lemmas: normalization decomposition (mass = normalized ancestral probability × per-node evidence factors), barren-subforest marginalization (needs a.s. finiteness), the moral-graph side split (standard graph theory, cited), factor mono-sidedness, and the recombination bijection (the genuinely dynamic core: separated sides of a class merge freely into class runs — where fixed-variable BN proofs have a product space, will has an exchange argument over event configurations). Soundness only: per-run actual-edge graphs are refuted by a pinned counterexample (a context-specific bias edge absent from every X=vb certificate), so separation is read on the class graph, decided on a static cover — the LDAG/CSI lesson, inherited deliberately."
tags: [linear-logic, probabilistic, will, provenance, conditioning, independence, certificates, proof-theory, graded-types, soundness]
category: "Probabilistic Generation"
unique_contribution: "The first conditional-independence theorem at the level of RUNS of a probabilistic forward-chaining calculus: separation on the dependency graph carried by run certificates of execution-generated (dynamic, possibly unbounded) derivation forests implies exact ℚ factorization of the unnormalized conditioned mass, with the factors exhibited by the certificate's token partition (existing CI theory proves separation theorems about MODELS — fixed BNs, proof nets, string diagrams, type-annotated programs; RES_0142 verified all five axes open). Three structural discoveries en route: (1) MASS-OBSERVED DRAWS — under unnormalized restriction semantics, a wave's total posterior weight is soft evidence on whether its draw happens, so any wave whose total varies across the conditioning class (bias, or a total ≠ 1 with existence OR drop varying) must enter d-separation as a conditioned virtual child of the draw node itself; without this the classic collider rules are unsound (pinned counterexamples: dependence through bare existence, and through a drop — a wave that always exists but loses its evar-carrier on the diagonal). (2) Value flow needs no edge sort of its own: modeling the draw event as consuming and re-emitting every evar-carrying fact (which is operationally exact — substituteEvar) makes d-separation's directional collider discipline literally the resource-flow discipline of the certificate. (3) Linear-resource contests are an influence channel invisible to fact-flow DAGs; latent allocation forks restore soundness and vanish exactly in certifyContention's conflict-free regime. Plus the counterexample making the object-level design forced: certificates of runs where a context-specific rule never fired carry no trace of it, so per-run actual-edge separation is unsound and the criterion must quantify over the class (computably: a statically pruned cover)."
references:
  - "TODO_0302 — the plan this discharges (M1 definitions, M2 factorization, M3 criterion, M4 soundness; M0's sweep = RES_0142)"
  - "THY_0026 §8 — T1 (the measure), T2 (subcriticality = H1), T3 (importance); §6 T4-d, the conjecture family"
  - "THY_0027 — trace-judgment cut admissibility; tokens in the zone; §8 focused counting + driver adequacy (L1's citation)"
  - "THY_0028 — single-counting + certificate visibility (Theorem 1 is this theorem's unconditional base case; the smuggling programs are M3 stress tests)"
  - "THY_0029 — leg (ii): ⊗-context splitting of the token zone (the per-derivation face of Lemma M2)"
  - "THY_0030 — conditioning by restriction (B4; the zero-variance identity is the telescoped special case of the mass-child discipline)"
  - "RES_0142 (hq) — the positioning sweep: all five novel axes verified open; the criterion's soundness-only stance and the static-cover design follow its §9"
  - "Di Guardia, Ehrhard, Evrard & Faggian (2026). arXiv:2602.04045, Thm 7.1 (disconnection ⟹ CI on a FIXED BN-as-proof-net — the static cousin; Lemma 2's atom-tree is the fixed analogue of our fact-flow edges)"
  - "Bao, Docherty, Hsu & Silva (2021). DIBI. LICS (qualitative CI as a bunched formula, Thm V.1 — the program-logic ancestor)"
  - "Li, Ahmed & Holtzen (2023). Lilac. PLDI (CI = ∗ under the disintegration modality; program-level, fixed Ω)"
  - "Fritz & Klingler (2023). The d-Separation Criterion in Categorical Probability. JMLR 24(46) (Thm 34 — Markov categories WITH conditionals, fixed string diagrams; usable only as a per-unfolding cross-check on ρ̂-normalized runs, per RES_0142 §3)"
  - "Verma & Pearl (1988); Lauritzen (1996), Prop. 3.25 / Thm 3.27 (moral-graph reduction of d-separation; the cited graph-theory backbone of L3)"
  - "Milch et al. (2005). Contingent Bayesian Networks / BLOG (per-world contingent variables — the D1 ancestor; no CI calculus)"
  - "Boutilier, Friedman, Goldszmidt & Koller (1996). Context-Specific Independence. UAI; Pensar et al. (2015). LDAGs (CSI-separation sound-NOT-complete — the incompleteness precedent our soundness-only stance inherits)"
  - "Meek (1995). Strong completeness and faithfulness in Bayesian networks. UAI (the genericity route for M6)"
  - "Darwiche & Marquis (2002). Knowledge compilation map. JAIR (decomposability = indeterminate-disjoint factorization — Lemma M2's circuit-side reading)"
  - "Green, Karvounarakis & Tannen (2007). Provenance Semirings. PODS (the polynomial face)"
  - "Winskel (1987). Event Structures (configurations; the recombination lemma's frame)"
  - "Rueckschloss & Weitkämper (2023). ILP (d-separation for probabilistic logic programs on the fixed ground Herbrand graph — the closest logic-programming prior)"
---

# Certified Conditional Independence on Dynamic Derivation Forests

**Status.** Proved at draft grain (2026-09-02, one session): definitions
(§2, M1), factorization lemma (§3, M2), separation criterion (§4, M3),
soundness theorem with a five-lemma proof (§5, M4); genericity converse
left as a conjecture with a route (§6, M6). FIRST adversarial pass done
same day (the THY_0027 discipline), two findings, both repaired at the
root: (1) the mass-child V_e must hang off the DRAW NODE itself — the
drop half of "the draw happens" leaks dependence exactly like the
existence half, pinned as pin 2b before the repair was written; (2) the
policy-order-sensitive-bias scope boundary is T1's, inherited and now
stated (§7). A FRESH-EYES audit (Denis / a later session) is still
required before the sequel paper leans on §5; the two places relying on
cited or previously-sketched material are flagged inline (L1's
driver-adequacy extension, L3's graph theory). The design decisions are
pinned numerically: `tests/engine/will-ci.test.js` — five programs whose
exact conditioned masses (engine-computed, hand-verified) refute the
naive criteria and witness the sound one.

## 1. Setting and scope

Fix a will program P (rules, clauses, priors ρ, datasort declarations),
an initial boundary state σ₀, and a horizon. The sample space Ω is the
set of leaves of the collapse tree (THY_0026 §8): maximal collapse paths
under the driver, each an alternation of deterministic settle segments
and draw events. The measure μ assigns a leaf the product of its
posterior draw weights w(e,c) = ρ(c)·Π{distinct bias factors} times its
woplus branch weights (T1); μ is unnormalized (ℚ≥0-valued),
policy-independent (the will paper's Cor. 7.2 — the derivation tree is
the org chart, not a schedule), and conditioning is RESTRICTION (B4,
THY_0030): excluded runs go to zero, surviving masses are untouched.

Scope hypotheses, each doing named work below:

- **(H1) a.s. finiteness.** Every class run is finite with probability 1
  under the normalized process (T2's subcriticality is the sufficient
  static condition; adversarial bias that breaks it puts a program
  outside scope, exactly as in THY_0026 §8 T2). Needed for barren-
  subforest marginalization (L2′) and for infinite-class sums, which
  live in ℝ≥0 ∪ {∞} by monotone convergence; on finite classes and
  f4-fenced datasorts every quantity is exact ℚ.
- **(H2) exact-mode legality.** No settle conflict is reachable in the
  class (the driver's loud-error discipline; certifiable in the
  structural regime by `calc.certifyContention`). Without H2 the measure
  itself is chooser-dependent and T1 does not apply. Residual contests
  the static check cannot exclude are represented in the graph as
  allocation forks (§2e) — the criterion then refuses separation rather
  than assuming the contest away.
- **(H3) supported conditioning.** The context z is a finite conjunction
  of (i) wave-value assignments Z = z_Z and (ii) leaf-observations of
  ground facts (F present in the final state). Both are events of Ω;
  their graph sites are defined in §2d.
- **(H4) positive premises.** Rule and clause premises are positive
  patterns (all of will today): there is no fires-on-absence channel.
  Absence influences mass only through weights (bias 0), which the
  mass-child discipline covers.

The evidence discipline S1–S3 (THY_0028) is NOT a soundness hypothesis:
smuggled sharing ($-reads, promotions, whole-binds) is recorded in the
certificate (reserved multisets, SLD support) and yields EDGES, so a
smuggled program merely has a denser graph and separates less often.
S1–S3 matter for the exhibition reading (§5, Cor. 3): they make the
factor structure of the mass coincide with the token structure of the
certificate.

## 2. Definitions (M1)

### 2a. Events and the run graph

A run r has three kinds of **events**: the initial event ⊥ (emitting
σ₀'s facts), one **fire event** per rule firing in its settle segments,
and one **draw event** d_e per wave e opened in r, with OUTCOME SPACE
members(sort) ∪ {dropped} — a wave whose evar-carrier is consumed
before its draw resolves to `dropped` with factor 1 (plain-∃ skolems
are token-free open events and carry no weight). The
run's certificate (certifyCollapse, elaborate-collapse.js) records
exactly these as @fire and @draw nodes with their consumed / produced /
reserved multisets, bias and alt factors, SLD support for clause-derived
persistent goals, and the endsequent Δ₀, ⟨Θ⟩ ⊢ {∃sk. ⊗residual}@h.

**The draw event is operationally a rewrite**: when e is drawn to c, the
engine substitutes e's evar throughout the state (`substituteEvar`).
Model it exactly so: d_e consumes its suspension fact and every fact
instance carrying e's evar, and re-emits their grounded images. This one
modeling decision makes VALUE flow a special case of FACT flow — no
second edge sort is needed, and the directional (collider) discipline of
§4 is literally the resource-flow discipline of the certificate.

**Edges of the run graph G(r)** (a DAG — every edge respects causal
order): u → v whenever an instance emitted by u is consumed, reserved
($-read), whole-bound, or used as SLD support by v. In particular:

- producer → fire (linear consumption, reservation, whole-bind);
- producer → fire (persistent facts read by the fire's own persistent
  premises or inside its clause derivations — the SLD certificates make
  this projection of the certificate total);
- spawner → d_e (the suspension fact: the EXISTENCE edge);
- bias/within producer → d_e (facts read by the posterior at e's draw;
  a bias fact derived causally after the draw biases nothing and
  contributes no edge);
- d_e → consumer (grounded facts — value flow, per the rewrite reading).

Facts consumed before e's draw while still carrying the evar flow from
their producers directly (the evar is opaque to matching), correctly
carrying no dependence on e's value.

### 2b. Wave variables under random existence (D1)

Certificates exist in two views: the recorded trace (evars in place) and
its post-hoc grounding σ. Identity lives in the UNGROUNDED view. Define
**provenance keys** recursively: κ(⊥-fact) = its hash; κ(fire) = (rule,
multiset of κ of its input instances, occurrence index); κ(instance) =
(κ of its producer, position); κ(d_e) = κ(e's suspension instance) —
all computed on ungrounded facts, evars mapped to the keys of their
waves. Keys are well-founded (a key contains only keys of causal
ancestors), and two runs assign the same key to events with the same
ungrounded causal history.

A **wave variable** X is a provenance key of a draw event. Its
**existence event** E_X ⊆ Ω is the set of runs containing an event
keyed κ(X); on E_X its **value** X(r) is the drawn member (head
constructor for rung-2 structured draws — matching the per-constructor
prior discipline; the argument waves are variables of their own).
Values change which downstream rules fire, so downstream waves are
genuinely contingent: a wave spawned only in the X = a worlds has
E ⊆ [X = a]. This is the contingent-variable reading of BLOG/CBN done
proof-theoretically, as RES_0142 §9 prescribes; derived facts are
deterministic functions of draws given structure and inherit their
theory as a corollary through provenance (d3, waves-first).

### 2c. The measure statements

For variables X̄ and values x̄, [X̄ = x̄] = {r : each Xᵢ exists in r with
Xᵢ(r) = xᵢ}; contexts z (H3) denote their event C_z ⊆ Ω. All statements
are division-free (exact ℚ, zero-safe):

> **Definition (CI).** X ⊥ Y | z iff for all values x, x′, y, y′:
> μ([X=x][Y=y]C_z) · μ([X=x′][Y=y′]C_z)
> = μ([X=x][Y=y′]C_z) · μ([X=x′][Y=y]C_z).

Factorization μ([X=x][Y=y]C_z) = f(x)·g(y) implies CI in this form by
direct computation; the theorem proves factorization.

### 2d. Conditioning sites

Three kinds of graph sites, uniformly "nodes observed at a fixed
outcome", so that all M-outcomes are determined by z (used in L5):

1. **Z-draws**: the real nodes d_Z, outcome fixed to z_Z.
2. **Observation colliders**: for each observed fact F a virtual node
   O_F with an edge u → O_F from EVERY class-run event that produces or
   consumes an F-instance, observed at "present at the leaf". Leaf
   presence is a joint function of exactly these parents, and because
   different class runs may realize F through different producers, O_F
   is intrinsically disjunctive — modeling it as an observed collider
   (rather than conditioning the producers themselves) is what keeps
   the disjunction sound.
3. **Mass-children**: for each wave e let λ_e(r) = T_e(r) if e is drawn
   in r (T_e the total posterior weight at e's draw, = Σ_c w(e,c),
   including inside masses for conditioned sorts) and λ_e(r) = 1 if e
   is absent or dropped. If λ_e is constant across C_z it is a harmless
   global factor. Otherwise add a virtual node V_e, observed, with
   edges from **d_e ITSELF** and from e's bias/within parents: λ_e is a
   function of d_e's outcome (member vs `dropped` — §2a) and the bias
   context, and nothing less. **This is forced by restriction
   semantics**: T_e is exactly a soft-evidence likelihood — with bias
   present, T_e varies with the bias context; with T_e ≠ 1, whether e's
   draw HAPPENS multiplies the run mass. Both halves of "happens" leak,
   and both are pinned: pin 2 (existence — a wave spawned only when
   X = Y, drawn and never used, at total prior mass 2: μ gains the
   factor 2 exactly on the diagonal, X ⊥̸ Y, though the spawn fire is an
   unobserved collider textbook d-separation calls blocked) and pin 2b
   (drop — the audit's finding 1: a wave that ALWAYS exists but whose
   evar-carrier is consumed before its draw exactly when X = Y = va
   pays T on the three other cells only; masses 1/4/4/8, dependence
   again, and the normalized twin is clean). The drop half is why V_e
   hangs off d_e rather than off e's spawner: drop-vs-draw is decided
   by whoever consumes the carrier first, which is a CONTEST between
   the consuming fire and d_e (a consumer of the same instances under
   §2a's rewrite reading) — covered by the allocation forks of §2e, so
   the deciding events are d-connected to d_e and the moral clique
   {V_e, d_e, bias-parents} carries the factor. Naive d-separation is
   unsound for unnormalized measures; the mass-child discipline repairs
   it. (THY_0030's zero-variance identity is the telescoped one-wave
   shadow: totals are importance factors.)

The site set M = {d_Z} ∪ {O_F} ∪ {V_e : λ_e non-constant}.

### 2e. The class graph, allocation forks, and the static cover

The **class graph** 𝒢[σ₀ | z] is the union of the run graphs G(r) over
r ∈ C_z under key identification, plus the sites of §2d, plus:

- **Allocation forks**: whenever two events of 𝒢 consume the SAME fact
  instance (same key) — possible across different runs even under H2 —
  add a latent unobserved node alloc with edges to both consumers.
  Contested linear supply is an influence channel (who gets the token
  depends on who else is enabled) invisible to pure fact flow; the fork
  makes it a d-connection. In certifyContention's structural regime no
  instance is ever contested and no forks exist.

𝒢 is a DAG on keys (edges follow key well-foundedness; virtual nodes
are sinks, allocation forks are sources into their competitors).

𝒢 quantifies over the class, so it is not directly computable from one
certificate — and cannot be replaced by one run's actual edges: **pin 3
refutes per-run separation.** A bias rule enabled only in the X = va
world makes Y depend on X (exact masses 3/2/2/4, cross-products 12 ≠ 4),
yet every X = vb certificate contains no bias fire at all: the
connecting edge is absent from the very runs it endangers. The theorem
is therefore stated for any DAG COVERING 𝒢 (a graph into which 𝒢 maps
preserving edges and sites), and decidability comes from a finite
**static cover**: nodes = rule names, binder occurrences, and initial
facts; edges by predicate-level unifiability of emissions against
premises (all channels, including bias/within targeting and potential
contests); context pruning deletes a rule node only when z alone
falsifies it (e.g. a premise demanding member m directly of a Z-wave's
witness with z_Z ≠ m — any certified-sound pruning predicate may
sharpen this). Every run event maps to its rule/binder; the covering
property is L3′ below. This two-level design — semantic theorem on the
class graph, checkable criterion on a pruned cover — is the LDAG/CSI
architecture, inherited deliberately, and is the source of the
soundness-only stance (§7).

## 3. The factorization lemma (M2)

Call a family ℛ of runs **decomposable along (𝒜, ℬ)** when there are
maps r ↦ (π_A(r), π_B(r)) with: (i) mass(r) = m_A(π_A(r)) · m_B(π_B(r))
for weight functions m_A, m_B; (ii) r ↦ (π_A, π_B) is a bijection
ℛ ≅ 𝒜 × ℬ.

> **Lemma (M2).** For decomposable ℛ:
> Σ_{r∈ℛ} mass(r) = (Σ_{α∈𝒜} m_A(α)) · (Σ_{β∈ℬ} m_B(β)),
> in ℝ≥0 ∪ {∞} (monotone rearrangement of a countable double sum of
> non-negative terms; exact ℚ when both sums are finite).

The per-run face is THY_0029 leg (ii) + THY_0028 Theorem 1: the
certificate's token zone splits Θ = Θ_A ⊎ Θ_B across the partition
(tokens are linear and follow their events), the fire chain's
provenances split with it, and the two prior products multiply to the
run's prior mass. The polynomial face: writing each run's monomial in
the indeterminates X_{(key, member)} (the trace polynomial of THY_0027
§6, conditioned by restriction to ℛ), decomposability says the
conditioned polynomial is a PRODUCT of two polynomials in disjoint
indeterminates — decomposability in exactly the d-DNNF/scope-partition
sense, and evaluation at ρ (the provenance homomorphism) turns the
polynomial identity into the mass identity. The work of the theorem is
entirely in producing (i) and (ii) from separation; that is §5.

## 4. The separation criterion (M3)

> **Definition (separation).** Let 𝒢⁺ be any DAG covering 𝒢[σ₀ | z]
> with site set M (§2d–e). X ⊥sep Y | z iff every path between d_X and
> d_Y in 𝒢⁺ is blocked given M: a non-collider path node in M blocks;
> a collider path node blocks unless it or one of its descendants is
> in M.

Design decisions, each validated:

- **Colliders à la d-separation, on resource flow (D4).** Pin 1: two
  waves feeding one fire are marginally independent (cross-products
  4 = 4, engine-exact) — the unobserved v-structure blocks; observing
  the fire's output breaks it (1·4 ≠ 0, explaining away). The
  directional discipline is available precisely because §2a makes every
  edge a resource edge with the draw event as rewriter.
- **Mass-children (the restriction-semantics repair).** Pins 2 and 2b,
  §2d — existence and drop are the two halves of "the draw happens",
  and both leak when T ≠ 1. Without V_e-sites (hung off the draw node
  itself) the criterion is UNSOUND, not merely incomplete.
- **Chains and forks block at conditioned nodes.** Pin 4: a spawn-order
  chain X → M → Y (context-specific spawning rules + bias) has
  X ⊥ Y | M = m exactly (80 = 80 and 16 = 16) and X ⊥̸ Y marginally
  (168 ≠ 264).
- **Class quantification (D1).** Pin 3, §2e: per-run actual-edge graphs
  are unsound; the criterion reads the cover.
- **Smuggling (D3).** THY_0028's smuggled program C shares one $-read
  observation between two bias fires; the reservation edges put both
  fires downstream of one producer — a fork — so any separation query
  through them sees the shared channel. The linear-evidence discipline
  is what makes the graph SPARSE and the token partition meaningful; it
  is not what makes the criterion sound.

The criterion claims soundness only. Completeness fails for the classic
reasons (parameter cancellation as in BNs; CSI-separation is already
sound-not-complete on static LDAGs) plus a new one: the static cover's
conservatism (unpruned rules that no class run can fire). §6 records
the genericity converse as the right partial converse.

## 5. The soundness theorem (M4)

> **Theorem.** Under H1–H4, if X ⊥sep Y | z (any cover 𝒢⁺), then there
> are f, g : members → ℝ≥0 ∪ {∞} and a constant c_M with
>
>   μ([X=x][Y=y]C_z) = c_M · f(x) · g(y)   for all x, y,
>
> hence X ⊥ Y | z (§2c). Moreover f(x) is the conditioned mass of the
> X-side sub-forest (the A∪M-projection of the class, a family of runs
> of the A-restricted program) and g(y) of the Y-side, and every class
> certificate exhibits the split: its events, token zone, and fire
> provenances partition along (A, B) (Cor. 3).

Throughout, work in the ancestral closure An := An({d_X, d_Y} ∪ M) of
𝒢⁺ (all nodes with a directed path into the query or site nodes).

**L1 (locality / configurations).** Class runs are exactly the maximal
conflict-free, causally-closed configurations of the class's event
structure (events = keys, causality = edges, conflict = contested
instances and alternative outcomes of one draw) that satisfy z, each
weighted by the product of its draw weights; every configuration is
realized by exactly one run per policy, and the measure is
policy-independent. *Grain:* this is the will paper's driver-adequacy
bijection (Cor. 7.2's machinery: post-hoc grounding sound by bias
monotonicity, injectivity by first divergent draw, surjectivity because
the derivation tree is the org chart) restated over configurations; the
restatement is verbatim once events are keyed as in §2b, and is flagged
for the audit pass rather than re-derived here.

**L2 (normalization decomposition).** Per class run,
mass(r) = Π_{d∈r} p̂_d(outcome | parents) · Π_{e} λ_e(r) · Π 1_{O}(r),
where p̂_d = w_d / T_d is the normalized posterior (a probability
kernel in the parents' outcomes), λ_e the mass-child factors (§2d,
constant λ's absorbed into c_M), and the indicators enforce z. Each
factor is a function of one node and its parents in 𝒢⁺ — for p̂_d
because the posterior reads exactly the suspension, bias, and within
parents (T1/M8); for λ and 1_O by construction of the virtual sites;
allocation outcomes are determined inside the configuration. The first
product defines the normalized ancestral process P̂, a probability
measure on configurations (proper by H1).

**L2′ (barren marginalization).** Nodes outside An carry factor p̂ only
(a λ ≠ 1 or an indicator would put them in An as ancestors of M). Fix
an An-projection; its fiber (all ways the barren part can extend it)
has P̂-total 1: the barren part is a subforest generated below the
projection, its draws are normalized, and H1 makes the generation
a.s. finite — the sum telescopes to 1 by monotone convergence, wave by
wave (this is the irrelevant-subforest integration; it is FALSE for
raw masses, which is again why the mass-children exist). Hence all
sums below range over An-projections with the An-restricted factors.

**L3 (side split — cited graph theory).** d-separation of d_X and d_Y
by M in the DAG 𝒢⁺ is equivalent to separation of d_X and d_Y by M in
the MORAL graph of An (marry all co-parents, drop directions; Lauritzen
1996, Prop. 3.25). Let A = the component side of d_X in (moral graph
minus M), B = the rest of An minus M; d_Y ∈ B.

**L4 (mono-sidedness).** Each factor of L2 is a function of a clique
{v} ∪ pa(v) of the moral graph (parents are pairwise married), and a
clique cannot straddle a separator: every factor lies wholly in A ∪ M
or wholly in B ∪ M. Assign M-only factors to the A side. Site outcomes
are fixed by z (§2d), so the A-side factor product is a function of the
A∪M-projection alone, evaluated at the fixed site outcomes; likewise B.

**L5 (recombination — the dynamic core).** The map r ↦ (π_{A∪M}(r),
π_{B∪M}(r)) restricted to An-projections is a bijection between class
An-projections and pairs (α, β) that agree on the (z-fixed) M-part:

- *Well-defined & injective*: A ∪ M and B ∪ M cover An; an event's
  parents lie in its own side ∪ M (L4's clique argument), so each side
  projection is itself causally closed and the pair determines the
  An-projection.
- *Surjective (the exchange argument)*: given α, β from class runs r₁,
  r₂, the merge α ∪ β is causally closed (parents per side), satisfies
  z (site outcomes agree and are z-fixed), and is conflict-free: a
  conflict would be two events consuming one instance; cross-side
  consumers of one instance induce an allocation fork with edges into
  both sides — an unobserved source, i.e. an active fork path between
  the sides — contradicting separation (paths within one side ∪ M
  cannot contest: they ride in a single run's projection, conflict-free
  by H2). No phantom events: an event enabled in the merge has its
  premises in one side ∪ M (its parent clique is mono-sided, since if
  it occurs in any class run it is a 𝒢-node under L4's argument), so
  it was enabled in that side's originating run and is already
  accounted for by that run's maximality — merges create no enablements
  neither side saw. By L1, the merged configuration extends (via L2′'s
  fibers) to class runs realizing exactly (α, β); maximality on each
  side gives exactly one An-projection. Draw-outcome consistency at M
  is the agreement hypothesis.

Assembling: by L2/L2′/L4, the mass of a class An-projection is
(Π A-side factors)(Π B-side factors); by L5 the sum over the class
splits per Lemma M2:

  μ([X=x][Y=y]C_z) = c_M · (Σ_{α : X=x} Π_A) · (Σ_{β : Y=y} Π_B)
                   = c_M · f(x) · g(y).                        ∎

**Corollary 1 (CI).** X ⊥ Y | z in the cross-product form (§2c). ∎

**Corollary 2 (sub-certificate masses).** f(x) = the mass of the
A-restricted class with X = x: the A∪M-projections are the runs of the
program restricted to the A-side rules and binders (L1 applied to the
A-side event structure), so the factors of the theorem are themselves
conditioned masses of the two sub-forests — computable, and certifiable,
by the same machinery. ∎

**Corollary 3 (exhibition).** For every r ∈ C_z the certificate's
events partition along (A ∪ M, B); the token zone splits
Θ = Θ_A ⊎ Θ_B (tokens are linear hypotheses of their draw events,
THY_0027), the endsequent's ⊗-partition realizes the split
(THY_0029 (ii)), and the fire provenances are side-pure (THY_0028
Thm 2b). Under S1–S3 the split is moreover in bijection with the
factor structure of the posterior products (Thm 1 there): the
certificate does not just permit the factorization, it displays it. ∎

## 6. The genericity converse (M6 — conjecture)

**Conjecture.** For generic parameters (priors and bias constants
algebraically independent over ℚ), an ACTIVE path between d_X and d_Y
given M implies X ⊥̸ Y | z, for some value pair — i.e. separation-
in-the-class-graph is complete up to a measure-zero parameter set.

Route (Meek 1995 transplanted): the CI defect
μ(x,y,z)μ(x′,y′,z) − μ(x,y′,z)μ(x′,y,z) is, on finite classes, a
polynomial in the parameters; an active path yields a witness
parameterization making it non-zero (pins 1–4 are four such witness
families: collider-conditioned, existence-mass, context-specific edge,
unblocked chain), so the defect polynomial is not identically zero and
generic parameters miss its zero set. The dynamic obligations: (i) a
witness construction per active-path SHAPE, including existence edges
and allocation forks (the pins cover the first three shapes); (ii) on
infinite classes the defect is a limit, and non-vanishing needs a
truncation argument (monotone lower approximants, T1). Left open;
theorem-or-remark per TODO_0302.

## 7. What this does not claim

- **Completeness.** Three independent failure sources: parameter
  cancellation (BN-classical), static-cover conservatism (§2e), and
  CSI-style context structure finer than the pruning predicate. The
  criterion refuses, it never asserts dependence.
- **Per-seed coupling.** Statements are about μ, never about the PRF:
  changing an X-side draw can change the PRF draws of separated waves
  in sample mode (keys are value-derived); the measure is unaffected.
- **Modelling honesty.** As in THY_0028: the theorem certifies that
  factor structure matches token structure; whether two tokens model
  independent worldly events remains the modeller's assertion, made
  inspectable.
- **Policy-order-sensitive bias.** A bias rule that needs another
  wave's GROUND value fires only after that wave's draw, so a policy
  that draws the biased wave first erases the factor — programs in
  this shape make the measure itself policy-sensitive. That is T1's
  standing scope boundary (the fixed-policy clause of §1, flagged at
  load by the C2 Hypothesis-S lint), inherited here, not created here:
  all statements are relative to the driver's policy, whose
  settle-to-quiescence-before-each-draw discipline is also what L2
  relies on for "every enabled bias fire has fired".
- **Normalized-conditional readings.** μ-CI is the restriction-
  semantics statement; the normalized conditional P(· | C_z) inherits
  it whenever 0 < μ(C_z) < ∞ (divide the cross-product identity), but
  existence-conditioning subtleties of normalized readings (comparing
  across classes with different μ(E_X)) are downstream bookkeeping,
  not part of the theorem.

## 8. Pins

`tests/engine/will-ci.test.js` (exact-mode masses, hand-verified,
division-free identities):

| pin | program shape | verdict pinned |
|---|---|---|
| 1 | two waves → one fire | marginal ⊥ (4 = 4); conditioning on the output breaks it (explaining away) |
| 2 | contingent wave, total 2 vs total 1 | bare existence leaks dependence iff total ≠ 1 (16 ≠ 4 vs 4 = 4) — mass-children forced |
| 2b | always-existing wave, dropped on the diagonal | drop leaks the same way (1·8 ≠ 4·4; normalized twin clean) — V_e hangs off the draw node (audit finding 1) |
| 3 | context-specific bias edge | dependence (12 ≠ 4) while every X=vb certificate shows no bias fire — class graph forced |
| 4 | spawn-order chain X → M → Y | blocked given M = m (80 = 80, 16 = 16); active marginally (168 ≠ 264) |
