/**
 * Engine seam contracts (RES_0143 F5) — the TYPED side of the port
 * boundaries. Source stays plain JS (the Svelte route: JSDoc +
 * checkJs, no build step); these declarations give every injected
 * record a checkable shape and editor IntelliSense at the seams:
 *
 *   CalculusConfig  — the cc port (runtime contract: cc-schema.js —
 *                     keep the two in sync; the schema is the enforcer,
 *                     this is the shape)
 *   MatchOpts       — the frozen 21-field matcher protocol (match.js
 *                     factories are the single source of field truth)
 *   ComposePass     — the compose pool-pipeline pass record (F3)
 *   EngineContext   — the optimizer-built engine context (F2)
 *   FactSetPolicy   — the linear-zone index/label policy (M1)
 *   ApiAttacher     — post-construction api extension (F6)
 *
 * Checked via `npm run check:types` (tsconfig.engine.json — an
 * explicit, growing include list; adding a file to it is the F5
 * adoption path).
 */

/** A content-addressed term/formula hash (lib/kernel/store.js). */
export type Hash = number;

/** tag → declaration from the .calc connective table. */
export interface ConnectiveInfo {
  category: string;
  arity: number;
  polarity?: 'positive' | 'negative';
}

export interface LoaderConfig {
  /** Required — the engine holds no default parser. */
  buildParser: () => unknown;
  connTags?: {
    computation?: { tag: string; bodyIdx: number; gradeIdx: number | null };
    implication?: string;
    product?: string;
    exponential?: string;
    preserved?: string;
  };
  grade0?: () => Hash;
  timed?: boolean;
  qexprPreds?: string[];
}

export interface CompileConfig {
  getModes: ((pred: string) => string[] | null) | null;
  getModeMeta?: unknown;
  discriminatorPreds?: Array<string | {
    pred: string; arrayArg: number; indexArg: number; valueArg: number;
  }>;
  /** Required — caches are epoch-namespaced per calculus. */
  cacheEpoch: string;
  /** Optional default optimizer profile ('bare' | 'fast' | 'full'). */
  profile?: string;
}

export interface FamilyConfig {
  name: string;
  engine: {
    proveNaive: Function | null;
    matchDynamicRule: Function | null;
    drainDynamicRules: Function | null;
    resolveEx: Function | null;
  };
}

export interface GradeConfig {
  grade0: () => Hash;
  gradeOmega: () => Hash;
}

export interface DomainConfig {
  evalNumeric?: (h: Hash) => bigint | null;
  /** Which persistent predicates carry eq/neq constraint semantics (L3), plus
   * the order guards (predName → comparator) decided on ground tells (#84). */
  constraintPreds?: { eq: string; neq: string; order?: Record<string, string> };
  /** Unbounded-sum predicates (predName → output position) for the §6.1
   * guard-exclusivity certifier: `plus A B C` proves C = A+B exactly (#85).
   * SOUNDNESS OBLIGATION: ALL summands must be non-negative (ℕ≥0) — the
   * certifier injects `summandᵢ ≤ C`, which is FALSE on a signed or wrapping
   * domain. Declaring sumPreds therefore requires a non-negative
   * `orderDomain.min` (enforced warn-first by well-moded.js checkSumPreds). */
  sumPreds?: Record<string, number>;
  /** The scrutinee value domain for the §6.3 rep-point coverage decision (#86)
   * and the sumPreds obligation. `min` is the well-founded floor (BigInt;
   * absent = no floor); `discrete` asserts an integer-successor order — the
   * SOUNDNESS gate for order-guard coverage, which is exact only on a discrete
   * order (a dense/ℚ domain must omit it, so order guards stay undecidable). */
  orderDomain?: { min?: bigint; discrete?: boolean };
  /** Structural-memo control predicates [pcPred, stackPred?] (L5). */
  memoControlTags?: string[];
  classifyLeafPolicy?: { terminals: Record<string, string>; runningPred: string | null };
  showExclude?: readonly string[];
  loadBytecode?: (hex: string) => unknown;
  bytecodeArrGetGuard?: unknown;
  bytecodeToTrie?: (state: object) => object;
  codeToArrlit?: unknown;
  bytesToSemantic?: unknown;
  normalizeQuery?: unknown;
  trieNav?: unknown;
  lookupArrayValue?: (keyHash: Hash, arrayHash: Hash) => Hash | null;
}

/** The value algebra of a labelled (timed) state — THY_0024. */
export interface GradesConfig {
  values: object;
  aggregate?: { class: string };
  availability?: object;
  effect?: object;
  isStamp?: Function;
  parseStamp?: Function;
  parseExtent?: Function;
  canonStamp?: Function;
}

/** Linear-zone FactSet policy. A policy with `labels` MUST carry
 *  `stampTable` (the interning constructor, supplied by lib/timed —
 *  RES_0143 M1: fact-set imports no timed code). */
export interface FactSetPolicy {
  groupKey?: Function;
  cmp?: Function;
  labels?: object;
  stampTable?: new (alg: object) => object;
  stampTag?: string;
}

/** Post-construction api extension (F6): self-gated, returns a partial
 *  api record to merge, or null. */
export type ApiAttacher =
  (ctx: { api: object; cc: CalculusConfig; calc: object; sortSystem: object | null })
    => object | null;

/**
 * The cc PORT — everything the engine reads from a calculus.
 * Runtime enforcement: lib/engine/cc-schema.js (fail-fast at the
 * composition root). One entry per socket; absence semantics live in
 * the schema's `absent` docs.
 */
export interface CalculusConfig {
  connectives: Record<string, ConnectiveInfo>;
  loader: LoaderConfig;
  compile: CompileConfig;
  family?: FamilyConfig;
  init?: () => void;
  typeCheck?: 'strict';
  theories?: object[];
  gradeUnit?: () => Hash;
  gradeConfig?: GradeConfig;
  backward?: object;
  ffi?: object;
  compose?: {
    chainConfigs?: object[];
    sroaConfig?: object;
    linearFusionPredicate?: string;
    residualResolver?: Function;
  };
  domain?: DomainConfig;
  sorts?: object;
  datasortMasses?: object;
  grades?: GradesConfig;
  factSetPolicy?: FactSetPolicy;
  stampTag?: string;
  shiftOps?: object;
  scheduler?: object;
  lintExempt?: object;
  apiExtensions?: ApiAttacher[];
  /** well-modedness enforcement (task #81 / P7): 'strict' ⇒ load error on a
   *  violation; absent ⇒ warn-first (calc.wellModedLint). */
  wellModed?: 'strict';
  /** calculus-private composition helpers (never engine-read) */
  gradeRegistry?: object;
  gradeAlgebraFor?: Function;
}

/**
 * The frozen 21-field matcher protocol (match.js — the four protocol
 * factories buildGenericProtocol / buildFamilyProtocol /
 * buildOptProtocol / buildFfiProtocol are the single source of field
 * truth; every matchOpts has identical shape for V8 monomorphism).
 * Which layer may READ which field is enforced separately by the
 * layer-dag matchOpts field-access test.
 */
export interface MatchOpts {
  // ── generic layer (buildGenericProtocol) ──
  optimizePreserved: boolean;
  evidence: boolean;
  canonicalize: Function | null;
  onProveFail: Function | null;
  onProveSuccess: Function | null;
  /** Interface contract — never null (generic baseline: state lookup only). */
  provePersistent: Function;
  // ── family layer (buildFamilyProtocol) ──
  matchDynamicRule: Function | null;
  resolveEx: Function | null;
  drainDynamicRules: Function | null;
  connectives: object | null;
  dynamicRuleTag: string | null;
  backchainUseFFI: boolean;
  // ── opt layer (buildOptProtocol) ──
  execPS: Function | null;
  execExStep: Function | null;
  tryCCDispatch: Function | null;
  deltaBypass: Function | null;
  useCompiledSteps: boolean;
  // ── FFI context (buildFfiProtocol) ──
  ffiParsedModes: object | null;
  ffiMeta: object | null;
  ffiGet: Function | null;
  ffiIsGround: Function | null;
}

/** A compose pool-pipeline pass (F3). The driver owns gating, empty-
 *  pool skip, and phase profiling; a pass holds its transformation. */
export interface ComposePass {
  name: string;
  /** onPhase event name, or null for silent passes. */
  phase: string | null;
  enabled?: (ctx: ComposePassCtx) => boolean;
  run: (pool: object[], ctx: ComposePassCtx) => { pool: object[]; meta?: object };
  /** Append a silent residual-resolution pass after this one. */
  resolveAfter?: boolean;
}

export interface ComposePassCtx {
  rc: object;
  getModeMeta: unknown;
  residualResolver: Function | null;
  chainConfigs: object[] | null;
  linearFusionPredicate: string | null;
  fusionBarriers: object | null;
  sroaConfig: object | null;
  onPhase: Function | null;
  diagnostics: Record<string, unknown>;
}

/** The engine context (F2): the ONE channel through which rule-selection
 *  strategy reaches the run loops. */
export interface EngineContext {
  profile: Record<string, boolean | string>;
  /** Profile-honoring, per-rule-list memoized strategy factory. */
  buildStrategy: (ruleList: object[]) => StrategyStack;
}

export interface StrategyStack {
  getCandidateRules: (state: object) => object[];
  fpConfig: object | null;
}
