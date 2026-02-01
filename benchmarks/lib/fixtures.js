/**
 * Benchmark Fixtures - Test formulas for benchmarking
 */

// Simple proofs (should be very fast)
const simple = {
  identity: '-- : A |- -- : A',
  identity_var: '-- : F?X |- -- : F?X',
  modus_ponens: '-- : P, -- : P -o Q |- -- : Q',
};

// Medium complexity proofs
const medium = {
  tensor_id: '-- : P * Q |- -- : P * Q',
  tensor_comm: '-- : P * Q |- -- : Q * P',
  tensor_assoc: '-- : (A * B) * C |- -- : A * (B * C)',
  with_elim_l: '-- : A & B |- -- : A',
  with_elim_r: '-- : A & B |- -- : B',
  with_intro: '-- : A |- -- : A & A',
  currying: '-- : (A * B) -o C |- -- : A -o (B -o C)',
  uncurrying: '-- : A -o (B -o C) |- -- : (A * B) -o C',
};

// Complex proofs (more branching, deeper)
const complex = {
  distribution: '-- : P -o (R & Q) |- -- : (P -o Q) & (P -o R)',
  tensor_with: '-- : (A & B) * (C & D) |- -- : (A * C) & (B * D)',
  deep_loli: '-- : A -o (B -o (C -o D)) |- -- : ((A * B) * C) -o D',
  nested_with: '-- : (A & B) & (C & D) |- -- : A & D',
};

// Stress tests (high branching, many choices)
const stress = {
  many_tensor: '-- : A * B * C * D |- -- : D * C * B * A',
  deep_tensor: '-- : ((((A * B) * C) * D) * E) |- -- : A * (B * (C * (D * E)))',
  many_with: '-- : A & B & C & D |- -- : A & D',
};

// All formulas combined
const all = { ...simple, ...medium, ...complex, ...stress };

module.exports = {
  simple,
  medium,
  complex,
  stress,
  all,
};
