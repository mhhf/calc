#!/usr/bin/env bash
# hevm vs CALC 1:1 benchmark comparison
#
# Usage:
#   ./tools/hevm-bench.sh [options]
#
# Options:
#   --bin <file>       Hex bytecode file for hevm (default: multisig_nocall_solc.bin)
#   --ill <files...>   CALC .ill files (default: multisig_nocall_solc_symbolic.ill)
#   --sig <sig>        Solidity function signature for hevm (default: confirmAndCheck(uint256,uint256,bytes32))
#   --iterations <n>   Number of iterations (default: 5)
#   --hevm-only        Only run hevm
#   --calc-only        Only run CALC
#
# Requires: hevm, z3, solc (install via: nix shell nixpkgs#haskellPackages.hevm nixpkgs#z3 nixpkgs#solc)

set -euo pipefail

# Defaults
BIN_FILE="calculus/ill/programs/multisig_nocall_solc.bin"
ILL_FILE="calculus/ill/programs/multisig_nocall_solc_symbolic.ill"
SIG="confirmAndCheck(uint256,uint256,bytes32)"
ITERATIONS=5
RUN_HEVM=true
RUN_CALC=true

# Parse args
while [[ $# -gt 0 ]]; do
  case "$1" in
    --bin) BIN_FILE="$2"; shift 2 ;;
    --ill) ILL_FILE="$2"; shift 2 ;;
    --iterations) ITERATIONS="$2"; shift 2 ;;
    --hevm-only) RUN_CALC=false; shift ;;
    --calc-only) RUN_HEVM=false; shift ;;
    --sig) SIG="$2"; shift 2 ;;
    *) echo "Unknown option: $1"; exit 1 ;;
  esac
done

# Collect timing samples into an array, compute median
median() {
  local -a arr=("$@")
  local n=${#arr[@]}
  IFS=$'\n' sorted=($(sort -n <<<"${arr[*]}")); unset IFS
  echo "${sorted[$((n / 2))]}"
}

echo "=== hevm vs CALC 1:1 Benchmark ==="
echo "Iterations: $ITERATIONS"
echo

# --- CALC ---
if $RUN_CALC; then
  echo "--- CALC symexec ---"
  calc_times=()
  for i in $(seq 1 "$ITERATIONS"); do
    # Use node to run symexec and capture time + stats
    result=$(node -e "
      const mde = require('./lib/engine');
      const { explore } = require('./lib/engine/explore');
      const { getAllLeaves, countNodes, maxDepth } = require('./lib/engine/tree-utils');
      const path = require('path');
      (async () => {
        const calc = await mde.load(path.resolve('${ILL_FILE}'));
        const query = calc.queries.get('symex');
        const state = mde.decomposeQuery(query);
        const calcCtx = { clauses: calc.clauses, definitions: calc.definitions };
        const t0 = performance.now();
        const tree = explore(state, calc.forwardRules, { maxDepth: 500, calc: calcCtx, structuralMemo: true });
        const elapsed = performance.now() - t0;
        const leaves = getAllLeaves(tree);
        const nodes = countNodes(tree);
        const depth = maxDepth(tree);
        console.log(JSON.stringify({ elapsed: elapsed.toFixed(2), nodes, leaves: leaves.length, depth }));
      })();
    " 2>&1)
    elapsed=$(echo "$result" | jq -r '.elapsed')
    calc_times+=("$elapsed")
    if [ "$i" -eq 1 ]; then
      nodes=$(echo "$result" | jq -r '.nodes')
      leaves=$(echo "$result" | jq -r '.leaves')
      depth=$(echo "$result" | jq -r '.depth')
      echo "  Nodes: $nodes  Leaves: $leaves  Depth: $depth"
    fi
    echo "  Run $i: ${elapsed}ms"
  done
  calc_median=$(median "${calc_times[@]}")
  echo "  Median: ${calc_median}ms"
  echo
fi

# --- hevm ---
if $RUN_HEVM; then
  echo "--- hevm symbolic ---"
  if ! command -v hevm &>/dev/null; then
    echo "  hevm not found. Install via: nix shell nixpkgs#haskellPackages.hevm nixpkgs#z3"
    echo "  Skipping hevm benchmark."
  elif [ ! -f "$BIN_FILE" ]; then
    echo "  Bytecode file not found: $BIN_FILE"
    echo "  Generate with: node tools/bytecode-to-ill.js (or create .bin manually)"
    echo "  Skipping hevm benchmark."
  else
    BYTECODE=$(cat "$BIN_FILE" | tr -d '[:space:]')
    # Ensure 0x prefix
    if [[ ! "$BYTECODE" == 0x* ]]; then
      BYTECODE="0x${BYTECODE}"
    fi

    hevm_times=()
    for i in $(seq 1 "$ITERATIONS"); do
      t_start=$(date +%s%N)
      hevm symbolic --code "$BYTECODE" --sig "$SIG" --solver z3 2>/dev/null || true
      t_end=$(date +%s%N)
      elapsed_ns=$((t_end - t_start))
      elapsed_ms=$(echo "scale=2; $elapsed_ns / 1000000" | bc)
      hevm_times+=("$elapsed_ms")
      echo "  Run $i: ${elapsed_ms}ms"
    done
    hevm_median=$(median "${hevm_times[@]}")
    echo "  Median: ${hevm_median}ms"
    echo
  fi
fi

# --- Summary ---
echo "=== Summary ==="
if $RUN_CALC; then
  echo "CALC median:  ${calc_median}ms"
fi
if $RUN_HEVM && command -v hevm &>/dev/null && [ -f "$BIN_FILE" ]; then
  echo "hevm median:  ${hevm_median}ms"
  if $RUN_CALC; then
    ratio=$(echo "scale=1; $hevm_median / $calc_median" | bc 2>/dev/null || echo "N/A")
    echo "Ratio (hevm/CALC): ${ratio}x"
  fi
fi
