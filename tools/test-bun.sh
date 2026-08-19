#!/usr/bin/env bash
# Per-file bun test runner.
#
# Bun runs all test files in a single process, which leaks module-scope state
# (Store arena, _exprParser, etc.) across files. Per-file invocation matches
# node --test's file-isolation model. See TODO_0219 Phase 3.
set -uo pipefail
cd "$(dirname "$0")/.."

BUN="${BUN:-bun}"
PARALLEL="${PARALLEL:-8}"

# Extract the same file list that `npm test` uses.
FILES=$(node -e "
import('./package.json', { with: { type: 'json' } }).then(m => {
  const mt = m.default.scripts.test.match(/--test\s+(.+)\$/);
  console.log(mt[1].split(/\s+/).filter(f => f.endsWith('.js')).map(f => './' + f).join('\n'));
});
")

export BUN
results=$(mktemp)
trap 'rm -f "$results"' EXIT

# --timeout 30000: bun's default 5s per-test timeout flakes on perf-heavy
# tests (vmPerformance/fibonacci16 ~9.5s under machine load, round-13 note);
# node --test has no such default, so this only aligns the runners.
echo "$FILES" | xargs -P "$PARALLEL" -I {} bash -c '
  out=$("$BUN" test --timeout 30000 "$1" 2>&1)
  if echo "$out" | tail -3 | grep -q " 0 fail"; then
    echo "OK $1"
  else
    printf "FAIL %s\n%s\n---\n" "$1" "$out"
  fi
' _ {} > "$results"

pass=$(grep -c "^OK " "$results" || true)
fail=$(grep -c "^FAIL " "$results" || true)

echo "===================="
echo "bun test per-file: $pass pass / $fail fail"
if [ "$fail" -gt 0 ]; then
  echo ""
  grep "^FAIL " "$results"
  echo ""
  echo "Full failure output:"
  awk '/^FAIL /,/^---$/' "$results"
  exit 1
fi
