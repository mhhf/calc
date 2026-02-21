#!/usr/bin/env bash
# List all tags used across doc/ frontmatter, with frequency counts.
# Usage: ./tools/list-tags.sh [--freq] [--search PATTERN]
#   --freq     Sort by frequency (default: alphabetical)
#   --search   Filter tags matching PATTERN (case-insensitive)

set -euo pipefail

DIRS="doc/research doc/theory doc/def doc/todo doc/documentation"
MODE="alpha"
PATTERN=""

while [[ $# -gt 0 ]]; do
  case "$1" in
    --freq) MODE="freq"; shift ;;
    --search) PATTERN="$2"; shift 2 ;;
    *) echo "Usage: $0 [--freq] [--search PATTERN]"; exit 1 ;;
  esac
done

extract_tags() {
  for dir in $DIRS; do
    [ -d "$dir" ] || continue
    grep -rh '^tags:' "$dir" 2>/dev/null || true
  done | sed 's/tags: *\[//;s/\]//;s/, */\n/g' | sed 's/^ *//;s/ *$//' | grep -v '^$'
}

if [ -n "$PATTERN" ]; then
  if [ "$MODE" = "freq" ]; then
    extract_tags | sort -f | uniq -ci | sort -rn | grep -i "$PATTERN"
  else
    extract_tags | sort -fu | grep -i "$PATTERN"
  fi
else
  if [ "$MODE" = "freq" ]; then
    extract_tags | sort -f | uniq -ci | sort -rn
  else
    extract_tags | sort -fu
  fi
fi
