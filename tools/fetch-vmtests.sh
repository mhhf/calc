#!/usr/bin/env bash
# Fetch Ethereum VMTest fixtures (shallow sparse clone)
set -euo pipefail

DEST="${1:-tests/fixtures/vmtests}"

if [ -d "$DEST/Constantinople" ]; then
  echo "VMTest fixtures already present at $DEST"
  exit 0
fi

mkdir -p "$DEST"
cd "$DEST"

git init
git remote add origin git@github.com:ethereum/legacytests.git || true
git sparse-checkout init --cone
git sparse-checkout set Constantinople/VMTests
git pull --depth 1 origin master

echo "VMTest fixtures fetched to $DEST"
