#!/usr/bin/env bash
# Deploy calc-web to hetzner.
#
# The symlink at /srv/apps/calc/current is what calc.service execs; flipping
# it atomically + restarting the service is the whole deploy. No pico-ci /
# auto-deploy hook exists for calc (unlike hq on um890), so this script is
# the only path that moves bits onto the server.
#
# Usage:
#   ./deploy.sh            # build, push, symlink, restart, healthcheck
#   SERVERS=hetzner ./deploy.sh
set -euo pipefail

APP_NAME="${APP_NAME:-calc}"
SERVERS="${SERVERS:-hetzner}"
SSH_USER="${SSH_USER:-mhhf}"
PORT="${PORT:-3100}"

VERSION="${1:-$(git describe --tags --always 2>/dev/null || echo "dev")}"
GIT_REV="$(git rev-parse HEAD)"
GIT_URL="$(git remote get-url origin 2>/dev/null || echo "local")"
DEPLOYED_AT="$(date -u +%Y-%m-%dT%H:%M:%SZ)"

if [[ -n "$(git status --porcelain 2>/dev/null)" ]]; then
  echo "WARN: working tree is dirty — deploying uncommitted state as v=$VERSION"
fi

echo "=== Deploying $APP_NAME v$VERSION (rev $GIT_REV) ==="
echo "Targets: $SERVERS"

echo
echo "Building .#web locally…"
STORE_PATH=$(nix build .#web --no-link --print-out-paths)
echo "Built: $STORE_PATH"

FAILED=""
for SERVER in $SERVERS; do
  echo
  echo "--- $SERVER ---"

  echo "Copying closure to $SSH_USER@$SERVER…"
  if ! nix copy "$STORE_PATH" --to "ssh://$SSH_USER@$SERVER" 2>&1; then
    echo "FAIL: nix copy to $SERVER"
    FAILED="$FAILED $SERVER"
    continue
  fi

  echo "Flipping /srv/apps/$APP_NAME/current → $STORE_PATH"
  ssh "$SSH_USER@$SERVER" "sudo ln -sfn '$STORE_PATH' /srv/apps/$APP_NAME/current"

  echo "Writing manifest…"
  ssh "$SSH_USER@$SERVER" "sudo tee /srv/apps/$APP_NAME/manifest.json >/dev/null" <<EOF
{
  "schema_version": 1,
  "name": "$APP_NAME",
  "version": "$VERSION",
  "git_rev": "$GIT_REV",
  "git_url": "$GIT_URL",
  "store_path": "$STORE_PATH",
  "deployed_at": "$DEPLOYED_AT",
  "deployed_by": "${USER:-manual}"
}
EOF

  echo "Restarting $APP_NAME.service…"
  ssh "$SSH_USER@$SERVER" "sudo systemctl restart $APP_NAME"

  echo "Health check on :$PORT…"
  sleep 2
  if ssh "$SSH_USER@$SERVER" "curl -sf http://localhost:$PORT/api/health >/dev/null"; then
    echo "OK: $SERVER healthy"
  else
    echo "WARN: $SERVER health check failed"
    ssh "$SSH_USER@$SERVER" "sudo journalctl -u $APP_NAME -n 20 --no-pager" || true
  fi
done

echo
if [[ -z "$FAILED" ]]; then
  echo "OK: deployed $APP_NAME v$VERSION to$([ -z "$SERVERS" ] && echo " (none)" || echo " $SERVERS")"
  echo "    store: $STORE_PATH"
  exit 0
else
  echo "FAIL: deploy failed for:$FAILED"
  exit 1
fi
