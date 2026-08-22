#!/bin/bash
# Bootstrap for Claude Code on the web: venv + package, Docker daemon, Lean image.
# Idempotent; runs only in remote sessions. Local setups keep using scripts/setup.sh.
set -euo pipefail

if [ "${CLAUDE_CODE_REMOTE:-}" != "true" ]; then
  exit 0
fi
cd "$CLAUDE_PROJECT_DIR"

# 1. Python environment (harness package + dev extras for pytest)
if [ ! -x .venv/bin/python ]; then
  python3 -m venv .venv
fi
.venv/bin/python -m pip install --quiet --upgrade pip
.venv/bin/python -m pip install --quiet -e ".[dev]"

# 2. Docker daemon (the container image ships dockerd but does not start it)
if ! docker version >/dev/null 2>&1; then
  nohup dockerd --iptables=false --ip6tables=false > /tmp/dockerd.log 2>&1 &
  for _ in $(seq 1 60); do
    if docker version >/dev/null 2>&1; then break; fi
    sleep 1
  done
fi
docker version >/dev/null 2>&1 || { echo "dockerd failed to start (see /tmp/dockerd.log)" >&2; exit 1; }

# 3. Pinned Lean/Mathlib image (network policy must allow ghcr.io and
#    pkg-containers.githubusercontent.com; ~3.3 GB compressed, cached afterwards)
IMAGE=$(.venv/bin/python -c "from re_harness.config import HarnessSettings; print(HarnessSettings.from_env(n_workers=1).lean_image)")
if ! docker image inspect "$IMAGE" >/dev/null 2>&1; then
  docker pull "$IMAGE"
fi

echo "session bootstrap complete: venv ready, dockerd up, Lean image present"
