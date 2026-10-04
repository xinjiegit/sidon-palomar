#!/usr/bin/env bash
set -euo pipefail
project_root=$(cd "$(dirname "$0")/.." && pwd)
cd "$project_root"
# Lake uses the committed lock file. Do not run `lake update` here: a
# dependency upgrade is a separate change requiring renewed verification.
python3 scripts/preflight.py
lake exe cache get
lake build
