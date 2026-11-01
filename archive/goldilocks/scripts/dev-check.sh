#!/usr/bin/env bash
# Development checks only. The full gate remains the G-S3 check.
set -euo pipefail
cd "$(dirname "$0")/.."
python3 -B scripts/dev-check.py "$@"
