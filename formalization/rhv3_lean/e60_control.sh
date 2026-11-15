#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/../.."

python3 - <<'PY'
import json
from pathlib import Path

p = Path("research/e60_singleton_center_off_collision_20260902/RESULTS.json")
d = json.loads(p.read_text())
off = d["off_mirror_control"]
stage = off["first_common_capture_stage_distribution"]
checks = {
    "E60_PAIR_COUNT": off["pair_count"],
    "E60_SAME_REFERENCE_PRIME_AT_FIRST_COMMON_CAPTURE":
        off["first_common_capture_both_cells_singleton_same_reference_prime"],
    "E60_DISTINCT_CONTACT_CELLS": off["first_common_capture_distinct_contact_cells"],
    "E60_STAGE1": stage["1"],
    "E60_STAGE2": stage["2"],
    "E60_PROOF_PREMISE": d["proof_premise"],
}
expected = {
    "E60_PAIR_COUNT": 75,
    "E60_SAME_REFERENCE_PRIME_AT_FIRST_COMMON_CAPTURE": 75,
    "E60_DISTINCT_CONTACT_CELLS": 75,
    "E60_STAGE1": 73,
    "E60_STAGE2": 2,
    "E60_PROOF_PREMISE": False,
}
for key, value in checks.items():
    print(f"{key}={str(value).lower() if isinstance(value, bool) else value}")
if checks != expected:
    raise SystemExit("E60_CONTROL_RESULT=FAIL")
print("E60_CONTROL_RESULT=PASS")
PY

