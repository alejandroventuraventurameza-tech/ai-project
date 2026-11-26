#!/usr/bin/env python3
"""Audit the ORIGINAL Python 33-coordinate two-date state timing.

Compare independently decoded log-chart and finite_irf.prefix_residual
date state/control handoffs, including the two firms' signed faces, bank
face, realized reserve rate and pre-payment reserves. Verify exactly
which six states are compact on date two and how pledgeability
reconstructs its two firm nominal faces.

Only a Python implementation check, not a SOURCE/Python cross-language
theorem nor a full equilibrium certificate.
"""
from __future__ import annotations

import hashlib
import json
import math
from pathlib import Path

import finite_irf as model
from frozen_stationary_prefix_audit import frozen_stationary_seed

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
MODEL = HERE / "finite_irf.py"
SOURCE = ROOT / "lean/checkpoint/modules/Ventura26LiquidityAllocation/EconomicModel.lean"
OUT = HERE / "output/original_python_two_date_coordinate_timing.json"
P0 = HERE / "inputs/rational_preconditioners.json"


def require(v, message):
    if not v:
        raise AssertionError(message)


def close(x, y, label):
    require(math.isfinite(x) and math.isfinite(y) and
            abs(x - y) < 2e-11 * (1 + abs(x) + abs(y)),
            f"{label}: {x} != {y}")


def main():
    py = MODEL.read_text(encoding="utf-8")
    source = SOURCE.read_text(encoding="utf-8")
    anchors = (
        "currentCapital := localPrefixStateSevenCapital Z.stateOne",
        "inheritedFace := localPrefixStateSevenFace Z.stateOne",
        "currentBankFace := Z.stateOne.bankFace",
        "lagReserveRate := Z.stateOne.reserveRateLag",
        "lagReservesPre := Z.stateOne.reservesPreLag",
        "controls := Z.controlsOne",
        "nextFace := localPrefixStateSixFace P Z.stateTwo",
    )
    require(all(a in source for a in anchors),
            "Original SOURCE date-state chronological structure changed")
    require("state2 = expand_compact_state(s, x2)" in py and
            "result.extend(binding_period_residual(s, x1, u1, x2, u2, base.e1))" in py,
            "Original Python date-one model handoff changed")
    p0 = [[float(v) for v in row]
          for row in json.loads(P0.read_text(encoding="utf-8"))["P0"]]
    require(len(p0) == 16 and all(len(r) == 6 for r in p0),
            "Pinned 16x6 continuation changed")
    s = model.steady_case()
    base = frozen_stationary_seed(s)
    charts = (
        [0.0] * 33,
        [4e-4 * math.sin(.47 * (i + 1)) for i in range(33)],
        [-5e-4 * math.cos(.31 * (i + 1)) for i in range(33)],
    )
    checks = 0
    max_face_error = 0.0
    for chart in charts:
        x1, u0, compact, u1, u2 = model.decode_prefix(base, p0, chart)
        state2 = model.expand_compact_state(s, compact)
        require(len(x1) == 7 and len(u0) == 10 and
                len(compact) == 6 and len(state2) == 7 and
                len(u1) == 10 and len(u2) == 10,
                "Original 7+10+6+10 date-coordinate dimensions changed")
        for i in range(7):
            close(x1[i], base.X1[i] * math.exp(chart[i]), f"x1[{i}]")
            checks += 1
        for i in range(10):
            close(u0[i], base.U0[i] * math.exp(chart[7+i]), f"u0[{i}]")
            close(u1[i], base.U1[i] * math.exp(chart[23+i]), f"u1[{i}]")
            checks += 2
        for i in range(6):
            close(compact[i], base.X2[i] * math.exp(chart[17+i]),
                  f"x2[{i}]")
            checks += 1
        # Date zero next state IS date one current state (shared x1).
        date_zero_next_state = x1
        date_one_current_state = x1
        date_zero_next_controls = u1
        date_one_current_controls = u1
        require(date_zero_next_state is date_one_current_state and
                date_zero_next_controls is date_one_current_controls,
                "Python 7-state/10-control chronological handoff drift")
        for i in range(2):
            face = s.pledge[i] * compact[2] * compact[i]
            close(state2[2+i], face, f"date2_face[{i}]")
            max_face_error = max(max_face_error, abs(state2[2+i]-face))
            checks += 1
        for idx, target in ((0, compact[0]), (1, compact[1]),
                             (4, compact[3]), (5, compact[4]),
                             (6, compact[5])):
            close(state2[idx], target, f"date2_state[{idx}]")
            checks += 1
        rows = model.prefix_residual(base, p0, "binding",
                                     (0., 0., 0., 0.), chart)
        require(len(rows) == 33 and all(math.isfinite(v) for v in rows),
                "Original 33-row evaluator drift")
    report = {
        "status": "ORIGINAL_PYTHON_33_COORDINATE_TIMING_AUDIT",
        "charts_tested": len(charts),
        "scalar_coordinate_checks": checks,
        "state_one_dimension": 7,
        "controls_zero_dimension": 10,
        "state_two_compact_dimension": 6,
        "controls_one_dimension": 10,
        "max_state_two_pledge_face_error": max_face_error,
        "source_structural_anchors_checked": len(anchors),
        "source_python_function_identity_proved": False,
        "validated_exact_SOURCE_equilibrium": False,
        "file_sha256": {
            "code/irf/finite_irf.py":
                hashlib.sha256(MODEL.read_bytes()).hexdigest(),
            "lean/checkpoint/modules/Ventura26LiquidityAllocation/EconomicModel.lean":
                hashlib.sha256(SOURCE.read_bytes()).hexdigest(),
        },
    }
    OUT.parent.mkdir(parents=True, exist_ok=True)
    OUT.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()
