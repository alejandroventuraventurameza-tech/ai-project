#!/usr/bin/env python3
"""Verify all 33 SOURCE labels, the Lean permutation and Python row order.

This is an executable CROSS-LANGUAGE ROW-LABEL/INDEX contract, not a
proof of equality of the corresponding economic equations or Jacobians.
"""
from __future__ import annotations

import hashlib
import json
import re
from pathlib import Path

import finite_irf as py
from audit_frozen_33_offroot_nonlinear_transform import SOURCE_TO_PY

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
ECON = ROOT / "lean/checkpoint/modules/Ventura26LiquidityAllocation/EconomicModel.lean"
INDEX_LEAN = ROOT / "lean/candidates/Ventura26LiquidityAllocation/SourcePython33RowIndexPermutationCandidate.lean"
OUT = HERE / "output/source_python_33_row_index_contract.json"
N = 33


def require(ok, msg):
    if not ok:
        raise AssertionError(msg)


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def parse_source_labels(source):
    a = source.index("def localPrefixEquationOfIndex : Fin 33")
    b = source.index("noncomputable def localReducedPrefixResidualVector", a)
    matches = re.findall(
        r"^\s*\|\s*(\d+)\s*=>\s*\.(\w+)\s*$",
        source[a:b], re.M,
    )
    require(len(matches) == N, "The original Lean SOURCE row enumeration drifted")
    result = {int(i):name for i,name in matches}
    require(set(result) == set(range(N)) and len(set(result.values())) == N,
            "Missing, repeated, or duplicate economic SOURCE row label")
    return result


def parse_lean_permutation(s, function_name, variable, next_name):
    a = s.index("def " + function_name)
    b = s.index(next_name, a + 1)
    block = s[a:b]
    pairs = [
        (int(i), int(j)) for i,j in re.findall(
            r"if\s+" + variable + r"\s*=\s*(\d+)\s+then\s+(\d+)",
            block,
        )
    ]
    require(len(pairs) == 6 and len({i for i,_ in pairs}) == 6,
            "Expected six exact nonidentity row permutations in " + function_name)
    require(all(0 <= i < N and 0 <= j < N for i,j in pairs),
            "Lean row indices out of Fin 33")
    change = dict(pairs)
    return {i:change.get(i,i) for i in range(N)}


def canonical_python_name(source_label):
    m = re.fullmatch(r"(.+?)(Zero|One)(H|L)?", source_label)
    require(m is not None, "Unrecognized SOURCE economic row " + source_label)
    stem = re.sub(r"([a-z])([A-Z])", r"\1_\2", m.group(1)).lower()
    date = "0" if m.group(2) == "Zero" else "1"
    firm = "_"+m.group(3) if m.group(3) else ""
    return stem+"_"+date+firm


def main():
    source = ECON.read_text(encoding="utf-8")
    lean = INDEX_LEAN.read_text(encoding="utf-8")
    labels = parse_source_labels(source)
    expected_py = {int(k):int(v) for k,v in SOURCE_TO_PY.items()}
    stp = parse_lean_permutation(
        lean, "sourceToPython33Index", "i",
        "/-- Explicit Python index",
    )
    pts = parse_lean_permutation(
        lean, "pythonToSource33Index", "j",
        "theorem pythonToSource33_sourceToPython33",
    )
    require(stp == expected_py, "Lean and Python 33-row permutations differ")
    require(sorted(stp.values()) == list(range(N)), "Row permutation not bijective")
    require(all(pts[stp[i]] == i for i in range(N))
            and all(stp[pts[j]] == j for j in range(N)),
            "Lean index inverse not matched by Python mirror")
    require(len(py.PREFIX_ROW_NAMES) == N,
            "Original Python residual row labels have changed")

    proof_table = []
    for i in range(N):
        j = stp[i]
        expected_name = canonical_python_name(labels[i])
        actual_name = py.PREFIX_ROW_NAMES[j]
        require(expected_name == actual_name,
                "Original economic SOURCE row-label mismatch at source "
                + str(i) + " / Python " + str(j)
                + ": " + expected_name + " != " + actual_name)
        proof_table.append({
            "source_index":i,
            "python_index":j,
            "source_equation":labels[i],
            "python_equation":actual_name,
        })

    report = {
        "status":"ALL_33_SOURCE_PYTHON_ROW_LABELS_AND_INDICES_MATCH",
        "source_economic_model_sha256":sha(ECON),
        "lean_permutation_candidate_sha256":sha(INDEX_LEAN),
        "python_engine_sha256":sha(HERE/"finite_irf.py"),
        "row_count":N,
        "nonidentity_index_moves":{str(i):stp[i] for i in range(N) if stp[i]!=i},
        "source_to_python_rows":proof_table,
        "matched_count":len(proof_table),
        "lean_permutation_kernel_verified":False,
        "cross_language_economic_functional_equivalence_proved":False,
        "true_SOURCE_jacobian_certified":False,
        "full_competitive_equilibrium_proved":False,
        "scope_note":"Checks source labels, numeric indices and 33-row bijection only, not mathematical residual equality.",
    }
    OUT.parent.mkdir(parents=True,exist_ok=True)
    OUT.write_text(json.dumps(report,indent=2,sort_keys=True)+"\n",
                   encoding="utf-8")
    print(json.dumps({
        "status":report["status"],
        "matched_count":report["matched_count"],
        "nonidentity_index_moves":report["nonidentity_index_moves"],
        "report":str(OUT),
    },indent=2))


if __name__=="__main__":
    main()
