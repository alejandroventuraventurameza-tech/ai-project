#!/usr/bin/env python3
"""At the FIXED-predecessor Python 34-boundary, audit 33 SOURCE-shaped rows.

A proposed invertible left row transform T must link the independent
SOURCE-shaped Python transcriptions to finite_irf.prefix_residual.
At a common root the 33 Jacobian rows satisfy J_python = T * J_source_shape
because terms differentiating T are multiplied by zero residuals.
We check this numerically at the actual h* frontier and compare it
with independent forward-mode AD of the original Python residual.

No line executes EconomicModel.lean or proves SOURCE/Python equivalence.
"""
from __future__ import annotations

import hashlib
import json
import math
from pathlib import Path

import finite_irf as engine
from frozen_stationary_prefix_audit import frozen_stationary_seed
from audit_frozen_33_offroot_nonlinear_transform import (
    build_source_shaped, nonlinear_pullback, SOURCE_TO_PY,
    SOURCE_INDICES, SHEAR,
)

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
SOURCE = ROOT / "lean/checkpoint/modules/Ventura26LiquidityAllocation/EconomicModel.lean"
ENGINE = HERE / "finite_irf.py"
PRE = HERE / "inputs/rational_preconditioners.json"
FRONTIER = HERE / "output/frozen_python_augmented34_boundary_search.json"
FORWARD_AD = HERE / "output/frozen_python_augmented34_forward_ad.json"
OUT = HERE / "output/frozen_python_frontier_source_shaped_row_transport.json"
N = 33
FULL = 34


def require(test, message):
    if not test:
        raise AssertionError(message)


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def candidate_rows(base, p0, w):
    assert len(w) == FULL
    shock = (w[N], 0., 0., 0.)
    src, _, _, _, _ = build_source_shaped(base, p0, w[:N], "binding", shock)
    return [src[k] for k in range(N)]


def root_transform(base, p0, z, h):
    shock = (h, 0., 0., 0.)
    src, scalar, coeff, _shear, _g = build_source_shaped(
        base, p0, z, "binding", shock
    )
    T = [[0.] * N for _ in range(N)]
    pledge_i = 21
    pledge_denom = scalar[pledge_i][2]
    require(pledge_denom > 0,
            "Nonpositive common-pledge scalar source normalization")
    for i in range(N):
        py_idx = SOURCE_TO_PY[i]
        if i in SOURCE_INDICES:
            _level, _logged, denom, sign = scalar[i]
            require(denom > 0 and sign in (-1,1),
                    "Non-positive scalar normalized SOURCE row")
            T[py_idx][i] = sign/denom
        elif i in SHEAR:
            T[py_idx][i] = 1.
            T[py_idx][pledge_i] = -coeff[i]/pledge_denom
        else:
            T[py_idx][i] = 1.
    return T, src, scalar, coeff


def dense_left_product(T, J):
    n = len(T)
    m = len(J[0])
    return [[sum(T[i][k]*J[k][j] for k in range(n))
             for j in range(m)] for i in range(n)]


def inverse_diagnostic(T):
    n = len(T)
    cols=[]
    pivot=float("inf")
    for j in range(n):
        rhs = [float(i == j) for i in range(n)]
        col, pivots = engine.solve_linear(T, rhs)
        cols.append(col)
        pivot = min(pivot, *pivots)
    Ti = [[cols[j][i] for j in range(n)] for i in range(n)]
    err_left=max(abs(sum(Ti[i][k]*T[k][j] for k in range(n))
                     - float(i==j)) for i in range(n) for j in range(n))
    err_right=max(abs(sum(T[i][k]*Ti[k][j] for k in range(n))
                      - float(i==j)) for i in range(n) for j in range(n))
    return pivot, err_left, err_right


def main():
    require(FRONTIER.is_file() and FORWARD_AD.is_file(),
            "Regenerate the boundary and original-Python AD reports")
    data=json.loads(FRONTIER.read_text(encoding="utf-8"))
    ad=json.loads(FORWARD_AD.read_text(encoding="utf-8"))
    require(data["status"] ==
            "NUMERICAL_PYTHON_34_BOUNDARY_CANDIDATE_FOUND_NOT_SOURCE_PROOF"
            and ad["status"] ==
            "FLOAT64_FORWARD_AD_PYTHON_34_JACOBIAN_NOT_SOURCE",
            "Invalid source-shaped comparison inputs")
    require(ad["parent_boundary_report_sha256"] == sha(FRONTIER)
            and data["source_sha256"] == sha(SOURCE)
            and data["python_engine_sha256"] == sha(ENGINE),
            "Source, numerical frontier, and original-Python AD not pinned")
    c = data["numerical_candidate"]
    z, h = c["baseline_33_unknowns"], c["innovation_h"]
    require(len(z) == N and c["max_34_residual"] < 1e-9,
            "No 34-row candidate root")
    payload=json.loads(PRE.read_text(encoding="utf-8"))
    p0=[[float(t) for t in row] for row in payload["P0"]]
    require(len(p0)==16 and all(len(row)==6 for row in p0),
            "Incorrect tail dimension")
    base=frozen_stationary_seed(engine.steady_case())
    frozen=tuple(base.X0)
    T, src, scalar, coeff = root_transform(base,p0,z,h)
    pulled=nonlinear_pullback(src,scalar,coeff)
    original=engine.prefix_residual(base,p0,"binding",(h,0.,0.,0.),z)
    functional_error=max(abs(a-b) for a,b in zip(pulled,original))
    # src is a dictionary indexed by SOURCE equation number. Iterate
    # its VALUES: iterating the dictionary itself returns indices 0..32
    # and incorrectly reports a maximum raw residual of exactly 32.
    root_src=max(abs(v) for v in src.values())
    root_normalized=max(abs(v) for v in pulled)
    worst_raw=sorted((
        {"source_row":i, "python_row":SOURCE_TO_PY[i],
         "raw_residual":src[i],
         "absolute_raw_residual":abs(src[i]),
         "scalar_denominator":scalar[i][2] if i in SOURCE_INDICES else None}
        for i in range(N)),
        key=lambda row:row["absolute_raw_residual"], reverse=True)[:5]
    require(functional_error < 1e-8,
            "Transcription and Python rows disagree at h*")
    require(root_normalized < 1e-8,
            "Normalized SOURCE-shaped candidate is not a numerical root")
    require(root_src < 1e-8,
            "Raw SOURCE-shaped residual is not a numerical root")
    require(abs(root_src - max(row["absolute_raw_residual"]
                            for row in worst_raw)) < 1e-30,
            "Source-shaped residual report disagrees with the raw values")

    # Test the NONLINEAR residual transformation off root in a local
    # 34-dimensional neighborhood, not merely at h*. The exact root-only
    # row matrix T is NOT used away from the root: the nonlinear
    # logarithms and endogenous pledge/Euler shears are recomputed.
    # This remains a float64 Python-transcription test, not a proof
    # that the Lean SOURCE operator equals the Python implementation.
    local_radius = 8e-5
    probes = []
    for index in range(FULL):
        for direction in (-1., 1.):
            trial_z = list(z)
            trial_h = h
            if index == N:
                trial_h += direction * local_radius
            else:
                trial_z[index] += direction * local_radius
            probes.append((trial_z, trial_h))
    probes.append((
        [z[k] + local_radius * math.sin(0.63*(k+1)) for k in range(N)],
        h + 0.5*local_radius,
    ))
    probes.append((
        [z[k] - local_radius * math.cos(0.49*(k+1)) for k in range(N)],
        h - 0.5*local_radius,
    ))
    max_neighborhood_functional_error = 0.
    max_neighborhood_raw_residual = 0.
    for trial_z, trial_h in probes:
        shaped, local_scalar, local_coeff, _shear, _g = build_source_shaped(
            base, p0, trial_z, "binding", (trial_h, 0., 0., 0.)
        )
        reconstructed = nonlinear_pullback(
            shaped, local_scalar, local_coeff
        )
        original_probe = engine.prefix_residual(
            base, p0, "binding", (trial_h, 0., 0., 0.), trial_z
        )
        max_neighborhood_functional_error = max(
            max_neighborhood_functional_error,
            max(abs(x-y) for x,y in zip(reconstructed, original_probe))
        )
        max_neighborhood_raw_residual = max(
            max_neighborhood_raw_residual,
            max(abs(v) for v in shaped.values())
        )
        require(tuple(base.X0) == frozen,
                "Inherited nominal state drifted during neighborhood audit")
    require(max_neighborhood_functional_error < 5e-8,
            "Nonlinear SOURCE-shaped/Python row transform fails near the frontier")

    w = list(z)+[h]
    S = engine.numerical_jacobian(
        lambda v: candidate_rows(base,p0,v), w, step=2e-6)
    require(len(S)==N and all(len(row)==FULL for row in S),
            "Wrong SOURCE-shaped candidate derivative dimensions")
    transported = dense_left_product(T,S)
    actual_ad=ad["forward_ad_jacobian_34"]
    err=max(abs(transported[i][j]-actual_ad[i][j])
            for i in range(N) for j in range(FULL))
    errA=max(abs(transported[i][j]-actual_ad[i][j])
             for i in range(N) for j in range(N))
    errb=max(abs(transported[i][N]-actual_ad[i][N])
             for i in range(N))
    pivot,left,right=inverse_diagnostic(T)
    require(math.isfinite(err) and err < 3e-5,
            "ROOT-only SOURCE-shaped row transform derivative mismatch")
    require(pivot > 1e-12 and max(left,right)<1e-7,
            "Proposed frontier row transform not numerically invertible")
    require(tuple(base.X0)==frozen,"Inherited predecessor changed")

    report={
        "status":"NUMERICAL_SOURCE_SHAPED_FRONTIER_ROW_TRANSPORT_NOT_LEAN_SOURCE",
        "scope":"same inherited X0, same log coordinates, same h*, binding branch",
        "source_sha256":sha(SOURCE),
        "python_engine_sha256":sha(ENGINE),
        "pinned_tail_sha256":sha(PRE),
        "frontier_report_sha256":sha(FRONTIER),
        "forward_ad_report_sha256":sha(FORWARD_AD),
        "innovation_h":h,
        "root_source_shaped_max_abs":root_src,
        "root_reconstructed_normalized_max_abs":root_normalized,
        "largest_unscaled_source_shaped_residuals":worst_raw,
        "max_reconstructed_functional_error":functional_error,
        "nonlinear_offroot_34_dimension_probe_count":len(probes),
        "nonlinear_offroot_log_radius":local_radius,
        "nonlinear_offroot_max_original_vs_transformed_Python_error":
            max_neighborhood_functional_error,
        "nonlinear_offroot_max_raw_source_shaped_residual":
            max_neighborhood_raw_residual,
        "offroot_row_transform_recomputed_at_each_probe":True,
        "source_to_python_indices":{str(i):SOURCE_TO_PY[i] for i in range(N)},
        "source_to_python_row_transform_T":T,
        "source_shape_jacobian_33_by_34":S,
        "transported_33_by_34_jacobian":transported,
        "max_derivative_error_vs_original_Python_AD":err,
        "max_33_block_error_vs_original_Python_AD":errA,
        "max_policy_forcing_error_vs_original_Python_AD":errb,
        "T_float_min_pivot":pivot,
        "max_T_inverse_left_error":left,
        "max_T_inverse_right_error":right,
        "original_lean_SOURCE_operator_evaluated":False,
        "original_SOURCE_row_transformation_proved":False,
        "true_SOURCE_Jacobian_enclosed":False,
        "IFT_root_certified":False,
        "full_competitive_equilibrium_proved":False,
    }
    OUT.parent.mkdir(parents=True,exist_ok=True)
    OUT.write_text(json.dumps(report,indent=2,sort_keys=True)+"\n",encoding="utf-8")
    print(json.dumps({k:report[k] for k in (
        "status","innovation_h","root_source_shaped_max_abs","root_reconstructed_normalized_max_abs",
        "max_reconstructed_functional_error",
        "nonlinear_offroot_34_dimension_probe_count",
        "nonlinear_offroot_max_original_vs_transformed_Python_error",
        "max_derivative_error_vs_original_Python_AD",
        "max_33_block_error_vs_original_Python_AD",
        "max_policy_forcing_error_vs_original_Python_AD",
        "T_float_min_pivot", "max_T_inverse_left_error",
        "max_T_inverse_right_error",
    )},indent=2))


if __name__=="__main__":
    main()
