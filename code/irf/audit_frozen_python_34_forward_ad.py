#!/usr/bin/env python3
"""Differentiate the original Python 33-row frozen-prefix map by forward AD.

This differentiates the actual finite_irf.prefix_residual implementation, not
a handwritten row-by-row derivative. The extra row is independently assembled
from the genuine SOURCE-shaped L dual formula (CRRA sigma_E=1 at illustration).
The result is a float64 forward-mode differential, NOT a directed interval
enclosure or an evaluation of EconomicModel.lean.
"""
from __future__ import annotations

import hashlib
import json
import math
from pathlib import Path

import finite_irf as engine
from frozen_stationary_prefix_audit import frozen_stationary_seed

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
INPUT = HERE / "output/frozen_python_augmented34_boundary_search.json"
OUT = HERE / "output/frozen_python_augmented34_forward_ad.json"
SOURCE = ROOT / "lean/checkpoint/modules/Ventura26LiquidityAllocation/EconomicModel.lean"
PYTHON = HERE / "finite_irf.py"
PRE = HERE / "inputs/rational_preconditioners.json"
DIM = 34
N = 33


def require(condition, message):
    if not condition:
        raise AssertionError(message)


def fingerprint(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


class Dual:
    __slots__ = ("value", "grad")

    def __init__(self, value, grad):
        self.value = float(value)
        self.grad = tuple(float(t) for t in grad)
        require(len(self.grad) == DIM and math.isfinite(self.value)
                and all(math.isfinite(t) for t in self.grad),
                "Invalid forward-mode dual number")

    @staticmethod
    def basis(x, index):
        grad = [0.0] * DIM
        grad[index] = 1.0
        return Dual(x, grad)

    @staticmethod
    def coerce(x):
        return x if isinstance(x, Dual) else Dual(x, (0.0,) * DIM)

    def __add__(self, other):
        other = Dual.coerce(other)
        return Dual(self.value + other.value,
                    (a+b for a,b in zip(self.grad, other.grad)))

    __radd__ = __add__

    def __neg__(self):
        return Dual(-self.value, (-a for a in self.grad))

    def __sub__(self, other):
        return self + (-Dual.coerce(other))

    def __rsub__(self, other):
        return Dual.coerce(other) - self

    def __mul__(self, other):
        other = Dual.coerce(other)
        return Dual(self.value * other.value,
                    (a*other.value + b*self.value
                     for a,b in zip(self.grad, other.grad)))

    __rmul__ = __mul__

    def __truediv__(self, other):
        other = Dual.coerce(other)
        require(other.value != 0, "Division by zero in dual arithmetic")
        d = other.value
        return Dual(self.value / d,
                    ((a*d-self.value*b)/(d*d)
                     for a,b in zip(self.grad, other.grad)))

    def __rtruediv__(self, other):
        return Dual.coerce(other) / self

    def __pow__(self, power):
        if isinstance(power, Dual):
            return (power*self.log()).exp()
        if power == 0:
            return Dual(1.0, (0.0,) * DIM)
        if self.value <= 0:
            require(isinstance(power, (int,float))
                    and float(power).is_integer()
                    and (self.value != 0 or power > 0),
                    "Noninteger power outside smooth positive domain")
        value = self.value ** power
        derivative = power * self.value ** (power-1)
        return Dual(value, (derivative*a for a in self.grad))

    def __rpow__(self, base):
        require(base > 0, "Exponential positive base required")
        return (self * math.log(base)).exp()

    def log(self):
        require(self.value > 0, "Log outside positive domain")
        return Dual(math.log(self.value),
                    (a/self.value for a in self.grad))

    def exp(self):
        value = math.exp(self.value)
        return Dual(value, (value*a for a in self.grad))

    def sqrt(self):
        require(self.value > 0, "Square root derivative outside positive domain")
        root = math.sqrt(self.value)
        return Dual(root, (a/(2*root) for a in self.grad))


class DualMathProxy:
    """Change only exp/log/sqrt in finite_irf; every other math operation
    remains the actual standard-library implementation."""
    def exp(self, value):
        return value.exp() if isinstance(value, Dual) else math.exp(value)

    def log(self, value, base=None):
        if base is not None:
            return self.log(value) / self.log(base)
        return value.log() if isinstance(value, Dual) else math.log(value)

    def sqrt(self, value):
        return value.sqrt() if isinstance(value, Dual) else math.sqrt(value)

    def __getattr__(self, name):
        return getattr(math, name)


def auto_jacobian(seed, p0, zstar, hstar):
    variables = [Dual.basis(zstar[i], i) for i in range(N)]
    h = Dual.basis(hstar, N)
    original_math = engine.math
    try:
        engine.math = DualMathProxy()
        residual = engine.prefix_residual(seed, p0, "binding",
            (h, 0., 0., 0.), variables)
    finally:
        engine.math = original_math

    require(len(residual) == N and all(isinstance(x, Dual) for x in residual),
            "Derivative silently dropped from one of the 33 source-shaped rows")
    # Exactly the SOURCE-shaped L financing dual (under sigma=1), with
    # direct dependence only on z8,z15,z24,z28.
    s = seed.s
    c0 = seed.U0[1] * variables[8].exp()
    c1 = seed.U1[1] * variables[24].exp()
    pi1 = seed.U1[5] * variables[28].exp()
    loan = seed.U0[8] * variables[15].exp()
    dual = 1.0 / loan - s.be * (c0 / c1) ** s.sigmaE / pi1
    require(isinstance(dual, Dual), "Differential lost from funding-dual row")
    return residual + [dual]


def main():
    require(INPUT.is_file(), "Boundary-search report must be generated first")
    data = json.loads(INPUT.read_text(encoding="utf-8"))
    require(data["status"] ==
            "NUMERICAL_PYTHON_34_BOUNDARY_CANDIDATE_FOUND_NOT_SOURCE_PROOF",
            "No Python frontier root candidate to differentiate")
    require(data["source_sha256"] == fingerprint(SOURCE)
            and data["python_engine_sha256"] == fingerprint(PYTHON)
            and data["preconditioner_sha256"] == fingerprint(PRE),
            "Model/source/preconditioner hash provenance drift")
    candidate = data["numerical_candidate"]
    z, h = candidate["baseline_33_unknowns"], candidate["innovation_h"]
    require(len(z) == N and candidate["max_34_residual"] < 1e-9,
            "Numerical reference unsuitable for this derivative audit")
    pins = json.loads(PRE.read_text(encoding="utf-8"))
    p0 = [[float(v) for v in row] for row in pins["P0"]]
    require(len(p0) == 16 and all(len(row) == 6 for row in p0),
            "Pinned tail dimensions changed")
    seed = frozen_stationary_seed(engine.steady_case())
    start = tuple(seed.X0)

    objects = auto_jacobian(seed, p0, z, h)
    require(len(objects) == DIM, "Wrong augmented Jacobian dimension")
    J = [list(value.grad) for value in objects]
    r = [value.value for value in objects]
    require(all(len(row) == DIM for row in J), "Wrong Jacobian shape")
    require(tuple(seed.X0) == start, "Inherited state modified by AD")
    require(max(abs(v) for v in r) < 1e-9,
            "Forward-mode primal residual disagrees with 34-equation root")
    require(J[-1][-1] == 0., "The SOURCE-shaped 34th row has direct h dependence")
    require(all(J[-1][j] == 0. for j in range(N)
                if j not in (8,15,24,28)),
            "Nonzero 34th-row derivative outside four SOURCE coordinates")

    previous = candidate["float_jacobian_probe"]
    finiteA = previous["first33_jacobian"]
    finiteB = previous["policy_forcing_column_b"]
    errorA = max(abs(J[i][j] - finiteA[i][j])
                 for i in range(N) for j in range(N))
    errorB = max(abs(J[i][-1] - finiteB[i]) for i in range(N))
    errorC = max(abs(J[-1][j] -
                     float(previous["sparse_funding_dual_gradient_c"].get(str(j),0.)))
                 for j in range(N))
    require(errorA < 2e-5 and errorB < 2e-5 and errorC < 1e-12,
            "Forward AD and central finite differences disagree")

    b = [J[i][-1] for i in range(N)]
    A = [row[:N] for row in J[:N]]
    u, pivots = engine.solve_linear(A, [-v for v in b])
    s_AD = sum(J[-1][i]*u[i] for i in range(N))
    require(math.isfinite(s_AD) and s_AD < -1e-3,
            "AD Schur scalar is not strictly negative at Python frontier")
    require(abs(s_AD-previous["approximate_schur_minus_c_Ainv_b"]) < 0.002,
            "AD and finite-difference Schur diagnostics disagree")
    linear_error = max(abs(sum(A[i][k]*u[k] for k in range(N)) + b[i])
                       for i in range(N))
    require(linear_error < 1e-8, "AD linear tangent identity failed")

    report = {
        "status": "FLOAT64_FORWARD_AD_PYTHON_34_JACOBIAN_NOT_SOURCE",
        "source_sha256": fingerprint(SOURCE),
        "python_engine_sha256": fingerprint(PYTHON),
        "tail_preconditioner_sha256": fingerprint(PRE),
        "parent_boundary_report_sha256": fingerprint(INPUT),
        "point": {"h": h, "log_coordinates": z,
                  "frozen_initial_state": list(start)},
        "augmented_34_residual": r,
        "forward_ad_jacobian_34": J,
        "max_augmented_residual": max(abs(v) for v in r),
        "max_A_difference_vs_centered_fd": errorA,
        "max_b_difference_vs_centered_fd": errorB,
        "max_c_difference_vs_independent_exact_sparse_formula": errorC,
        "sparse_last_row_indices": [8,15,24,28],
        "last_row_policy_derivative": J[-1][-1],
        "forward_ad_schur_scalar": s_AD,
        "float_min_33_pivot": min(pivots),
        "float_linear_tangent_error": linear_error,
        "original_prefix_residual_differentiated_without_row_transcription": True,
        "genuine_SOURCE_operator_differentiated": False,
        "directed_rounding_derivative_error_enclosure": False,
        "source_python_functional_equivalence_proved": False,
        "economic_34_root_existence_proved": False,
    }
    OUT.parent.mkdir(parents=True, exist_ok=True)
    OUT.write_text(json.dumps(report, indent=2, sort_keys=True)+"\n",
                   encoding="utf-8")
    print(json.dumps({key: report[key] for key in (
        "status", "max_augmented_residual",
        "max_A_difference_vs_centered_fd", "max_b_difference_vs_centered_fd",
        "max_c_difference_vs_independent_exact_sparse_formula",
        "forward_ad_schur_scalar", "last_row_policy_derivative",
    )}, indent=2))


if __name__ == "__main__":
    main()
