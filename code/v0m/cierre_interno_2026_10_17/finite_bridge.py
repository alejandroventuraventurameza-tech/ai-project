"""Internal finite-node algebra and interval Jacobians, not an IRF engine."""
from pathlib import Path
import importlib.util
import json
import os
import numpy as np

HERE = Path(__file__).resolve().parent
PREVIOUS = HERE.parent / "cotas_2026_10_15"
spec = importlib.util.spec_from_file_location(
    "interval_arithmetic", PREVIOUS / "verified_linear_operator.py"
)
bd = importlib.util.module_from_spec(spec)
spec.loader.exec_module(bd)
I, D = bd.I, bd.D


class AD:
    """Interval value and interval first derivatives in log coordinates."""
    size = 1

    def __init__(self, value=0, derivative=None):
        self.x = I(value)
        self.d = bd.zeros((AD.size,)) if derivative is None else derivative

    def __add__(self, other):
        z = asad(other)
        return AD(self.x + z.x, self.d + z.d)

    __radd__ = __add__

    def __neg__(self):
        return AD(-self.x, -self.d)

    def __sub__(self, other):
        return self + (-asad(other))

    def __rsub__(self, other):
        return asad(other) + (-self)

    def __mul__(self, other):
        z = asad(other)
        return AD(self.x * z.x, self.d * z.x + z.d * self.x)

    __rmul__ = __mul__

    def reciprocal(self):
        inv = self.x.reciprocal()
        return AD(inv, -self.d * inv * inv)

    def __truediv__(self, other):
        return self * asad(other).reciprocal()

    def __rtruediv__(self, other):
        return asad(other) * self.reciprocal()

    def __pow__(self, n):
        assert isinstance(n, int)
        if n == 0:
            return AD(1)
        return AD(self.x ** n, self.d * I(n) * self.x ** (n - 1))

    def root(self, n):
        value = self.x.root(n)
        return AD(value, self.d * value / (I(n) * self.x))

    def exp(self):
        value = self.x.exp()
        return AD(value, self.d * value)

    def ln(self):
        return AD(self.x.ln(), self.d / self.x)


def asad(x):
    return x if isinstance(x, AD) else AD(x)


# Let interval constants defer mixed operations to AD; pure interval arithmetic
# still uses the previously audited methods without alteration.
def defer_to_ad(original):
    def method(self, other):
        return NotImplemented if isinstance(other, AD) else original(self, other)
    return method


for operation in ("__add__", "__sub__", "__mul__", "__truediv__"):
    setattr(I, operation, defer_to_ad(getattr(I, operation)))


def total(values):
    return sum(values, AD(0))


def enclosure(x):
    if isinstance(x, AD):
        x = x.x
    return [str(x.lo), str(x.hi)]


def scalar_boundary(s, R):
    """One scalar equation with an exactly stationary continuation."""
    R = asad(R)
    rr = R - s.cbar
    rd = (
        rr + (1 - s.rho) * s.cbar + s.rho * s.zeta * s.cdiff / 2
    ) / (1 + s.zeta * s.cdiff / (2 * rr))
    q = (s.uc[1] + s.ad * s.q) / R
    scale = 1 / (s.ad + (q - 1) / s.phiI)
    cw = s.CW / (s.bw * rd)
    c = [
        s.cc[0] * (q - s.pledge[0] * s.J / R) / s.p[0],
        s.cc[1] / (s.be * R),
    ]
    k = [s.k[i] * scale for i in range(2)]
    w = s.w * ((cw / s.CW) * (scale ** 4).root(5)).root(3)
    ell = [
        (s.beta * s.mc * s.technology[i] * (k[i] ** 2).root(5) / w) ** 2
        for i in range(2)
    ]
    yy = [w * v / (s.beta * s.mc) for v in ell]
    Y = total([s.mass[i] * yy[i] for i in range(2)])
    K = s.K * scale
    inv = s.K - s.ad * K
    Gamma = inv + s.phiI * inv ** 2 / (2 * K)
    f = Y - cw - total([s.mass[i] * c[i] for i in range(2)]) - Gamma
    return f, dict(
        R=R, rr=rr, rd=rd, q=q, scale=scale, cw=cw, c=c,
        k=k, w=w, Y=Y, yy=yy, inv=inv,
    )


def make_boundary():
    AD.size = 1
    s = bd.steady()
    lo, hi = D("1.025"), D("1.032")
    assert scalar_boundary(s, I(lo))[0].x.hi < 0
    assert scalar_boundary(s, I(hi))[0].x.lo > 0
    derivative = scalar_boundary(s, AD(I(lo, hi), bd.arr([I(1)])))[0].d[0]
    assert derivative.lo > 0
    for _ in range(180):
        mid = (lo + hi) / 2
        value = scalar_boundary(s, I(mid))[0].x
        if value.hi < 0:
            lo = mid
        elif value.lo > 0:
            hi = mid
        else:
            break
    f, raw = scalar_boundary(s, I(lo, hi))
    z = {
        key: ([v.x for v in val] if isinstance(val, list) else val.x)
        for key, val in raw.items()
    }
    h = s.rho + (z["rd"] / z["rr"] - s.rho) * s.zeta * (
        (1 - s.tight) / (1 + s.tight)
    )
    equity = s.E * s.rate / z["R"]
    bankB = s.B * s.rate / z["R"]
    bankD = (bankB - equity) / (1 - h)
    money = h * bankD
    faces = [
        (1 - s.beta) * s.mc * z["yy"][i] + s.ad * z["q"] * z["k"][i]
        - z["c"][i] - (z["q"] - s.pledge[i] * s.J / z["R"]) * s.k[i]
        for i in range(2)
    ]
    X0 = [*z["k"], *faces, equity, s.rr, s.M]
    U0 = [*z["c"], z["cw"], z["w"], s.mc, I(1), z["q"],
          z["rd"], z["R"], s.tight]
    X1 = [*s.k, *s.F, s.E, z["rr"], money]
    U1 = list(s.base[6:])
    X2 = list(s.base[:6])
    e0 = [(z["rr"] / s.rr).ln() - I(".0625") * (z["Y"] / s.Y).ln(),
          (money / s.M).ln()]
    e1 = [-I(".5") * (z["rr"] / s.rr).ln(),
          -I(".5") * (money / s.M).ln()]
    margins = {
        "H_dual": 1 / z["R"] - s.be * z["c"][0] / s.cc[0],
        "inherited_cover_H": s.pledge[0] * s.ad * z["q"] * z["k"][0] - faces[0],
        "inherited_cover_L": s.pledge[1] * s.ad * z["q"] * z["k"][1] - faces[1],
        "deposit_cap": 4 - bankD / equity,
        "loan_cap": 6 - bankB / equity,
        "positive_investment": z["inv"],
        "retention": z["R"] / z["rd"] - 1,
        "bank_continuation": 1 - I(".9") * z["R"] / z["rd"],
        "household_public_bonds_Gbar_2Mbar": 2 * s.M - money,
        "loan_deposit_spread": z["R"] - z["rd"],
        "effective_price_H": z["q"] - s.pledge[0] * s.J / z["R"],
        "effective_price_L": z["q"] - s.pledge[1] * s.J / z["R"],
        "consumption_H": z["c"][0],
        "consumption_L": z["c"][1],
        "consumption_W": z["cw"],
        "inherited_face_H": faces[0],
        "inherited_face_L": faces[1],
        "reserve_ratio_lower": h,
        "reserve_ratio_upper": 1 - h,
        "no_deposit_dual_H": 1 - z["rd"] * s.be * z["c"][0] / s.cc[0],
        "no_deposit_dual_L": 1 - z["rd"] / z["R"],
    }
    for name, value in margins.items():
        assert value.lo > 0, (name, value)
    returns, ib_positions = [], []
    for omega, slope, name in [(I("-.2"), s.cm, "minus"), (I(".2"), s.cp, "plus")]:
        surplus = money - s.rho * bankD + (z["rd"] / z["rr"] - s.rho) * omega * bankD
        margins["solvency_" + name] = (
            z["R"] * bankB + z["rr"] * money - z["rd"] * bankD + slope * surplus
        ) / equity
        margins["payment_sign_" + name] = -surplus if name == "minus" else surplus
        assert margins["solvency_" + name].lo > 0
        assert margins["payment_sign_" + name].lo > 0
        returns.append(margins["solvency_" + name])
        ib_positions.append(
            -(s.aa if name == "minus" else s.tight * s.aa) * surplus
        )
    assert ((returns[0] + returns[1]) / 2 - z["R"]).magnitude() < D("1e-45")
    assert ((ib_positions[0] + ib_positions[1]) / 2).magnitude() < D("1e-45")
    return s, z, X0, U0, X1, U1, X2, e0, e1, margins, derivative, f.x


def production(s, k, u):
    w, m = u[3:5]
    ell = [
        (s.beta * m * s.technology[i] * (k[i] ** 2).root(5) / w) ** 2
        for i in range(2)
    ]
    yy = [w * v / (s.beta * m) for v in ell]
    profit = [(1 - s.beta) * m * v for v in yy]
    uk = [s.alpha * m * yy[i] / k[i] for i in range(2)]
    return ell, yy, profit, uk


def auxiliary(s, X, U, k_next, e, rho=None, corridor=None):
    rho = asad(s.rho if rho is None else rho)
    corridor = asad(s.Delta if corridor is None else corridor)
    k = X[:2]
    ell, yy, profit, uk = production(s, k, U)
    c, cw, w, m, pi, q, rd, rl, th = U[:2], *U[2:]
    K = total([s.mass[i] * k[i] for i in range(2)])
    Knext = total([s.mass[i] * k_next[i] for i in range(2)])
    Y = total([s.mass[i] * yy[i] for i in range(2)])
    L = total([s.mass[i] * ell[i] for i in range(2)])
    rr = s.rr * (
        I(".5") * (X[5] / s.rr).ln()
        + I(".5") * (I("1.5") * pi.ln() + I(".125") * (Y / s.Y).ln()) + e[0]
    ).exp()
    money = s.M * (I(".5") * (X[6] / s.M).ln() + e[1]).exp()
    nu = 1 / (1 + (2 - th).root(2))
    cm = corridor * (1 - s.aa + s.aa * nu)
    cp = corridor * th * s.aa * nu
    cb, cd = (cm + cp) / 2, cm - cp
    xi = rd / rr
    h = rho + (xi - rho) * s.zeta * (1 - th) / (1 + th)
    N = [
        profit[i] + s.ad * q * k[i] - X[2 + i] / pi for i in range(2)
    ]
    investment = Knext - s.ad * K
    Gamma = investment + s.phiI * investment ** 2 / (2 * K)
    Rot = I(75) * (pi - 1) ** 2 * Y
    return dict(
        K=K, Y=Y, L=L, rr=rr, money=money, cb=cb, cd=cd, xi=xi,
        h=h, N=N, inv=investment, Gamma=Gamma, Rot=Rot, uk=uk,
        rho=rho, corridor=corridor,
    )


def remaining(s, X, U, Xnext, Unext, a, anext):
    c, cw, w, m, pi, q, rd, rl, th = U[:2], *U[2:]
    lw = s.bw * cw / Unext[2]
    return [
        (Xnext[4] / (s.aB * rl * X[4] / pi)).ln(),
        q - 1 - s.phiI * a["inv"] / a["K"],
        cw + total([s.mass[i] * c[i] for i in range(2)]) + a["Gamma"] + a["Rot"] - a["Y"],
        (w / (s.chiW * a["L"] * cw)).ln(),
        (rd * lw / Unext[5]).ln(),
        1 - s.eps + s.eps * m - I(150) * pi * (pi - 1)
        + lw * I(150) * anext["Y"] / a["Y"] * Unext[5] * (Unext[5] - 1),
        (Xnext[5] / a["rr"]).ln(),
        (Xnext[6] / a["money"]).ln(),
        rl - a["rr"] - a["cb"],
        a["rr"] + (1 - a["rho"]) * a["cb"]
        - (a["xi"] - a["rho"]) * s.zeta * a["cd"] / 2 - rd,
        total([s.mass[i] * Xnext[2 + i] / rl for i in range(2)])
        - (X[4] / pi + (1 / a["h"] - 1) * a["money"]),
    ]


def evaluate_bridge(base, P, branch, policy_inputs=True, point_capture=None):
    s, z, X0b, U0b, X1b, U1b, X2b, e0b, e1b, *_ = base
    AD.size = 37
    eps = []
    for j in range(37):
        d = bd.zeros((37,))
        d[j] = I(1)
        eps.append(AD(0, d))
    X1 = [X1b[j] * eps[j].exp() for j in range(7)]
    U0 = [U0b[j] * eps[7 + j].exp() for j in range(10)]
    x2 = eps[17:23]
    X2common = [X2b[j] * x2[j].exp() for j in range(6)]
    U1 = [U1b[j] * eps[23 + j].exp() for j in range(10)]
    tail_log = [total([P[i, j] * x2[j] for j in range(6)]) for i in range(16)]
    tail = [s.base[i] * tail_log[i].exp() for i in range(16)]
    U2 = tail[6:]
    X2 = [
        *X2common[:2],
        *[s.pledge[i] * X2common[2] * X2common[i] for i in range(2)],
        X2common[3], X2common[4], X2common[5],
    ]
    X0 = [asad(v) for v in X0b]
    e0 = [asad(e0b[j]) + eps[33 + j] for j in range(2)]
    e1 = [asad(v) for v in e1b]
    a0 = auxiliary(s, X0, U0, X1[:2], e0,
                   rho=s.rho + eps[35], corridor=s.Delta + eps[36])
    a1 = auxiliary(s, X1, U1, X2[:2], e1)
    # Only production is required in a2. Its unused policy inputs are harmless.
    a2 = auxiliary(s, X2, U2, X2[:2], [AD(0), AD(0)])
    le0 = [s.be * U0[i] / U1[i] for i in range(2)]
    le1 = [s.be * U1[i] / U2[i] for i in range(2)]
    J1 = s.ad * U1[5] * U1[6]
    J2 = X2common[2]
    res0 = []
    for i in range(2):
        H = s.pledge[i] * J1
        res0.append(U0[i] + U0[6] * X1[i] - X1[2 + i] / U0[8] - a0["N"][i])
        if i == 1 and branch == "slack":
            res0.append(U0[6] - le0[i] * (a1["uk"][i] + s.ad * U1[6]))
            res0.append((U0[8] * le0[i] / U1[5]).ln())
        else:
            res0.append(
                U0[6] - H / U0[8]
                - le0[i] * (a1["uk"][i] + s.ad * U1[6] - H / U1[5])
            )
            res0.append((X1[2 + i] / (H * X1[i])).ln())
    res0 += remaining(s, X0, U0, X1, U1, a0, a1)
    res1 = []
    for i in range(2):
        H = s.pledge[i] * J2
        res1.append(U1[i] + (U1[6] - H / U1[8]) * X2[i] - a1["N"][i])
        res1.append(
            U1[6] - H / U1[8]
            - le1[i] * (a2["uk"][i] + s.ad * U2[6] - H / U2[5])
        )
    res1.append((J2 / (s.ad * U2[5] * U2[6])).ln())
    res1 += remaining(s, X1, U1, X2, U2, a1, a2)
    assert len(res0) == 17 and len(res1) == 16
    residuals = res0 + res1
    J = bd.arr([r.d[:33] for r in residuals])
    forcing = bd.arr([r.d[33:] for r in residuals])
    metrics = {
        "L_cover_slack_ratio": 1 - X1[3] / (s.pledge[1] * J1 * X1[1]),
        "L_dual": 1 / U0[8] - le0[1] / U1[5],
        "log_loan_rate": (U0[8] / z["R"]).ln(),
        "log_relative_capital": (X1[0] / X1[1]).ln(),
        "log_H_capital": (X1[0] / s.k[0]).ln(),
        "log_L_capital": (X1[1] / s.k[1]).ln(),
        "log_total_next_capital": (
            total([s.mass[i] * X1[i] for i in range(2)]) / s.K
        ).ln(),
        "log_H_credit": (X1[2] / U0[8]).ln(),
        "log_L_credit": (X1[3] / U0[8]).ln(),
        "log_reserve_remuneration": (a0["rr"] / z["rr"]).ln(),
        "interbank_rate": a0["rr"] + a0["corridor"] / (1 + (2 - U0[9]).root(2)),
        "loan_deposit_spread": U0[8] - U0[7],
        "loan_liquidity_component": U0[8] - a0["rr"],
        "log_OTC_tightness": (U0[9] / s.tight).ln(),
    }
    ZA = total([s.mass[i] * I(s.technology[i]) ** 10 for i in range(2)])
    effective_output = (
        ZA.root(10) * (total([s.mass[i] * X1[i] for i in range(2)]) ** 2).root(5)
        * a1["L"].root(2)
    )
    metrics["conditional_misallocation_loss"] = (effective_output / a1["Y"]).ln()
    solution = bd.solve(J, -forcing)
    inverse = bd.solve(J, bd.eye(33))
    inverse_error = bd.upper_norm(J @ inverse - bd.eye(33))
    assert inverse_error < D("1e-32"), inverse_error
    # OPTIONAL point-only export; default generated economic certificate unchanged.
    # The exact Lean modified row 5 is 1 - coverage - prescribed_slack,
    # NOT the legacy binding log(coverage) row at finite deviations.
    if point_capture is not None and branch == "binding":
        source_row5 = 1 - X1[3] / (s.pledge[1] * J1 * X1[1])
        source_J = bd.arr([
            [source_row5.d[j] if i == 5 else J[i, j] for j in range(33)]
            for i in range(33)
        ])
        # The old logarithmic-row inverse with column 5 flipped is a
        # sensible POINT preconditioner, not an interval inverse.
        source_R = bd.arr([
            [I(-inverse[i, j].midpoint() if j == 5 else
               inverse[i, j].midpoint()) for j in range(33)]
            for i in range(33)
        ])
        source_F0 = [
            enclosure(source_row5 if i == 5 else residuals[i])
            for i in range(33)
        ]
        source_G0 = [
            ([["-1", "-1"]] if i == 5 else [["0", "0"]]) +
            [enclosure(source_row5.d[33 + j] if i == 5
                       else forcing[i, j]) for j in range(4)]
            for i in range(33)
        ]
        point_defect_upper = bd.upper_norm(source_R @ source_J - bd.eye(33))
        assert point_defect_upper < D("0.5"), point_defect_upper
        point_capture.update({
            "schema": "ventura-source-point-jacobian-CANDIDATE-v1",
            "scope": "POINT-ONLY. NOT a product-ball IFT enclosure or Lean proof.",
            "branch": "binding",
            "parameters_order": ["s", "v_R", "v_M", "v_rho", "v_Delta"],
            "state_dimension": 33,
            "parameter_dimension": 5,
            "source_residual": "localBindingResidualWithSlack (SEMANTIC ROW MAP STILL TO BE PROVED)",
            "source_row5": "1-coverage-s (direct interval automatic differentiation)",
            "preconditioner": [[str(source_R[i, j].midpoint()) for j in range(33)]
                               for i in range(33)],
            "point_jacobian_box": [[enclosure(source_J[i, j]) for j in range(33)]
                                   for i in range(33)],
            "point_policy_derivative_box": source_G0,
            "point_center_residual_box": source_F0,
            "point_preconditioned_defect_upper": str(point_defect_upper),
            "uniform_ball_jacobian_enclosures_proven": False,
            "exact_zero_center_proven": False,
            "economic_source_row_map_proven": False,
            "formal_Lean_witness_established": False,
        })
    responses = {
        name: metric.d[:33] @ solution + metric.d[33:]
        for name, metric in metrics.items()
    }
    # An independent hand stencil from the previous audit must agree after
    # compressing the two inherited faces to their common binding manifold.
    order = [0, 2, 1, 3, *range(4, 16)]
    tail_rows = bd.arr([res1[i].d[:33] for i in order])
    for i in range(2):
        tail_rows[2 + i] = tail_rows[2 + i] - s.be * s.pledge[i] * s.J * tail_rows[4]
    current_map = bd.zeros((33, 16))
    current_map[0, 0] = current_map[1, 1] = I(1)
    current_map[2, 0] = current_map[2, 2] = I(1)
    current_map[3, 1] = current_map[3, 2] = I(1)
    current_map[4, 3] = current_map[5, 4] = current_map[6, 5] = I(1)
    for i in range(10):
        current_map[23 + i, 6 + i] = I(1)
    C0, C1 = bd.coefficients(s)
    current_error = bd.upper_norm(tail_rows @ current_map - C0)
    future_error = bd.upper_norm(tail_rows[:, 17:23] - C1 @ P)
    assert current_error < D("1e-35"), current_error
    assert future_error < D("1e-35"), future_error
    schur = None
    if branch == "binding":
        # The L coverage row is log(f/Hk) - log(1-s) = 0.
        # At s=0 its partial derivative with respect to s is +1.
        v = -inverse[:, 5]
        schur = enclosure(metrics["L_dual"].d[:33] @ v)
    maxres = max(r.x.magnitude() for r in residuals)
    assert maxres < D("1e-45"), maxres
    return dict(
        residual_upper=str(maxres),
        inverse_norm_upper=str(bd.upper_norm(inverse)),
        inverse_identity_error_upper=str(inverse_error),
        independent_current_stencil_error_upper=str(current_error),
        independent_future_stencil_error_upper=str(future_error),
        reduced_mu_derivative_with_respect_to_slack=schur,
        response_enclosures={
            key: [enclosure(v) for v in vals] for key, vals in responses.items()
        },
    )


def main():
    base = make_boundary()
    s, z, X0, U0, X1, U1, X2, e0, e1, margins, derivative, residual = base
    raw = json.loads((PREVIOUS / "rational_preconditioners.json").read_text())
    cert = json.loads((PREVIOUS / "verified_linear_bounds.json").read_text())
    error = D(cert["exact_graph_entry_error_upper"])
    P = bd.arr([
        [I(value) + (I(-error, error) if i >= 6 else I(0)) for value in row]
        for i, row in enumerate(raw["P0"])
    ])
    point_capture = {} if os.environ.get("VENTURA_EXPORT_POINT_MATRICES") == "1" else None
    branches = {
        branch: evaluate_bridge(base, P, branch,
                 point_capture=(point_capture if branch == "binding" else None))
        for branch in ("slack", "binding")
    }
    if point_capture is not None:
        assert point_capture["state_dimension"] == 33
        (HERE / "binding_source_point_jacobian_CANDIDATE.json").write_text(
            json.dumps(point_capture, indent=2) + "\n",
            encoding="utf-8", newline="\n")
        print("EXPORTED POINT ONLY: binding_source_point_jacobian_CANDIDATE.json")
    # Check the policy-sign conclusions used in the text in both branches.
    for name, info in branches.items():
        responses = info["response_enclosures"]
        assert D(responses["log_loan_rate"][0][0]) > 0
        assert D(responses["log_loan_rate"][1][1]) < 0
        assert D(responses["log_reserve_remuneration"][0][0]) > 0
    def signed_interval(pair, direction):
        value = I(*pair) * I(direction)
        return value
    directions = (-1, 1, -1, -1)
    for j, direction in enumerate(directions):
        S = branches["slack"]["response_enclosures"]
        B = branches["binding"]["response_enclosures"]
        assert signed_interval(S["L_cover_slack_ratio"][j], direction).lo > 0
        assert signed_interval(B["L_dual"][j], direction).lo > 0
        for branch_responses in (S, B):
            assert signed_interval(branch_responses["log_loan_rate"][j], direction).hi < 0
            assert signed_interval(branch_responses["log_H_credit"][j], direction).lo > 0
            assert signed_interval(branch_responses["interbank_rate"][j], direction).hi < 0
        assert signed_interval(S["log_relative_capital"][j], direction).lo > 0
        assert signed_interval(B["log_relative_capital"][j], direction).hi < 0
        assert signed_interval(S["conditional_misallocation_loss"][j], direction).hi < 0
        assert signed_interval(B["conditional_misallocation_loss"][j], direction).lo > 0
    assert D(branches["slack"]["response_enclosures"]["L_cover_slack_ratio"][0][1]) < 0
    assert D(branches["slack"]["response_enclosures"]["L_cover_slack_ratio"][1][0]) > 0
    assert D(branches["binding"]["response_enclosures"]["L_dual"][0][1]) < 0
    assert D(branches["binding"]["response_enclosures"]["L_dual"][1][0]) > 0
    assert D(branches["binding"]["reduced_mu_derivative_with_respect_to_slack"][1]) < 0
    for info in branches.values():
        r = info["response_enclosures"]
        assert D(r["loan_liquidity_component"][1][1]) < 0
        assert D(r["loan_deposit_spread"][1][0]) > 0
        assert D(r["loan_deposit_spread"][2][0]) > 0
        assert D(r["loan_deposit_spread"][3][0]) > 0
    result = {
        "scope": __doc__,
        "interpretation": (
            "Exact scalar boundary construction plus interval nonsingularity "
            "and local comparative derivatives of two finite equations blocks "
            "closed by the already proved infinite deterministic tail."
        ),
        "scalar_root": enclosure(z["R"]),
        "scalar_derivative_on_initial_bracket": enclosure(derivative),
        "scalar_residual_enclosure": enclosure(residual),
        "initial_controls": {
            key: enclosure(z[key]) for key in ["rr", "rd", "q", "cw", "w", "Y", "inv"]
        },
        "initial_state_seven": [enclosure(x) for x in X0],
        "initial_controls_ten": [enclosure(x) for x in U0],
        "announced_innovations_t0": [enclosure(x) for x in e0],
        "announced_innovations_t1": [enclosure(x) for x in e1],
        "policy_derivative_columns": [
            "initial log reserve-remuneration rule innovation",
            "initial log reserve-quantity rule innovation",
            "temporary initial reserve-requirement level change",
            "temporary initial gross-return corridor-width change",
        ],
        "strict_initial_margins": {key: enclosure(value) for key, value in margins.items()},
        "branches": branches,
        "limits": (
            "No empirical calibration, no macro IRF or simulated shock path. "
            "Derivatives describe an infinitesimal initial-node comparison "
            "with fixed inherited states and fixed subsequent announced "
            "innovations. IFT supplies existence locally; this calculation "
            "does not supply a quantitative nonlinear policy radius."
        ),
    }
    (HERE / 'finite_bridge_certificate.json').write_text(json.dumps(result, indent=2) + '\n', encoding='utf-8', newline='\n')
    print("Scalar root, both finite Jacobians and policy signs verified.")
    for branch, info in branches.items():
        print(branch, "inverse norm <", info["inverse_norm_upper"][:15])


if __name__ == "__main__":
    main()
