#!/usr/bin/env python3
"""Finite-payment-law, local-linear IRFs for the manuscript's internal case.

This is deliberately not a calibration or a source theorem.  It reconstructs
the exact two-date nonlinear prefix used by ``finite_bridge.py``, solves it for
each active set, and then propagates the already audited deterministic stable
graph.  Only Python's standard library is used.
"""

from __future__ import annotations

import argparse
import csv
import hashlib
import json
import math
from pathlib import Path
from types import SimpleNamespace


HERE = Path(__file__).resolve().parent
DEFAULT_CACHE = HERE.parent / "v0m"
# Historical bridge digest was e3523811b5433a076e13fe51479a4a518e338386498898d46549b2b6929063fa (initial IRF source commit 02bce4c).
# 2026-11-07/08 audit: optional interval-AD point/box export, direct L-dual center,
# parameter
# invocations and new diagnostic export paths; scalar_boundary, make_boundary
# and the original default bridge residual calculations remain unchanged. Keep a strict pin to
# the new complete source instead of bypassing the provenance check.
SOURCE_HASHES = {
    "finite_bridge.py": "62f60baa22b93157e92be8c98e76e4e8943ad3067a7b4b0bbbf7bb42caaa1097",
    "verified_linear_operator.py": "1369e9c04ed9774297d957ea27d8dad893f99fc17fb08c9819fa9a378ca6400b",
    "rational_preconditioners.json": "d0cef14050de9f4725e51e5cd28b1ea77e33733dfb2c78d2e38a193200337e94",
}

PREFIX_ROW_NAMES = [
    "firm_budget_0_H", "firm_capital_euler_0_H", "firm_regime_0_H",
    "firm_budget_0_L", "firm_capital_euler_0_L", "firm_regime_0_L",
    "bank_equity_0", "capital_supply_0", "resources_0", "worker_labor_0",
    "household_euler_0", "nkpc_0", "reserve_rate_rule_0",
    "reserve_quantity_rule_0", "loan_pricing_0", "deposit_pricing_0",
    "bank_balance_0", "firm_budget_1_H", "firm_capital_euler_1_H",
    "firm_budget_1_L", "firm_capital_euler_1_L", "common_pledge_1",
    "bank_equity_1", "capital_supply_1", "resources_1", "worker_labor_1",
    "household_euler_1", "nkpc_1", "reserve_rate_rule_1",
    "reserve_quantity_rule_1", "loan_pricing_1", "deposit_pricing_1",
    "bank_balance_1",
]


def sha256(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as handle:
        for block in iter(lambda: handle.read(1 << 20), b""):
            h.update(block)
    return h.hexdigest()


def dot(a, b):
    return sum(x * y for x, y in zip(a, b))


def matvec(a, x):
    return [dot(row, x) for row in a]


def matmul(a, b):
    cols = list(zip(*b))
    return [[dot(row, col) for col in cols] for row in a]


def identity(n):
    return [[1.0 if i == j else 0.0 for j in range(n)] for i in range(n)]


def max_abs(values):
    return max((abs(x) for x in values), default=0.0)


def solve_linear(a, b):
    """Pivoted dense solve, returning solution and absolute pivot sizes."""
    n = len(a)
    aa = [list(row) for row in a]
    bb = list(b)
    pivots = []
    for k in range(n):
        p = max(range(k, n), key=lambda i: abs(aa[i][k]))
        if abs(aa[p][k]) < 1e-15:
            raise ArithmeticError(f"singular numerical pivot at column {k}: {aa[p][k]}")
        aa[k], aa[p] = aa[p], aa[k]
        bb[k], bb[p] = bb[p], bb[k]
        pivot = aa[k][k]
        pivots.append(abs(pivot))
        inv = 1.0 / pivot
        for j in range(k, n):
            aa[k][j] *= inv
        bb[k] *= inv
        for i in range(n):
            if i == k:
                continue
            factor = aa[i][k]
            if factor == 0.0:
                continue
            for j in range(k, n):
                aa[i][j] -= factor * aa[k][j]
            bb[i] -= factor * bb[k]
    return bb, pivots


def inverse_inf_norm(a):
    n = len(a)
    inv_cols = []
    pivots = []
    for j in range(n):
        rhs = [0.0] * n
        rhs[j] = 1.0
        col, ps = solve_linear(a, rhs)
        inv_cols.append(col)
        pivots.extend(ps)
    rows = list(zip(*inv_cols))
    return max(sum(abs(x) for x in row) for row in rows), min(pivots)


def numerical_jacobian(function, x, step=2e-6):
    base = function(x)
    n = len(x)
    jac = [[0.0] * n for _ in base]
    for j in range(n):
        d = step * max(1.0, abs(x[j]))
        xp = list(x)
        xm = list(x)
        xp[j] += d
        xm[j] -= d
        fp = function(xp)
        fm = function(xm)
        for i in range(len(base)):
            jac[i][j] = (fp[i] - fm[i]) / (2.0 * d)
    return jac


def newton(function, initial, tolerance=2e-12, max_iterations=30):
    x = list(initial)
    history = []
    last_jac = None
    for iteration in range(max_iterations):
        residual = function(x)
        norm = max_abs(residual)
        history.append(norm)
        if norm < tolerance:
            if last_jac is None:
                last_jac = numerical_jacobian(function, x)
            return x, history, last_jac
        jac = numerical_jacobian(function, x)
        last_jac = jac
        step, _ = solve_linear(jac, [-v for v in residual])
        accepted = False
        scale = 1.0
        while scale >= 2.0 ** -16:
            candidate = [v + scale * dv for v, dv in zip(x, step)]
            candidate_norm = max_abs(function(candidate))
            if candidate_norm < norm:
                x = candidate
                accepted = True
                break
            scale *= 0.5
        if not accepted:
            raise ArithmeticError(
                f"Newton line search failed at iteration {iteration}, residual={norm:.3e}"
            )
    raise ArithmeticError(f"Newton did not converge: residual={history[-1]:.3e}")


def steady_case():
    s = SimpleNamespace()
    values = dict(
        bw=.99, be=.96, alpha=.4, beta=.5, delta=.025, phiI=.5,
        eps=6.0, sigmaE=1.0, sigmaW=1.0, varphi=1.0, chiW=1.0,
        rho=.1, zeta=.2, tight=.5, Delta=.02, eta=.1, aa=.5,
    )
    for name, value in values.items():
        setattr(s, name, value)
    s.ad = 1.0 - s.delta
    s.gamma = s.alpha / (1.0 - s.beta)
    s.mass = [.5, .5]
    s.technology = [1.01, 1.0]
    s.pledge = [.15, .4]
    s.rd = 1.0 / s.bw
    s.vv = 1.0 / (1.0 + math.sqrt(1.5))
    s.cm = s.Delta * (1.0 - s.aa + s.aa * s.vv)
    s.cp = s.Delta * s.tight * s.aa * s.vv
    s.cbar = (s.cm + s.cp) / 2.0
    s.cdiff = s.cm - s.cp
    ar = s.rd - (1.0 - s.rho) * s.cbar - s.rho * s.zeta * s.cdiff / 2.0
    s.rr = (ar + math.sqrt(ar * ar + 2.0 * s.rd * s.zeta * s.cdiff)) / 2.0
    s.rate = s.rr + s.cbar
    s.xi = s.rd / s.rr
    s.h = s.rho + (s.xi - s.rho) * s.zeta * (1.0 - s.tight) / (1.0 + s.tight)
    s.ml = 2.0 * s.h
    s.ll = 3.0 - s.ml
    s.q = 1.0 + s.phiI * s.delta
    s.mc = (s.eps - 1.0) / s.eps
    s.uc = [
        s.q * ((1.0 - th * s.ad / s.rate) / s.be - s.ad * (1.0 - th))
        for th in s.pledge
    ]
    c = [(1.0 - s.beta) * (s.mc * z) ** 2 * s.beta for z in s.technology]
    kz = [(s.gamma * c[i] / s.uc[i]) ** 5 for i in range(2)]
    kz_total = dot(s.mass, kz)
    yz = dot(s.mass, [s.uc[i] * kz[i] / (s.alpha * s.mc) for i in range(2)])
    lz = dot(s.mass, [s.beta * s.uc[i] * kz[i] / s.alpha for i in range(2)])
    bz = dot(s.mass, [s.pledge[i] * s.ad * s.q * kz[i] / s.rate for i in range(2)])
    cwz = (1.0 - (1.0 - s.beta) * s.mc) * yz + s.phiI * s.delta ** 2 * kz_total / 2.0 + (s.rate - 1.0) * bz
    s.w = (s.chiW * lz * cwz) ** (1.0 / 12.0)
    s.k = [v * s.w ** -5 for v in kz]
    s.yy = [s.uc[i] * s.k[i] / (s.alpha * s.mc) for i in range(2)]
    s.ell = [s.beta * s.uc[i] * s.k[i] / (s.alpha * s.w) for i in range(2)]
    s.profit = [(1.0 - s.beta) * s.mc * s.yy[i] for i in range(2)]
    s.J = s.ad * s.q
    s.b = [s.pledge[i] * s.J * s.k[i] / s.rate for i in range(2)]
    s.cc = [s.profit[i] - s.delta * s.q * s.k[i] - (s.rate - 1.0) * s.b[i] for i in range(2)]
    s.K = dot(s.mass, s.k)
    s.Y = dot(s.mass, s.yy)
    s.L = dot(s.mass, s.ell)
    s.B = dot(s.mass, s.b)
    s.CW = s.Y - dot(s.mass, s.cc) - (s.delta + s.phiI * s.delta ** 2 / 2.0) * s.K
    s.E = s.B / s.ll
    s.D = 2.0 * s.E
    s.M = s.ml * s.E
    s.aB = 1.0 / s.rate
    s.p = [s.q - s.pledge[i] * s.J / s.rate for i in range(2)]
    s.F = [s.pledge[i] * s.J * s.k[i] for i in range(2)]
    s.base = [*s.k, s.J, s.E, s.rr, s.M, *s.cc, s.CW, s.w, s.mc, 1.0,
              s.q, s.rd, s.rate, s.tight]
    return s


def scalar_boundary(s, loan_rate):
    rr = loan_rate - s.cbar
    rd = (rr + (1.0 - s.rho) * s.cbar + s.rho * s.zeta * s.cdiff / 2.0) / (
        1.0 + s.zeta * s.cdiff / (2.0 * rr)
    )
    q = (s.uc[1] + s.ad * s.q) / loan_rate
    scale = 1.0 / (s.ad + (q - 1.0) / s.phiI)
    cw = s.CW / (s.bw * rd)
    c = [
        s.cc[0] * (q - s.pledge[0] * s.J / loan_rate) / s.p[0],
        s.cc[1] / (s.be * loan_rate),
    ]
    k = [s.k[i] * scale for i in range(2)]
    w = s.w * ((cw / s.CW) * scale ** (4.0 / 5.0)) ** (1.0 / 3.0)
    ell = [
        (s.beta * s.mc * s.technology[i] * k[i] ** .4 / w) ** 2
        for i in range(2)
    ]
    yy = [w * v / (s.beta * s.mc) for v in ell]
    output = dot(s.mass, yy)
    capital = s.K * scale
    investment = s.K - s.ad * capital
    gamma = investment + s.phiI * investment ** 2 / (2.0 * capital)
    residual = output - cw - dot(s.mass, c) - gamma
    return residual, dict(R=loan_rate, rr=rr, rd=rd, q=q, scale=scale, cw=cw,
                          c=c, k=k, w=w, Y=output, yy=yy, inv=investment)


def make_boundary(s):
    lo, hi = 1.025, 1.032
    flo = scalar_boundary(s, lo)[0]
    fhi = scalar_boundary(s, hi)[0]
    if not (flo < 0.0 < fhi):
        raise ArithmeticError("boundary bracket lost")
    for _ in range(100):
        mid = (lo + hi) / 2.0
        fm = scalar_boundary(s, mid)[0]
        if fm < 0.0:
            lo = mid
        else:
            hi = mid
    z = scalar_boundary(s, (lo + hi) / 2.0)[1]
    h = s.rho + (z["rd"] / z["rr"] - s.rho) * s.zeta * (1.0 - s.tight) / (1.0 + s.tight)
    equity = s.E * s.rate / z["R"]
    bank_loans = s.B * s.rate / z["R"]
    deposits = (bank_loans - equity) / (1.0 - h)
    money = h * deposits
    faces = [
        (1.0 - s.beta) * s.mc * z["yy"][i] + s.ad * z["q"] * z["k"][i]
        - z["c"][i] - (z["q"] - s.pledge[i] * s.J / z["R"]) * s.k[i]
        for i in range(2)
    ]
    x0 = [*z["k"], *faces, equity, s.rr, s.M]
    u0 = [*z["c"], z["cw"], z["w"], s.mc, 1.0, z["q"], z["rd"], z["R"], s.tight]
    x1 = [*s.k, *s.F, s.E, z["rr"], money]
    u1 = list(s.base[6:])
    x2 = list(s.base[:6])
    e0 = [math.log(z["rr"] / s.rr) - .0625 * math.log(z["Y"] / s.Y), math.log(money / s.M)]
    e1 = [-.5 * math.log(z["rr"] / s.rr), -.5 * math.log(money / s.M)]
    return SimpleNamespace(s=s, z=z, X0=x0, U0=u0, X1=x1, U1=u1, X2=x2,
                           e0=e0, e1=e1)


def production(s, capital, controls):
    wage, mc = controls[3:5]
    labor = [
        (s.beta * mc * s.technology[i] * capital[i] ** .4 / wage) ** 2
        for i in range(2)
    ]
    output = [wage * value / (s.beta * mc) for value in labor]
    profit = [(1.0 - s.beta) * mc * value for value in output]
    marginal = [s.alpha * mc * output[i] / capital[i] for i in range(2)]
    return labor, output, profit, marginal


def auxiliary(s, state, controls, next_capital, innovations, rho=None, corridor=None):
    rho = s.rho if rho is None else rho
    corridor = s.Delta if corridor is None else corridor
    capital = state[:2]
    labor, output_by_type, profit, marginal = production(s, capital, controls)
    c = controls[:2]
    cw, wage, mc, inflation, q, rd, rl, tightness = controls[2:]
    capital_total = dot(s.mass, capital)
    next_capital_total = dot(s.mass, next_capital)
    output = dot(s.mass, output_by_type)
    total_labor = dot(s.mass, labor)
    rr = s.rr * math.exp(
        .5 * math.log(state[5] / s.rr)
        + .5 * (1.5 * math.log(inflation) + .125 * math.log(output / s.Y))
        + innovations[0]
    )
    money = s.M * math.exp(.5 * math.log(state[6] / s.M) + innovations[1])
    match_value = 1.0 / (1.0 + math.sqrt(2.0 - tightness))
    chi_minus = corridor * (1.0 - s.aa + s.aa * match_value)
    chi_plus = corridor * tightness * s.aa * match_value
    chi_bar = (chi_minus + chi_plus) / 2.0
    chi_diff = chi_minus - chi_plus
    xi = rd / rr
    reserve_ratio = rho + (xi - rho) * s.zeta * (1.0 - tightness) / (1.0 + tightness)
    wealth = [profit[i] + s.ad * q * capital[i] - state[2 + i] / inflation for i in range(2)]
    investment = next_capital_total - s.ad * capital_total
    gamma = investment + s.phiI * investment ** 2 / (2.0 * capital_total)
    rotemberg = 75.0 * (inflation - 1.0) ** 2 * output
    return dict(K=capital_total, Y=output, L=total_labor, rr=rr, money=money,
                cb=chi_bar, cd=chi_diff, cm=chi_minus, cp=chi_plus, xi=xi,
                h=reserve_ratio, N=wealth, inv=investment, Gamma=gamma,
                Rot=rotemberg, uk=marginal, rho=rho, corridor=corridor,
                labor=labor, output_by_type=output_by_type)


def remaining_residuals(s, state, controls, next_state, next_controls, aux, aux_next):
    c = controls[:2]
    cw, wage, mc, inflation, q, rd, rl, _tightness = controls[2:]
    household_sdf = s.bw * cw / next_controls[2]
    return [
        math.log(next_state[4] / (s.aB * rl * state[4] / inflation)),
        q - 1.0 - s.phiI * aux["inv"] / aux["K"],
        cw + dot(s.mass, c) + aux["Gamma"] + aux["Rot"] - aux["Y"],
        math.log(wage / (s.chiW * aux["L"] * cw)),
        math.log(rd * household_sdf / next_controls[5]),
        1.0 - s.eps + s.eps * mc - 150.0 * inflation * (inflation - 1.0)
        + household_sdf * 150.0 * aux_next["Y"] / aux["Y"]
        * next_controls[5] * (next_controls[5] - 1.0),
        math.log(next_state[5] / aux["rr"]),
        math.log(next_state[6] / aux["money"]),
        rl - aux["rr"] - aux["cb"],
        aux["rr"] + (1.0 - aux["rho"]) * aux["cb"]
        - (aux["xi"] - aux["rho"]) * s.zeta * aux["cd"] / 2.0 - rd,
        dot(s.mass, [next_state[2 + i] / rl for i in range(2)])
        - (state[4] / inflation + (1.0 / aux["h"] - 1.0) * aux["money"]),
    ]


def expand_compact_state(s, compact):
    return [compact[0], compact[1], s.pledge[0] * compact[2] * compact[0],
            s.pledge[1] * compact[2] * compact[1], *compact[3:]]


def binding_period_residual(s, state, controls, next_compact, next_controls, innovations):
    next_state = expand_compact_state(s, next_compact)
    aux = auxiliary(s, state, controls, next_state[:2], innovations)
    aux_next = auxiliary(s, next_state, next_controls, next_state[:2], [0.0, 0.0])
    sdf = [s.be * controls[i] / next_controls[i] for i in range(2)]
    result = []
    for i in range(2):
        collateral = s.pledge[i] * next_compact[2]
        result.append(controls[i] + (controls[6] - collateral / controls[8]) * next_state[i] - aux["N"][i])
        result.append(
            controls[6] - collateral / controls[8]
            - sdf[i] * (aux_next["uk"][i] + s.ad * next_controls[6] - collateral / next_controls[5])
        )
    result.append(math.log(next_compact[2] / (s.ad * next_controls[5] * next_controls[6])))
    result.extend(remaining_residuals(s, state, controls, next_state, next_controls, aux, aux_next))
    return result


def prefix_residual(base, p0, branch, intervention, log_coordinates):
    s = base.s
    z = log_coordinates
    x1 = [base.X1[i] * math.exp(z[i]) for i in range(7)]
    u0 = [base.U0[i] * math.exp(z[7 + i]) for i in range(10)]
    x2 = [base.X2[i] * math.exp(z[17 + i]) for i in range(6)]
    u1 = [base.U1[i] * math.exp(z[23 + i]) for i in range(10)]
    tail_log = matvec(p0, z[17:23])
    u2 = [s.base[6 + i] * math.exp(tail_log[6 + i]) for i in range(10)]
    state2 = expand_compact_state(s, x2)
    # Backward compatible: scalar legacy v_R or the exact four-tool
    # (v_R, v_M, v_rho, v_Delta) source initial intervention vector.
    if isinstance(intervention, (tuple, list)):
        if len(intervention) != 4:
            raise ValueError("Expected four date-zero policy instruments.")
        v_rate, v_quantity, v_requirement, v_corridor = intervention
    else:
        v_rate, v_quantity, v_requirement, v_corridor = intervention, 0.0, 0.0, 0.0
    e0 = [base.e0[0] + v_rate, base.e0[1] + v_quantity]
    aux0 = auxiliary(
        s, base.X0, u0, x1[:2], e0,
        rho=s.rho + v_requirement, corridor=s.Delta + v_corridor
    )
    aux1 = auxiliary(s, x1, u1, state2[:2], base.e1)
    aux2 = auxiliary(s, state2, u2, state2[:2], [0.0, 0.0])
    sdf0 = [s.be * u0[i] / u1[i] for i in range(2)]
    result = []
    for i in range(2):
        collateral = s.pledge[i] * s.ad * u1[5] * u1[6]
        result.append(u0[i] + u0[6] * x1[i] - x1[2 + i] / u0[8] - aux0["N"][i])
        if branch == "slack" and i == 1:
            result.append(u0[6] - sdf0[i] * (aux1["uk"][i] + s.ad * u1[6]))
            result.append(math.log(u0[8] * sdf0[i] / u1[5]))
        else:
            result.append(
                u0[6] - collateral / u0[8]
                - sdf0[i] * (aux1["uk"][i] + s.ad * u1[6] - collateral / u1[5])
            )
            result.append(math.log(x1[2 + i] / (collateral * x1[i])))
    result.extend(remaining_residuals(s, base.X0, u0, x1, u1, aux0, aux1))
    result.extend(binding_period_residual(s, x1, u1, x2, u2, base.e1))
    if len(result) != 33:
        raise AssertionError(len(result))
    return result


def decode_prefix(base, p0, z):
    s = base.s
    x1 = [base.X1[i] * math.exp(z[i]) for i in range(7)]
    u0 = [base.U0[i] * math.exp(z[7 + i]) for i in range(10)]
    x2 = [base.X2[i] * math.exp(z[17 + i]) for i in range(6)]
    u1 = [base.U1[i] * math.exp(z[23 + i]) for i in range(10)]
    tail_log = matvec(p0, z[17:23])
    u2 = [s.base[6 + i] * math.exp(tail_log[6 + i]) for i in range(10)]
    return x1, u0, x2, u1, u2


def period_metrics(
    s, state, controls, next_state, next_controls, innovations, branch,
    rho=None, corridor=None,
):
    aux = auxiliary(
        s, state, controls, next_state[:2], innovations,
        rho=rho, corridor=corridor,
    )
    aux_next = auxiliary(s, next_state, next_controls, next_state[:2], [0.0, 0.0])
    _, _, _, marginal_next = production(s, next_state[:2], next_controls)
    sdf = [s.be * controls[i] / next_controls[i] for i in range(2)]
    collateral = [s.pledge[i] * s.ad * next_controls[5] * next_controls[6] for i in range(2)]
    credit = [next_state[2 + i] / controls[8] for i in range(2)]
    slack = [1.0 - next_state[2 + i] / (collateral[i] * next_state[i]) for i in range(2)]
    dual = [1.0 / controls[8] - sdf[i] / next_controls[5] for i in range(2)]
    equity = state[4] / controls[5]
    bank_loans = dot(s.mass, credit)
    deposits = aux["money"] / aux["h"]
    surplus_minus = aux["money"] - aux["rho"] * deposits + (aux["xi"] - aux["rho"]) * (-s.zeta) * deposits
    surplus_plus = aux["money"] - aux["rho"] * deposits + (aux["xi"] - aux["rho"]) * s.zeta * deposits
    nominal_minus = controls[8] * bank_loans + aux["rr"] * aux["money"] - controls[7] * deposits + aux["cm"] * surplus_minus
    nominal_plus = controls[8] * bank_loans + aux["rr"] * aux["money"] - controls[7] * deposits + aux["cp"] * surplus_plus
    za = dot(s.mass, [v ** 10 for v in s.technology])
    effective_output = za ** .1 * dot(s.mass, next_state[:2]) ** .4 * aux_next["L"] ** .5
    interbank_rate = aux["rr"] + aux["corridor"] / (1.0 + math.sqrt(2.0 - controls[9]))
    return {
        "capital_H": state[0], "capital_L": state[1], "capital_next_H": next_state[0],
        "capital_next_L": next_state[1], "credit_H": credit[0], "credit_L": credit[1],
        "consumption_H": controls[0], "consumption_L": controls[1],
        "worker_consumption": controls[2], "wage": controls[3], "input_price": controls[4],
        "total_consumption": controls[2] + dot(s.mass, controls[:2]),
        "output": aux["Y"], "output_H": aux["output_by_type"][0],
        "output_L": aux["output_by_type"][1], "labor": aux["L"],
        "labor_H": aux["labor"][0], "labor_L": aux["labor"][1],
        "capital_adjustment_resources": aux["Gamma"],
        "price_adjustment_resources": aux["Rot"],
        "inflation": controls[5], "capital_price": controls[6],
        "deposit_rate": controls[7], "loan_rate": controls[8],
        "reserve_rate": aux["rr"], "interbank_rate": interbank_rate,
        "tightness": controls[9], "bank_equity": equity, "bank_loans": bank_loans,
        "bank_deposits": deposits, "reserves_pre": aux["money"],
        "loan_deposit_spread": controls[8] - controls[7],
        "conditional_misallocation_loss": math.log(effective_output / aux_next["Y"]),
        "relative_capital_log": math.log(next_state[0] / next_state[1]),
        "investment": aux["inv"], "effective_price_H": controls[6] - collateral[0] / controls[8],
        "effective_price_L": controls[6] - collateral[1] / controls[8],
        "collateral_slack_H": slack[0], "collateral_slack_L": slack[1],
        "collateral_dual_H": dual[0], "collateral_dual_L": dual[1],
        "deposit_cap_slack": 4.0 - deposits / equity,
        "loan_cap_slack": 6.0 - bank_loans / equity,
        "xi_minus_rho": aux["xi"] - aux["rho"],
        "payment_sign_minus": -surplus_minus, "payment_sign_plus": surplus_plus,
        "bank_solvency_minus": nominal_minus / (equity * next_controls[5]),
        "bank_solvency_plus": nominal_plus / (equity * next_controls[5]),
        "bank_gamma_minus_one": controls[8] / controls[7] - 1.0,
        "bank_contraction_gap": 1.0 - (1.0 - s.eta) * controls[8] / controls[7],
        "illustrative_two_M_bond_proxy": 2.0 * s.M - aux["money"],
        "regime": branch,
        "next_marginal_product_H": marginal_next[0],
        "next_marginal_product_L": marginal_next[1],
    }


def build_path(base, p0, f0, z, branch, horizon, date_zero_intervention):
    s = base.s
    x1, u0, x2, u1, _u2 = decode_prefix(base, p0, z)
    rows = []
    state2 = expand_compact_state(s, x2)
    u2_log = matvec(p0, [math.log(x2[i] / base.X2[i]) for i in range(6)])
    u2 = [s.base[6 + i] * math.exp(u2_log[6 + i]) for i in range(10)]
    e0 = [base.e0[0] + date_zero_intervention, base.e0[1]]
    rows.append(period_metrics(s, base.X0, u0, x1, u1, e0, branch))
    rows.append(period_metrics(s, x1, u1, state2, u2, base.e1, "binding"))
    xlog = [math.log(x2[i] / base.X2[i]) for i in range(6)]
    for _t in range(2, horizon + 1):
        ylog = matvec(p0, xlog)
        compact = [base.X2[i] * math.exp(xlog[i]) for i in range(6)]
        controls = [s.base[6 + i] * math.exp(ylog[6 + i]) for i in range(10)]
        next_log = matvec(f0, xlog)
        next_compact = [base.X2[i] * math.exp(next_log[i]) for i in range(6)]
        next_ylog = matvec(p0, next_log)
        next_controls = [s.base[6 + i] * math.exp(next_ylog[6 + i]) for i in range(10)]
        rows.append(period_metrics(s, expand_compact_state(s, compact), controls,
                                   expand_compact_state(s, next_compact), next_controls,
                                   [0.0, 0.0], "binding"))
        xlog = next_log
    return rows, xlog


def recurrent_exact_residuals(base, p0, f0, initial_log, horizon):
    s = base.s
    xlog = list(initial_log)
    maxima = []
    linear_maxima = []
    for _ in range(horizon):
        ylog = matvec(p0, xlog)
        next_log = matvec(f0, xlog)
        next_ylog = matvec(p0, next_log)
        compact = [base.X2[i] * math.exp(xlog[i]) for i in range(6)]
        controls = [s.base[6 + i] * math.exp(ylog[6 + i]) for i in range(10)]
        next_compact = [base.X2[i] * math.exp(next_log[i]) for i in range(6)]
        next_controls = [s.base[6 + i] * math.exp(next_ylog[6 + i]) for i in range(10)]
        exact = binding_period_residual(s, expand_compact_state(s, compact), controls,
                                        next_compact, next_controls, [0.0, 0.0])
        maxima.append(max_abs(exact))
        xlog = next_log
    return maxima


def terminal_decay_table(f0, initial_log, horizons=(20, 40, 80, 160)):
    x = list(initial_log)
    result = {}
    last = max(horizons)
    for step in range(last + 1):
        if step in horizons:
            result[str(step)] = max_abs(x)
        x = matvec(f0, x)
    return result


def bank_dynamic_checks(rows, s):
    """Deterministic finite-law franchise recursion and terminal sensitivity."""
    steady_gamma = s.rate / s.rd
    steady_value = s.eta * steady_gamma / (1.0 - (1.0 - s.eta) * steady_gamma)

    def backward(terminal_value):
        values = [0.0] * (len(rows) + 1)
        values[-1] = terminal_value
        for t in range(len(rows) - 1, -1, -1):
            gamma = rows[t]["loan_rate"] / rows[t]["deposit_rate"]
            values[t] = gamma * (s.eta + (1.0 - s.eta) * values[t + 1])
        return values

    values = backward(steady_value)
    zero_terminal_values = backward(0.0)
    residuals = []
    survival = 1.0
    for t, row in enumerate(rows):
        gamma = row["loan_rate"] / row["deposit_rate"]
        residuals.append(abs(values[t] - gamma * (s.eta + (1.0 - s.eta) * values[t + 1])))
        survival *= (1.0 - s.eta) * gamma
    return {
        "steady_gamma": steady_gamma,
        "steady_value_per_equity": steady_value,
        "value_per_equity_t0": values[0],
        "minimum_value_per_equity": min(values[:-1]),
        "retention_margin_min_value_minus_one": min(v - 1.0 for v in values[:-1]),
        "bellman_recursion_residual_max_abs": max(residuals),
        "homogeneity_residual_V_2e_minus_2V_e": 0.0,
        "terminal_value_sensitivity_at_t0_zero_vs_steady_terminal":
            abs(values[0] - zero_terminal_values[0]),
        "surviving_terminal_coefficient_through_reported_horizon": survival,
        "interpretation": (
            "Checks V_t(e)=v_t e for the deterministic finite-law path.  "
            "It is not the still-open owner-payoff decomposition and dynamic-to-local "
            "optimality transfer; feasibility splicing is proved separately in Lean."
        ),
    }


def validate_margins(rows, branch):
    positive_names = [
        "capital_H", "capital_L", "capital_next_H", "capital_next_L",
        "credit_H", "credit_L", "consumption_H", "consumption_L",
        "worker_consumption", "output", "labor", "inflation", "capital_price",
        "deposit_rate", "loan_rate", "reserve_rate", "interbank_rate", "tightness",
        "bank_equity", "bank_loans", "bank_deposits", "reserves_pre", "investment",
        "effective_price_H", "effective_price_L", "collateral_dual_H",
        "deposit_cap_slack", "loan_cap_slack", "xi_minus_rho",
        "payment_sign_minus", "payment_sign_plus", "bank_solvency_minus",
        "bank_solvency_plus", "bank_gamma_minus_one", "bank_contraction_gap",
        "illustrative_two_M_bond_proxy",
    ]
    minima = {name: min(row[name] for row in rows) for name in positive_names}
    minima["tightness_upper"] = min(1.0 - row["tightness"] for row in rows)
    minima["reserve_to_deposit_rate"] = min(row["deposit_rate"] - row["reserve_rate"] for row in rows)
    minima["deposit_to_loan_rate"] = min(row["loan_rate"] - row["deposit_rate"] for row in rows)
    # The continuation uses B for BOTH firms from date 1 onwards, in
    # either date-0 branch. Previously only H's dual (and L's date-0
    # condition) was checked; this left later L KKT admissibility UNGATED.
    # Here both source complementary variables are required in their
    # active-set locations, without pretending KKT is globally sufficient.
    if len(rows) < 2:
        raise AssertionError("Need at least two dates for recurrent KKT checks")
    kkt_tol = 1e-9
    minima["H_binding_face_all_dates_abs_tolerance"] = (
        kkt_tol - max(abs(row["collateral_slack_H"]) for row in rows)
    )
    minima["L_binding_face_from_date1_abs_tolerance"] = (
        kkt_tol - max(abs(row["collateral_slack_L"]) for row in rows[1:])
    )
    minima["L_strict_funding_dual_from_date1"] = min(
        row["collateral_dual_L"] for row in rows[1:]
    )
    minima["L_complementarity_product_from_date1_tolerance"] = (
        kkt_tol - max(abs(row["collateral_slack_L"] *
                          row["collateral_dual_L"]) for row in rows[1:])
    )
    if branch == "slack":
        minima["date0_L_slack"] = rows[0]["collateral_slack_L"]
        minima["date0_L_dual_abs_tolerance"] = 1e-9 - abs(rows[0]["collateral_dual_L"])
    else:
        minima["date0_L_dual"] = rows[0]["collateral_dual_L"]
        minima["date0_L_slack_abs_tolerance"] = 1e-9 - abs(rows[0]["collateral_slack_L"])
    failures = {name: value for name, value in minima.items() if not value > 0.0}
    return minima, failures


def write_csv(path, branch_paths, baseline_paths):
    metric_names = sorted(branch_paths["slack"][0])
    fields = ["branch", "period", "period_unit"]
    for name in metric_names:
        if name == "regime":
            continue
        fields.extend([name, name + "_baseline", name + "_deviation", name + "_log_deviation_pct"])
    with path.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=fields)
        writer.writeheader()
        for branch, rows in branch_paths.items():
            for t, row in enumerate(rows):
                base = baseline_paths[branch][t]
                out = {"branch": branch, "period": t, "period_unit": "illustrative quarter"}
                for name in metric_names:
                    if name == "regime":
                        continue
                    out[name] = row[name]
                    out[name + "_baseline"] = base[name]
                    out[name + "_deviation"] = row[name] - base[name]
                    out[name + "_log_deviation_pct"] = (
                        100.0 * math.log(row[name] / base[name])
                        if row[name] > 0.0 and base[name] > 0.0 else ""
                    )
                writer.writerow(out)


def write_svg(path, branch_paths, baseline_paths, periods, shock_basis_points):
    panels = [
        ("loan_rate", "Loan rate (bp)", 10000.0, False),
        ("reserve_rate", "Reserve remuneration (bp)", 10000.0, False),
        ("output", "Output (log %, local)", 100.0, True),
        ("credit_H", "H credit (log %)", 100.0, True),
        ("credit_L", "L credit (log %)", 100.0, True),
        ("conditional_misallocation_loss", "Conditional loss (pp)", 100.0, False),
    ]
    width, height = 1080, 720
    margin_x, margin_y, gap_x, gap_y = 65, 55, 45, 55
    panel_w = (width - 2 * margin_x - 2 * gap_x) / 3
    panel_h = (height - 2 * margin_y - gap_y) / 2
    colors = {"slack": "#1769aa", "binding": "#c23b22"}
    lines = [f'<svg xmlns="http://www.w3.org/2000/svg" width="{width}" height="{height}" viewBox="0 0 {width} {height}">',
             '<rect width="100%" height="100%" fill="white"/>',
             '<style>text{font-family:DejaVu Sans,Arial,sans-serif;fill:#222}.title{font-size:14px;font-weight:600}.tick{font-size:10px}.note{font-size:11px}</style>']
    for idx, (name, title, scale, use_log) in enumerate(panels):
        col, row_idx = idx % 3, idx // 3
        x0 = margin_x + col * (panel_w + gap_x)
        y0 = margin_y + row_idx * (panel_h + gap_y)
        series = {}
        for branch in ("slack", "binding"):
            values = []
            for t in range(periods + 1):
                value = branch_paths[branch][t][name]
                base = baseline_paths[branch][t][name]
                values.append(scale * (math.log(value / base) if use_log else value - base))
            series[branch] = values
        bound = max(1e-12, max(abs(v) for values in series.values() for v in values)) * 1.12
        def px(t): return x0 + panel_w * t / periods
        def py(v): return y0 + panel_h * (0.5 - 0.5 * v / bound)
        lines.append(f'<text class="title" x="{x0}" y="{y0 - 12}">{title}</text>')
        lines.append(f'<rect x="{x0}" y="{y0}" width="{panel_w}" height="{panel_h}" fill="none" stroke="#bbb"/>')
        lines.append(f'<line x1="{x0}" y1="{py(0)}" x2="{x0+panel_w}" y2="{py(0)}" stroke="#999" stroke-dasharray="3 3"/>')
        for t in range(0, periods + 1, max(1, periods // 5)):
            lines.append(f'<text class="tick" x="{px(t)}" y="{y0+panel_h+15}" text-anchor="middle">{t}</text>')
        lines.append(f'<text class="tick" x="{x0-6}" y="{py(bound)+4}" text-anchor="end">{bound:.3g}</text>')
        lines.append(f'<text class="tick" x="{x0-6}" y="{py(-bound)+4}" text-anchor="end">{-bound:.3g}</text>')
        for branch in ("slack", "binding"):
            points = " ".join(f"{px(t):.2f},{py(v):.2f}" for t, v in enumerate(series[branch]))
            lines.append(f'<polyline points="{points}" fill="none" stroke="{colors[branch]}" stroke-width="2"/>')
    lines.append(f'<line x1="{width-255}" y1="22" x2="{width-225}" y2="22" stroke="{colors["slack"]}" stroke-width="3"/><text class="note" x="{width-218}" y="26">S: L collateral slack</text>')
    lines.append(f'<line x1="{width-255}" y1="40" x2="{width-225}" y2="40" stroke="{colors["binding"]}" stroke-width="3"/><text class="note" x="{width-218}" y="44">B: L collateral binding</text>')
    lines.append(f'<text class="note" x="65" y="705">Finite-payment internal case; {shock_basis_points:.3g} bp date-0 rule innovation; local-linear recurrent continuation; no empirical calibration.</text>')
    lines.append('</svg>')
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--cache", type=Path, default=DEFAULT_CACHE)
    parser.add_argument("--shock", type=float, default=-1e-5,
                        help="date-0 log reserve-rate rule innovation")
    parser.add_argument("--horizon", type=int, default=160)
    parser.add_argument("--solver-tolerance", type=float, default=2e-12)
    parser.add_argument("--tail-residual-tolerance", type=float, default=1e-7)
    parser.add_argument("--output", type=Path, default=HERE / "finite_irf_output")
    args = parser.parse_args()
    args.output.mkdir(parents=True, exist_ok=True)

    sources = {
        "finite_bridge.py": args.cache / "cierre_interno_2026_10_17/finite_bridge.py",
        "verified_linear_operator.py": args.cache / "cotas_2026_10_15/verified_linear_operator.py",
        "rational_preconditioners.json": HERE / "inputs/rational_preconditioners.json",
    }
    actual_hashes = {name: sha256(path) for name, path in sources.items()}
    if actual_hashes != SOURCE_HASHES:
        raise RuntimeError(f"input hash mismatch: {actual_hashes}")
    matrices = json.loads(sources["rational_preconditioners.json"].read_text(encoding="utf-8"))
    p0 = [[float(value) for value in row] for row in matrices["P0"]]
    f0 = [[float(value) for value in row] for row in matrices["F0"]]
    graph_shape_checks = {
        "P0_rows": len(p0),
        "P0_columns": len(p0[0]) if p0 else 0,
        "F0_rows": len(f0),
        "F0_columns": len(f0[0]) if f0 else 0,
    }
    if graph_shape_checks != {
        "P0_rows": 16, "P0_columns": 6, "F0_rows": 6, "F0_columns": 6
    }:
        raise RuntimeError(f"unexpected stable-graph dimensions: {graph_shape_checks}")

    s = steady_case()
    base = make_boundary(s)
    zero = [0.0] * 33
    baseline_solutions = {}
    shock_solutions = {}
    solver_diagnostics = {}
    for branch in ("slack", "binding"):
        f_base = lambda z, b=branch: prefix_residual(base, p0, b, 0.0, z)
        baseline, history0, jac0 = newton(f_base, zero, tolerance=args.solver_tolerance)
        forcing_step = 1e-6
        forcing = [
            (a - b) / (2.0 * forcing_step)
            for a, b in zip(
                prefix_residual(base, p0, branch, forcing_step, baseline),
                prefix_residual(base, p0, branch, -forcing_step, baseline),
            )
        ]
        tangent, _ = solve_linear(jac0, [-v for v in forcing])
        initial = [baseline[i] + args.shock * tangent[i] for i in range(33)]
        f_shock = lambda z, b=branch: prefix_residual(base, p0, b, args.shock, z)
        shocked, history, jac = newton(f_shock, initial, tolerance=args.solver_tolerance)
        inv_norm, min_pivot = inverse_inf_norm(jac)
        baseline_solutions[branch] = baseline
        shock_solutions[branch] = shocked
        solver_diagnostics[branch] = {
            "baseline_newton_residual_history": history0,
            "shock_newton_residual_history": history,
            "final_prefix_residual_max_abs": max_abs(f_shock(shocked)),
            "numerical_jacobian_inverse_inf_norm": inv_norm,
            "gauss_jordan_min_abs_pivot": min_pivot,
            "prefix_residuals_by_named_row": dict(zip(PREFIX_ROW_NAMES, f_shock(shocked))),
        }

    branch_paths = {}
    baseline_paths = {}
    terminal = {}
    exact_tail_residual = {}
    margins = {}
    failures = {}
    bank_dynamics = {}
    for branch in ("slack", "binding"):
        baseline_paths[branch], _ = build_path(
            base, p0, f0, baseline_solutions[branch], branch, args.horizon, 0.0
        )
        branch_paths[branch], terminal_log = build_path(
            base, p0, f0, shock_solutions[branch], branch, args.horizon, args.shock
        )
        x2_log = [
            math.log(decode_prefix(base, p0, shock_solutions[branch])[2][i] / base.X2[i])
            for i in range(6)
        ]
        exact_residuals = recurrent_exact_residuals(base, p0, f0, x2_log, args.horizon - 1)
        exact_tail_residual[branch] = {
            "maximum_over_reported_path": max(exact_residuals),
            "by_period_from_2": exact_residuals,
            "interpretation": "nonlinear residual left by the local-linear recurrent graph",
        }
        margin_values, margin_failures = validate_margins(branch_paths[branch], branch)
        margins[branch] = margin_values
        failures[branch] = margin_failures
        bank_dynamics[branch] = bank_dynamic_checks(branch_paths[branch], s)
        terminal[branch] = {
            "terminal_state_log_sup_norm": max_abs(terminal_log),
            "decay_from_date_two_by_additional_periods": terminal_decay_table(f0, x2_log),
            "state_log_sup_norm_at_20": max_abs(
                [math.log(branch_paths[branch][20][name] / baseline_paths[branch][20][name])
                 for name in ("capital_H", "capital_L", "bank_equity", "reserve_rate", "reserves_pre")]
            ) if args.horizon >= 20 else None,
        }

    linear_certificate = json.loads(
        (HERE / "inputs/verified_linear_bounds.json").read_text(encoding="utf-8")
    )
    nonlinear_certificate = json.loads(
        (HERE / "inputs/verified_nonlinear_radius.json").read_text(encoding="utf-8")
    )
    numerical_tolerances = {
        "prefix_residual_max_abs": 1e-10,
        "recurrent_nonlinear_residual_max_abs": args.tail_residual_tolerance,
        "active_regime_margin_strict": 0.0,
        "newton_stopping_tolerance": args.solver_tolerance,
    }
    gates = {
        branch: {
            "prefix_residual": solver_diagnostics[branch]["final_prefix_residual_max_abs"]
                < numerical_tolerances["prefix_residual_max_abs"],
            "recurrent_nonlinear_residual": exact_tail_residual[branch]["maximum_over_reported_path"]
                < numerical_tolerances["recurrent_nonlinear_residual_max_abs"],
            "strict_regime_margins": not failures[branch],
            "finite_jacobian_nonsingular": solver_diagnostics[branch]["gauss_jordan_min_abs_pivot"] > 0.0,
            "bank_bellman_recursion": bank_dynamics[branch]["bellman_recursion_residual_max_abs"] < 1e-14,
            "bank_retention": bank_dynamics[branch]["retention_margin_min_value_minus_one"] > 0.0,
        }
        for branch in ("slack", "binding")
    }
    report = {
        "status": "internal_finite_local_linear_irf",
        "public_debt_scope": "Government debt is not calibrated. illustrative_two_M_bond_proxy is a diagnostic only, not a verified household-asset or fiscal closure condition.",
        "scope_limits": [
            "finite atomic payment law only",
            "illustrative parameters; no estimation, calibration or external data",
            "exact nonlinear two-date prefix with audited local-linear recurrent continuation",
            "not a Lean theorem, source receipt, full equilibrium validation or branch selection rule",
            "general source Proposition 3.8 remains open",
        ],
        "period_unit": "one illustrative model quarter",
        "shock": {
            "instrument": "date-0 log reserve-remuneration-rule innovation v_R",
            "value": args.shock,
            "approx_basis_points": 10000.0 * args.shock,
            "later_announcements": "held at the boundary path; v_R is zero from date 1 onward",
        },
        "parameters": {
            "beta_worker": s.bw, "beta_entrepreneur": s.be,
            "risk_aversion_worker": s.sigmaW, "risk_aversion_entrepreneur": s.sigmaE,
            "capital_share": s.alpha, "labor_share": s.beta, "depreciation": s.delta,
            "capital_adjustment_cost": s.phiI, "price_elasticity": s.eps,
            "price_adjustment_cost": 150.0, "reserve_requirement": s.rho,
            "payment_shocks": [-s.zeta, s.zeta], "payment_probabilities": [.5, .5],
            "bank_exit_probability": s.eta, "matching_tightness_steady": s.tight,
            "corridor_width": s.Delta, "productivities": s.technology,
            "pledgeabilities": s.pledge, "masses": s.mass,
            "policy_persistence_reserve_rate": .5, "policy_persistence_reserve_quantity": .5,
            "inflation_rule_coefficient": 1.5, "output_rule_coefficient": .125,
        },
        "input_hashes": actual_hashes,
        "boundary_scalar_root": base.z["R"],
        "solver": solver_diagnostics,
        "numerical_tolerances": numerical_tolerances,
        "numerical_gates": gates,
        "strict_regime_minima": margins,
        "strict_regime_failures": failures,
        "recurrent_nonlinear_residual_diagnostics": exact_tail_residual,
        "terminal_diagnostics": terminal,
        "finite_dynamic_bank_checks": bank_dynamics,
        "stationary_recurrent_residual_max_abs": max_abs(
            binding_period_residual(
                s, expand_compact_state(s, base.X2), s.base[6:], base.X2,
                s.base[6:], [0.0, 0.0]
            )
        ),
        "stable_graph_input_checks": {
            **graph_shape_checks,
            "timing": "P0 maps date-t compact state logs to date-t controls; F0 maps date-t compact state logs to date-(t+1) compact state logs from t=2 onward",
            "expectations": "deterministic aggregate continuation with zero later innovations; the two-point idiosyncratic payment law enters the reduced bank pricing rows, not a simulated aggregate-state expectation tree",
            "selected_eight_step_norm_upper": linear_certificate["selected_eight_step_norm_upper"],
            "state_sixteen_step_norm_upper": linear_certificate["state_sixteen_step_norm_upper"],
            "exact_transition_sixteen_step_norm_upper": linear_certificate["exact_transition_sixteen_step_norm_upper"],
            "exact_graph_entry_error_upper": linear_certificate["exact_graph_entry_error_upper"],
            "rational_expectations_determinacy_established": False,
            "warning": "These checks certify the stored stable local graph used by the experiment. They do not prove Blanchard-Kahn or global rational-expectations determinacy.",
        },
        "equilibrium_correspondence": {
            "nonlinear_prefix": "33 named residuals in 33 positive log unknowns, solved separately for the two active sets",
            "recurrent_tail": "P0/F0 local-linear graph checked against the exact nonlinear recurrent residual at every reported tail date",
            "bank_optimality": "The backward recursion is a numerical evaluation, not proof of policy optimality. Conditional Lean helpers exist in an isolated preliminary campaign; no complete branch equilibrium proof is integrated here.",
            "full_infinite_equilibrium_established": False,
            "open_bridges": [
                "instantiate the actual supported-history policy and its analytic conditions",
                "connect the externally certified reduced exact continuation to literal economic allocation and Lean",
                "full prefix-to-competitive-equilibrium sufficiency and terminality",
                "rational-expectations existence/determinacy and branch selection",
            ],
        },
        "nonlinear_certificate_boundary": {
            "certified_eta_upper_fixed_worst_child": nonlinear_certificate["certified_eta_upper"],
            "certified_eta_upper_endogenous_minimum": nonlinear_certificate["endogenous_minimum_without_fixed_order"]["certified_eta_upper"],
            "warning": "These risk-radius bounds are not a quantitative radius for the date-0 policy shock used here.",
        },
        "branch_selection": "Both active-set solutions are reported conditionally; no averaging or selection rule is imposed.",
    }
    report_path = args.output / "finite_irf_validation.json"
    report_path.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    write_csv(args.output / "finite_irf_paths.csv", branch_paths, baseline_paths)
    write_svg(args.output / "finite_irf_figure.svg", branch_paths, baseline_paths,
              min(args.horizon, 20), 10000.0 * args.shock)
    manifest = {
        "finite_irf_validation.json": sha256(report_path),
        "finite_irf_paths.csv": sha256(args.output / "finite_irf_paths.csv"),
        "finite_irf_figure.svg": sha256(args.output / "finite_irf_figure.svg"),
    }
    (args.output / "SHA256SUMS.json").write_text(
        json.dumps(manifest, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )
    print(json.dumps({
        "shock": args.shock,
        "horizon": args.horizon,
        "final_prefix_residuals": {b: solver_diagnostics[b]["final_prefix_residual_max_abs"] for b in solver_diagnostics},
        "regime_failures": failures,
        "numerical_gates": gates,
        "terminal_state_log_sup_norm": {b: terminal[b]["terminal_state_log_sup_norm"] for b in terminal},
        "output": str(args.output),
    }, indent=2))


if __name__ == "__main__":
    main()
