#!/usr/bin/env python3
"""Exact rational test of the SOURCE 33-row banking shear structure.

Coefficients are deliberately synthetic. No SOURCE equilibrium, Jacobian
inverse, Python/SOURCE functional bridge, or economic calibration is certified.
"""
from fractions import Fraction as Q
from random import Random

N = 33

def make_shear(values):
    loan0, deposit0, loan1, deposit1, rate0, quantity0, rate1, quantity1 = values
    A = [[Q(int(i == j)) for j in range(N)] for i in range(N)]
    for row, col, coef in ((14, 12, loan0), (15, 12, deposit0),
                           (16, 12, rate0), (16, 13, quantity0),
                           (30, 28, loan1), (31, 28, deposit1),
                           (32, 28, rate1), (32, 29, quantity1)):
        A[row][col] += coef
    return A

def matmul(A, B):
    return [[sum((A[i][k] * B[k][j] for k in range(N) if A[i][k]), Q(0))
             for j in range(N)] for i in range(N)]

def identity(A):
    return all(A[i][j] == Q(int(i == j)) for i in range(N) for j in range(N))

def norm_inf(A):
    return max(sum(map(abs, row), Q(0)) for row in A)

def run():
    rng = Random(20261126)
    cases = [tuple(Q(0) for _ in range(8)),
             (Q(-2), Q(3,2), Q(-7,3), Q(0), Q(5), Q(-5), Q(8,7), Q(-1,9))]
    for _ in range(10):
        cases.append(tuple(Q(rng.randint(-9,9), rng.randint(1,9))
                           for _ in range(8)))
    for coeffs in cases:
        E = make_shear(coeffs)
        Einv = make_shear(tuple(-x for x in coeffs))
        assert identity(matmul(E, Einv))
        assert identity(matmul(Einv, E))
        l0, d0, l1, d1, r0, q0, r1, q1 = coeffs
        exact_norm = Q(1) + max(abs(l0), abs(d0), abs(r0)+abs(q0),
                                abs(l1), abs(d1), abs(r1)+abs(q1))
        assert norm_inf(Einv) == exact_norm
    print("PASS: 12 synthetic exact-rational 33x33 SOURCE row-shear inverses and infinity norms")
    print("SCOPE: structural algebra only; no economic SOURCE root or Jacobian certificate")

if __name__ == "__main__":
    run()
