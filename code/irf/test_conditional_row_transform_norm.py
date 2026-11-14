#!/usr/bin/env python3
"""Dependency-free structural regression for the conditional 33-row transform.

This test checks algebra on deliberately varied diagonals/shears only.
It never invokes SOURCE residuals or asserts an equilibrium certificate.
"""
import math
import random

N=33

def multiply(A,B):
    return [[sum(A[i][k]*B[k][j] for k in range(N)) for j in range(N)]
            for i in range(N)]

def inorm(A):
    return max(sum(abs(x) for x in row) for row in A)

def identity_error(A):
    return max(abs(A[i][j]-(1.0 if i==j else 0.0))
               for i in range(N) for j in range(N))

def matrices(diag, a_h, a_l):
    T=[[0.0]*N for _ in range(N)]
    Ti=[[0.0]*N for _ in range(N)]
    for i,d in enumerate(diag):
        T[i][i]=d
        Ti[i][i]=1.0/d
    T[19][21]=-a_h*diag[21]
    T[20][21]=-a_l*diag[21]
    Ti[19][21]=a_h/diag[19]
    Ti[20][21]=a_l/diag[20]
    return T,Ti

def closed_norm(diag,a_h,a_l):
    return max((1+abs({19:a_h,20:a_l}[i]))/abs(d) if i in (19,20)
               else 1/abs(d) for i,d in enumerate(diag))

def main():
    rng=random.Random(20261111)
    max_error=0.0
    for trial in range(32):
        diag=[(-1 if rng.random()<0.5 else 1)*10**rng.uniform(-1.5,1.5)
              for _ in range(N)]
        # The model currently uses lambda19=lambda20=1, but the general
        # algebra must not rely on those values accidentally.
        a_h=rng.uniform(-2,2)
        a_l=rng.uniform(-2,2)
        T,Ti=matrices(diag,a_h,a_l)
        error=max(identity_error(multiply(T,Ti)),
                  identity_error(multiply(Ti,T)))
        max_error=max(max_error,error)
        assert error<1e-11,(trial,error)
        measured=inorm(Ti)
        analytic=closed_norm(diag,a_h,a_l)
        assert math.isclose(measured,analytic,rel_tol=1e-13,
                            abs_tol=1e-13),(trial,measured,analytic)
        assert inorm(T)*measured>=1-1e-12
    print("PASS: 32 synthetic candidate inverses, row norms and condition bounds;"
          f" maximum identity residual {max_error:.3g}.")
    print("Scope: algebraic candidate only; SOURCE Jacobian and equilibrium NOT certified.")

if __name__=="__main__":
    main()
