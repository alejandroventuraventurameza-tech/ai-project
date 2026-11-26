#!/usr/bin/env python3
"""Exact rational 33x33 Neumann perturbation regression.

Tests only a synthetic matrix pair, not economic SOURCE/Python Jacobians.
All computations use fractions.Fraction; no floating-point threshold.
"""
from fractions import Fraction as Q

N=33
def zero():
    return [[Q(0) for _ in range(N)] for _ in range(N)]

def eye():
    a=zero()
    for i in range(N):
        a[i][i]=Q(1)
    return a

def matmul(a,b):
    result=zero()
    for i in range(N):
        for k in range(N):
            if a[i][k]:
                for j in range(N):
                    if b[k][j]:
                        result[i][j]+=a[i][k]*b[k][j]
    return result

def infnorm(a):
    return max(sum(abs(x) for x in row) for row in a)

def assert_identity(a):
    ident=eye()
    assert a==ident,"Exact inverse identity failed"

def example():
    # Synthetic nonsingular M=(I+K)D, with sparse K^2=0.
    d=[Q(i+10,10) for i in range(N)]
    K=zero()
    K[19][21]=-Q(1,10)
    K[20][21]=Q(1,8)
    assert matmul(K,K)==zero()
    M=zero()
    Minv=zero()
    for i in range(N):
        M[i][i]=d[i]
        Minv[i][i]=1/d[i]
    for i in (19,20):
        M[i][21]=K[i][21]*d[21]
        Minv[i][21]=-K[i][21]/d[i]
    assert_identity(matmul(M,Minv))
    assert_identity(matmul(Minv,M))
    return M,Minv

def perturbation(magnitude):
    E=zero()
    for i in range(N):
        E[i][i]=magnitude
    E[19][21]=magnitude/2
    E[20][21]=-magnitude/3
    return E

def add(a,b):
    return [[a[i][j]+b[i][j] for j in range(N)] for i in range(N)]

def test():
    M,Minv=example()
    inverse_norm=infnorm(Minv)
    assert inverse_norm>0
    good_E=perturbation(Q(1,100))
    good_q=infnorm(matmul(Minv,good_E))
    assert Q(0)<good_q<Q(1)
    bound=inverse_norm/(1-good_q)
    assert bound>=inverse_norm
    assert bound*(1-good_q)==inverse_norm
    # Larger error defeats the sufficient test; never infer singularity.
    bad_E=perturbation(Q(100,1))
    bad_q=infnorm(matmul(Minv,bad_E))
    assert bad_q>=1
    # A failed sufficient condition is not evidence of singularity:
    # E = +100 I gives a strictly row-diagonally dominant M+E.
    diag_E=zero()
    for i in range(N):
        diag_E[i][i]=Q(100)
    assert infnorm(matmul(Minv,diag_E))>=1
    shifted=add(M,diag_E)
    for i in range(N):
        assert abs(shifted[i][i])>sum(abs(shifted[i][j])
                                     for j in range(N) if j!=i)
    # True singularity is possible when E=-M; q>=1 in that case.
    minus_M=[[-x for x in row] for row in M]
    assert add(M,minus_M)==zero()
    assert infnorm(matmul(Minv,minus_M))==1
    print("PASS: exact 33x33 inverse and rational Neumann bounds")
    print("good q = %s; inverse bound = %s" % (good_q,bound))
    print("negative controls: q>=1 permits both invertible and singular cases")
    print("SCOPE: synthetic rational regression only; no SOURCE Jacobian certificate")

if __name__=="__main__":
    test()
