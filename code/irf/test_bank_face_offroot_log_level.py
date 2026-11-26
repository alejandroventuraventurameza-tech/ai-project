#!/usr/bin/env python3
"""Exact off-root bank-face level/log bridge: 33-direction regression.

A(z), D(z)>0 are independent affine test functions. The identities tested
are pure calculus, NOT a claim that these functions are SOURCE primitives.
This catches the false extension dF=D*dG away from a common root.
"""
import math
import random

DIM=33
SEED=20261111

def dot(a,z):
    return sum(x*y for x,y in zip(a,z))

def evaluate(z, a0, d0, ag, dg):
    A=a0+dot(ag,z)
    D=d0+dot(dg,z)
    if min(A,D)<=0:
        raise ValueError("Off positive chart")
    F=A-D
    G=math.log(A/D)
    return A,D,F,G

def main():
    rng=random.Random(SEED)
    maximum_value_error=0.0
    maximum_gradient_error=0.0
    maximum_finite_difference_error=0.0
    max_wrong_offroot_error=0.0
    cases=0
    for trial in range(24):
        # Positive chart: small affine slopes and z coordinates.
        a0=rng.uniform(1.1,2.2)
        d0=a0 if trial%3==0 else rng.uniform(0.8,2.5)
        ag=[rng.uniform(-0.03,0.03) for _ in range(DIM)]
        dg=[rng.uniform(-0.03,0.03) for _ in range(DIM)]
        z=[0.0]*DIM if trial%3==0 else [rng.uniform(-0.3,0.3) for _ in range(DIM)]
        A,D,F,G=evaluate(z,a0,d0,ag,dg)
        # A/D may be close to one. expm1 improves numerical stability.
        identity_error=abs(F-D*math.expm1(G))
        maximum_value_error=max(maximum_value_error,identity_error)
        assert identity_error<5e-14
        for j in range(DIM):
            analytic_F=ag[j]-dg[j]
            analytic_G=ag[j]/A-dg[j]/D
            offroot_rhs=math.expm1(G)*dg[j]+D*math.exp(G)*analytic_G
            gradient_error=abs(analytic_F-offroot_rhs)
            maximum_gradient_error=max(maximum_gradient_error,gradient_error)
            assert gradient_error<2e-14
            h=1e-5
            zp=z.copy(); zm=z.copy()
            zp[j]+=h; zm[j]-=h
            _,_,Fp,Gp=evaluate(zp,a0,d0,ag,dg)
            _,_,Fm,Gm=evaluate(zm,a0,d0,ag,dg)
            numeric_F=(Fp-Fm)/(2*h)
            numeric_G=(Gp-Gm)/(2*h)
            finite_error=max(abs(numeric_F-analytic_F),abs(numeric_G-analytic_G))
            maximum_finite_difference_error=max(maximum_finite_difference_error,finite_error)
            assert finite_error<2e-9
            # Root-only simplification dF=D*dG is valid at F=G=0.
            if trial%3==0:
                assert abs(analytic_F-D*analytic_G)<2e-14
            else:
                max_wrong_offroot_error=max(max_wrong_offroot_error,
                    abs(analytic_F-D*analytic_G))
            cases+=1
    # Off-root correction is genuinely nonzero in this experiment.
    assert max_wrong_offroot_error>1e-5
    print("PASS: exact bank-face positive-domain off-root identity and all 33 derivatives")
    print(f"Cases={cases}; max value error={maximum_value_error:.3e}; "
          f"gradient error={maximum_gradient_error:.3e}; "
          f"finite-difference error={maximum_finite_difference_error:.3e}; "
          f"omitted off-root term witness={max_wrong_offroot_error:.3e}")
    print("Scope: algebra/calculus synthetic test only; not SOURCE/Python economic operator equivalence.")

if __name__=="__main__":
    main()
