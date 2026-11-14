# SOURCE 34: rational uniform Schur-sign perturbation certificate

14 November 2026. This is an EXACT RATIONAL CONDITIONAL bound, NOT a verified SOURCE derivative enclosure.
Reference: code/irf/audit_frozen_python_34_ad_rational_gate.py.

## The matrix and its representation

The 34x34 nominal matrix Jq consists of exact Fraction coefficients obtained by decimal rounding of the float64 forward-AD Jacobian of finite_irf.py. Its block partition is Jq = [[Aq,bq],[cq,0]], with Aq of size 33x33.

The target hypothetical real matrix H must be expressed in precisely the SAME unknowns, output ordering and residual normalization as Jq and satisfy the ENTRYWISE inequality |H_ij-Jq_ij| <= epsilon. This comparison is NOT yet established for the genuine SOURCE derivative: the Lean SOURCE-to-Python INDEX permutation is not a cross-language semantic identity between all SOURCE and finite_irf.py equations.

## Exact Neumann inequalities

Let C33 and C34 be rational approximate inverse matrices. Define q33=||I-C33*Aq||_infinity<1, q34=||I-C34*Jq||_infinity<1, n33=||C33||_infinity, n34=||C34||_infinity. For any H satisfying the same-coordinate entrywise epsilon ball:

delta33 = q33 + 33*n33*epsilon; delta34 = q34 + 34*n34*epsilon.

If both are strictly below one, the 33x33 and 34x34 blocks of H are invertible, and ||A_H^(-1)||_infinity <= K = n33/(1-delta33). This follows from Neumann-series bounds, with all displayed quantities evaluated as exact rational numbers after input rationalization.

## Simultaneous perturbation of the scalar Schur complement

Let u0 be an exact rationalized approximate solution of Aq*u0+bq=0, with rational residual rho=||Aq*u0+bq||_infinity, U=||u0||_infinity and C=||cq||_1. For actual H, define uH=-A_H^(-1)*b_H and sH=d_H+c_H*uH (the Schur complement). The whole-matrix entrywise bound implies:

||uH-u0||_infinity <= Eu = K*(rho+epsilon*(33*U+1)).

|sH-cq*u0| <= Es = epsilon + C*Eu + 33*epsilon*(U+Eu).

The first epsilon also allows the last-row policy derivative d_H to vary; it need not equal zero in an arbitrary H. Therefore, if cq*u0+Es < 0, the Schur complement sH is strictly negative for ALL matrices H in that common entrywise ball, and both A_H and H are invertible.

The script finds a strict rational radius by repeatedly halving the inverse-only radius until delta33<1, delta34<1 and the Schur upper bound is negative. It writes conditional_joint_inverse_and_negative_schur_entry_tolerance and the rational upper and lower Schur bounds to the generated JSON. No numerical threshold should be quoted without an audited run.

## Scope firewall

DEMOSTRADO in Lean: the genuine SOURCE two-collateral-log derivative factorization, rank transport and conditional economic Schur gate at a positive SOURCE root.

EXACT RATIONAL CONDITIONAL: the robust 33/34 inverse and negative Schur bounds for any real matrix within the common entrywise radius of the rationalized Python AD witness.

PENDIENTE: SOURCE/Python semantic derivative and normalization alignment; validated enclosure of the true SOURCE Jacobian; a true SOURCE boundary root; regularity of the actual continuation tail and fixed economic regime; the 33-block SOURCE inverse and the nonzero Schur scalar; IFT, KKT, dynamic equilibrium and long-run growth.

The nominal Python forward AD values are binary64 calculations. Rationalizing their decimal output does NOT enclose the real derivative or prove equilibrium existence.