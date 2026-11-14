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
## Reproduced candidate numbers (Python verification job; 2026-11-14)

The code/verify.py job 132568704888 of GitHub Actions build #43634657181 completed successfully on source commit 095659116b8420989a138d9bb9dbff8923d1562a. Its stdout reported the following exact-Fraction-derived quantities (decimal displays are approximations):

- 33x33 rational reference Neumann defect: 2.79684733361678e-10.
- 34x34 rational reference Neumann defect: 2.8881849479728e-10.
- Original inverse-only conditional uniform entry tolerance: 7.957357478193563e-05.
- NEW joint inverse-and-negative-Schur tolerance: 1.989339369548391e-05.
- Upper Schur value valid inside this hypothetical same-coordinate ball: -1.1598717884709056.
- Unperturbed rational-reference Schur interval: [-4.212023236694934, -4.212023198052517].

The full build's other jobs are independent checks. These numbers are classified EXACT RATIONAL CONDITIONAL on the rounded forward-AD matrix, NOT a verified SOURCE derivative/root certificate. The bound makes no claim about unknown SOURCE/Python transformation error.


## Conditional 34-dimensional SOURCE root-box budget (audit pending)

The root-existence obligation now has an explicit Banach fixed-point gate rather than a numerical-root assertion. Let F denote the actual SOURCE 34-equation residual, evaluated in EXACTLY the same ordering, variables, and residual normalization as the rationalized Python AD reference Jq. Choose a candidate centre w0 and a closed sup-norm ball B_R of radius R entirely inside a single smooth SOURCE chart and fixed economic regime.

Let C34 be the exact rational approximate inverse, q=||I-C34*Jq||_infinity<1, and nC=||C34||_infinity. Assume that an INDEPENDENT validated SOURCE evaluation proves, for every w in B_R:

    max_ij |DF(w)[i,j]-Jq[i,j]| <= epsilon
    delta = q + 34*nC*epsilon < 1.

Then the map G(w)=w-C34*F(w) contracts the ball with Lipschitz constant at most delta. If a separately validated SOURCE centre residual satisfies

    ||F(w0)||_infinity < (1-delta)*R/nC,

then G maps B_R into itself, and Banach yields a unique zero in that box, given complete-domain regularity. The same epsilon may be the stricter previously audited budget preserving invertibility and negative Schur sign throughout the box.

The rational auditor now computes exact conditional root residual budgets for R = 1/1000000, 1/100000, and 1/10000, using exactly the same 34x34 preconditioner and Schur-sign radius. Their numerical values must be read from an audited run.

MISSING SOURCE INPUTS: (i) actual centre residual F(w0), with directed or certified absolute enclosure; (ii) uniform derivative enclosure of DF over the WHOLE box, in matching coordinates; (iii) chart smoothness including the continuation-tail derivative; (iv) regime validity and all positive denominators over the box; (v) a source/native representation of the centre. Python forward AD or a small floating residual cannot fill these obligations.

The regression script test_schur_sign_perturbation_bound.py also checks the exact root-budget algebra on a synthetic 2x2 map and rejects a non-contraction case. This is not a SOURCE numerical execution or a proof of a complete dynamic competitive equilibrium.
