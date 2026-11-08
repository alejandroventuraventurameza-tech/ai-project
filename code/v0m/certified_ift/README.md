# Quantitative implicit-function arithmetic gate — 33 rows × 5 parameters

**Status: synthetic arithmetic tests PASS; economic-source Jacobian certificate OPEN.**
This directory deliberately separates what has been *executed* from what has
been *proved for the economic model*. Nothing here constitutes a Lean proof,
a calibrated policy IRF, two full equilibria, or a growth result.

## Verified implementation

Run from the repository root:

```bash
python3 -m unittest discover -s code/v0m/certified_ift -p 'test_quantitative_ift.py' -v
python3 code/v0m/certified_ift/check_quantitative_ift.py \
  --certificate PATH/TO/PROVEN_INTERVAL_DATA.json \
  --output PATH/TO/ARITHMETIC_AUDIT.json
```

The CI workflow is `.github/workflows/quantitative-ift-arithmetic.yml`.
It tests **only synthetic** 33×33 interval matrices and a five-parameter
family; it never labels toy inputs as economic enclosures. A failing
five-parameter family now returns exit status **2**, even when the
one-point ball passes. Ill-formed input returns **3**. The report includes
the SHA-256 of input bytes, but not a validation of those bytes' origins.

The arithmetic uses `fractions.Fraction`, converting decimal strings
as exact rational numbers; it prohibits native binary JSON floats.
The requested-domain gate must pass, not just the base-ball gate.

## Mathematical contract

Let (F:\mathbb R^{33}\times\mathbb R^5\to\mathbb R^{33})
be the exact *modified binding-prefix* residual in source log coordinates.
Given a rational center (z_c), state radius (r_z>0), parameter radius
(r_y>0), rational preconditioner (R), and justified interval boxes
enclosing (F(z_c,0)), (D_zF(z,y)), (D_yF(z_c,y)) on the declared domains,
the tool computes rigorous rational **upper bounds**

```text
q   >= sup_(z,y) || I - R DzF(z,y) ||_infty
eta >=             || R F(z_c,0) ||_infty
Ly  >= sup_y       || R DyF(z_c,y) ||_infty
```

A sufficient uniform Banach gate is

```text
q < 1  and  eta + Ly * r_y + q * r_z < r_z .
```

If all input boxes are sound and (F) is C1 on the domain, this
produces a unique fixed point of (T_y(z)=z-RF(z,y)) in the closed
state ball for each permitted parameter vector. Its fixed point is
a zero of (F), as (q<1) forces the square (R) to be invertible.
Moreover (‖D_zF^{-1}‖ <= ‖R‖/(1-q)). The
usual IFT then establishes local C1 dependence on parameters.

For the **literal** `solutionLog 0 = 0` requirement, even a residual
interval containing zero is insufficient: the center must be
(z_c=0) and (F(0,0)=0) must be established *exactly*.

## Actual existing model sources and gaps

Pinned economic/research branch inspected:
`work/lean-ci-validation-otc-20261106`, HEAD before this addition
`40eb8e8b0d3b1223da79caa1f4e2b26cf1c07c48`.

- `lean/checkpoint/modules/Ventura26LiquidityAllocation/EconomicModel.lean`
  defines `LocalReducedPrefixLogJacobianCertifiedAt`,
  `LocalScalarImplicitReduction` and the 33 modified source rows.
- `code/v0m/cierre_interno_2026_10_17/finite_bridge.py`
  computes `J=bd.arr([r.d[:33] for r in residuals])`,
  `inverse=bd.solve(J,bd.eye(33))`, and four policy forcing columns
  at the **initial finite block**, checking pointwise inverse defects.
- `finite_bridge_certificate.json` reports binding residual upper
  `4.05961091301148599112115E-55`, approximate inverse norm upper
  `75.02226161142` and inverse identity defect upper
  `1.84110822798E-35`. These are **pointwise** numerical audit data,
  not uniform 33×33 Jacobian boxes on a five-parameter neighborhood.
- That file reports a negative binding-branch derivative of the L funding
  dual with respect to collateral slack, but `null` for the slack-branch
  counterpart. Do not repurpose the binding certificate for slack.
- `code/v0m/cotas_2026_10_15/verified_nonlinear_radius.json`
  refers to the separate nonlinear history-tree certificate. Its Hessian
  bound must NOT be multiplied into this 33-row finite-node Jacobian
  calculation without proving the two source operators coincide.

**Missing source-linked inputs** to this verifier are a rational
33×33 preconditioner (exportable from the pointwise routine),
a genuine interval enclosure of `D_zF` on the entire product
ball, justified 33×5 `D_yF` boxes, the exact-center residual,
a source-matching coordinate/row map, and nonempty domain radii.
The current legacy JSON contains no such full product-ball arrays.
Producing them is the next substantive computational proof task.

After those inputs, a separate Lean bridge must re-prove the
quantified inequalities for `localBindingResidualWithSlack`,
establish a `solutionLog` witness with normalization and regularity,
and certify the Schur signs. Neither this arithmetic workflow nor
a green general build provides that witness.
