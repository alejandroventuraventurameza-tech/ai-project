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

## Critical row-5 source-operator conversion

The old finite-node **binding** Jacobian uses row 5
`g_log(z)=log(face_L(z)/collateral_L(z))`
(in `finite_bridge.py`), whereas the current exact Lean source uses
`g_mod(z,s)=1-face_L(z)/collateral_L(z)-s`
(in `EconomicModel.lean:localBindingResidualWithSlack`).
At the boundary `face_L/collateral_L=1`, both are zero for `s=0`,
but their **state derivatives are negatives**:
`D_z g_mod = -D_z g_log`; the **direct slack derivative** of the Lean row
is `-1`.

For **point Jacobians only**, set `D=diag(1,...,-1 at row 5,...)`.
Then `J_source=D*J_legacy` and the point preconditioner transforms as
`R_source=R_legacy*D`; hence
`R_source*J_source=R_legacy*J_legacy`.
The executable `source_row5_transform.py` implements that rational
row/column sign transformation, and `test_source_row5_transform.py`
tests its identity on a synthetic 33-dimensional system.

**DO NOT** treat this as a uniform nonlinear enclosure. Away from
coverage ratio one, the two different residuals are not related by
a constant row-sign flip. The true product-ball Jacobian still must
be evaluated and enclosed from the Lean-modified residual itself,
including the four direct monetary policy derivatives and the
prescribed-slack direction in the exact order `(s,v_R,v_M,v_rho,v_Delta)`.


## Augmented 34-by-34 boundary-zero audit (conditional)

The previous numerical model returned a tiny *enclosed* residual at its
nominal reference, **not** the exact equation `mu_L(0,0)=0`.
To avoid confusing a near-zero residual with a normalized exact zero,
`audit_augmented_34.py` frees the reserve-remuneration innovation
`h=v_R` as a 34th unknown and adds the original normalized L funding
dual as a 34th equation:

```text
H(z,h) := (F_binding_modified(z, (0,h,0,0,0)), mu_L(z))
```

The producer now exports `funding_dual_center_box` from the actual
point interval-AD expression; the uniform derivative boxes already
include `Dz mu_L`. The script forms a rational approximate 34x34
block inverse from the existing 33x33 preconditioner and nominal
Schur complement, then **independently** encloses its full defect
against the *uniform* interval Jacobian. It uses weighted sup norm
radii `r_z=1e-10` and `r_h=1e-15`, exactly matching the
producer's current domain.

Execute the source audit with the existing
`.github/workflows/finite-source-point-export.yml` workflow.
The ten toy regressions run in
`.github/workflows/quantitative-ift-arithmetic.yml`.
The executed candidate passed at
[42447037264](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/42447037264):
`q ~ 0.004156677924539059` and `eta ~ 3.54434692385473e-41`.
The exact fractions and source input SHA-256 are in the retained
`binding_augmented34_arithmetic_CANDIDATE.json` artifact.

**Conditional theorem:** For a genuinely C1 source operator enclosed
by the supplied boxes on the anisotropic rectangle, `q<1` and
`eta+q<1` yield a unique exact zero `(z*,h*)` in that rectangle.
This does **not** prove `h*=0` or `F(0,0)=0`; it only supports a
recentered base whose monetary reference may have shifted.
The quantitative radius `1e-15` in `h` cannot justify IRFs at
`v_R=-1e-5`. Full Python-to-Lean semantic identity, source C1,
an exact Lean IFT witness, agent sufficiency, and a complete dynamic
equilibrium are all **pending**, as recorded in
`docs/PUENTE_REDUCIDO_EQUILIBRIO.md`.
