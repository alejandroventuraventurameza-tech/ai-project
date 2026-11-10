# SOURCE: exact-integer interval calculation and Lean proof ledger

**Source and version:** `work/lean-ci-validation-otc-20261106`, numerical script initially added in `882c77706225f30c00c6677f2b5829ad207ec66d`, numerical workflow updated in `64b20eec2c87ff8efe1ebe147b04b9fea70b70ff`, and Lean interval bridge proposed in `24b0ef0eaf96b5c7e87196d2962072a10ecc0e74`.

**Do not conflate:** `NUMERICO EXACTO` means rigorously outward-rounded *arithmetic on an independent translation of the model formulas*. `DEMOSTRADO LEAN` additionally requires proofs that these expressions and inequalities are exactly the original SOURCE terms in the Lean kernel. A CI green check on the Python script establishes the former, **not** the latter.

## Financial claim

The source's date-zero nominal-face consistency can be written

```text
Delta_Face = RD[-1] * D_household[-1]
             - sum_i mass_i * F_firm_i[-1]
             - RR[-1] * reservesPost[-1]
             + RF[-1] * facilityBorrowing[-1]
             + F_bank[-1] / renewalFactor.
```

The government-bond payment cancels on the two sides of the original equation. The SOURCE carrier satisfies `InheritedNominalFaceConsistency` iff its `Delta_Face` is **zero**, given positive bank renewal factor. This exact equivalence and the conditional impossibility of a full competitive equilibrium if `Delta_Face ≠ 0` are already Lean-certified in commit `ca95dd269207f7bf781435cf7c271758d8e6c801` (focused gate #42727586055, all-candidates audit #42727577042).

## Independent exact-integer enclosure

Code: `scripts/audit_source_inherited_nominal_faces_exact_intervals.py`. Successful GitHub Actions run: [#42741556652](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/42741556652).

The program uses rational endpoints internally represented as enclosing multiples of `10^-42`. Each addition, subtraction, multiplication and division performs outward rounding with **integers**. Fractional powers are bounded by binary-searching integer `q`th roots and proving the `y^q` comparison with exact integers. There are no floating-point operations in the certificate. The program independently transcribes the SOURCE bank and real quantities and checks its answer against the earlier 70-digit Decimal reconstruction.

| Quantity | Rigorous outward interval from independently translated formulas |
|---|---|
| Candidate root bracket | `1029135/1000000 ≤ R ≤ 1029136/1000000` |
| Resource residual at 1.029135 | `[-0.000028894789729426872529, -0.000028894789729426872528]` |
| Resource residual at 1.029136 | `[0.000007245939064546064514, 0.000007245939064546064515]` |
| Initial inherited-face gap, uniform over bracket | `[0.082885242451942429580652, 0.082962664157610490221170]` |
| Parent stationary face gap | within `[-10^-24, +10^-24]` |

**Result (`NUMERICO EXACTO`):** the transcribed resource function crosses zero across the rational bracket. The transcribed face gap is strictly bounded between 0.08 and 0.09 at every real rate in that interval, not merely at a midpoint. The Lean model already has a monotone resource function and a unique broad-bracket SOURCE root, so importing these inequalities as kernel proofs would establish the exclusion of the current inherited-state witness.

## Separate kernel obligations

The source-side Lean module `BoundaryInheritedFaceIntervalBridgeCandidate.lean` states a **conditional theorem**, not a new assumption-free incompatibility result. It uses pre-existing Lean monotonicity and root uniqueness to narrow the SOURCE root, provided the two endpoint signs for the original `boundaryResourceResidual` are demonstrated. A second conditional theorem uses a uniform 0.08 lower bound for the **original** `inheritedNominalFaceGap` to derive the no-equilibrium conclusion.

Remaining to prove *inside Lean*:

1. `boundaryResourceResidual (1029135 / 1000000) < 0`.
2. `0 < boundaryResourceResidual (1029136 / 1000000)`.
3. `∀ R ∈ [1029135/1000000, 1029136/1000000], 0.08 < inheritedNominalFaceGap (boundaryPrimitives G R) (boundaryInitialState G R)`.

No one may replace any of these with a `sorry`, `axiom`, an unchecked JSON, an unproved `native_decide`, or a numerical estimate and then claim kernel-certified impossibility.

## Economic repair and next steps

The initial state of an unanticipated monetary-policy intervention must be predetermined. The existing `boundaryInitialState G R` changes entrepreneurial face claims, capital and bank face with `R`, which makes it unsuitable as an unchanged initial state across the counterfactual. Once the exact obstruction is certified, retain this result as a **negative audit** of that candidate; rebuild the intervention using a common initial state, not an ad hoc adjustment of inherited household deposits. Prove budget flows, population-level bank feasibility, private optimality and TVCs for any new candidate before labeling it an equilibrium or claiming causal long-run growth effects.
