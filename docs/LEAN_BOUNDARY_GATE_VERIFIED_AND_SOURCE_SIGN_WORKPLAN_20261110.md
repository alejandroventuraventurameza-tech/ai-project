# Lean boundary gate: verified CI and remaining SOURCE sign certificates (2026-11-10)

## Exact checked revision

- Revision tested: `ec25cabb06f1adbb210cafd91dc317108c75422b`.
- Focused boundary run: [#42863798988](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/42863798988), **success**.
- Boundary job: `129996671303`, **success**.
- Both steps `Compile literal boundary root and normalization chain` and `Audit exact frontier theorems without sorryAx` completed successfully.
- Focused paper claims run: [#42863799232](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/42863799232), **success**.
- Build run: [#42863798809](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/42863798809), **success**.
- Editorial QA run: [#42863798886](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/42863798886), **success**.

The boundary workflow compiles `BoundaryFaceGapFiscalReductionCandidate`, including its imports `BoundaryPredeterminedStateCandidate` and the original SOURCE chain. Its axiom audit includes the fiscal-reference reduction and the conditional firm-face lower-bound results, and rejects `sorryAx`. These results are **kernel-checked for their stated (sometimes conditional) hypotheses**, not assumptions-free proofs of the residual signs.

## Mathematical frontier that CI does NOT close

In `BoundaryInheritedFaceIntervalBridgeCandidate.lean`, the following original-SOURCE inequalities are still premises:

1. `boundaryResourceResidual (1029135 / 1000000 : ℝ) < 0`.
2. `0 < boundaryResourceResidual (1029136 / 1000000 : ℝ)`.
3. Uniformly on this rational interval, `(8 / 100 : ℝ) < inheritedNominalFaceGap (boundaryPrimitives 0 R) (boundaryInitialState 0 R)`.

The third obligation has been reduced to the reference fiscal parameter `G = 0` by the previously kernel-proven independence of the inherited-face gap from `G`. This does **not** assert the fiscal reference `G=0` belongs to an admissible full equilibrium domain; it is only an algebraic evaluation point.

The independent exact-integer script `scripts/audit_source_inherited_nominal_faces_exact_intervals.py` supports all three signs for independently translated expressions. It does not produce Lean proof terms for the original expressions.

## Proof-engineering order (no conditional-theorem proliferation)

1. Use existing certified bounds and source definitions in `BoundaryResourceRootCandidate.lean` and `BoundaryNormalizationBridgeCandidate.lean` to derive two endpoint signs. The original residual is `boundaryAggregateOutput R - boundaryWorkerConsumption R - average (boundaryConsumption R) - boundaryCapitalCost R`. Exploit the normalization and rational box lemmas already proved, not a new independent transcription of the model.
2. Prove the narrow uniform nominal-face gap sign on the **original** `boundaryPrimitives`/`boundaryInitialState` terms. The existing `boundaryInheritedGap_eq_face_shifts` decomposes this into the firm contribution and the renewal-adjusted bank face; the bank contribution is strictly negative, so the firm contribution must be bounded carefully rather than omitted.
3. Apply the already certified conditional theorem `noCompetitiveEquilibrium_from_zero_fiscal_reference` once the three kernel premises are discharged.
4. Preserve `BoundaryFrozenInheritanceCandidate`: the counterfactual must retain the same predated capital and bank/firm promises across monetary interventions. Refuting the old SOURCE witness does not establish an alternative infinite-horizon competitive equilibrium, policy effect, or growth theorem.

## Scope discipline

- **DEMOSTRADO LEAN:** exact financial decomposition; independence from fiscal G; sign of the bank-face component on the broad boundary interval; logical reduction to the three sign obligations; frozen-state consistency results, as checked at the identified successful focused gate.
- **NUMERICO EXACTO (separate):** endpoint signs and uniform positive gap over independently translated formulas.
- **PENDIENTE:** original-SOURCE endpoint signs and uniform gap in Lean; constructive positive equilibrium satisfying private optimality, budget feasibility and TVCs; causal long-horizon growth claims.

Do not relabel a conditional lemma, green unrelated CI run or exact-integer Python interval as an unconditional kernel proof.
