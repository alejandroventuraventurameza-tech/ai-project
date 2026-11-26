import Ventura26LiquidityAllocation.SourceReserveRulesLogRatioBridgeCandidate

/-!
# Exact off-root nonlinear normalization map for three genuine SOURCE rows

Earlier candidates proved positive-domain zero-set equivalence and
directional derivatives at roots. This module provides stronger,
OFF-ROOT function-value identities for the three actual
SOURCE remaining rows with original-Python logarithmic counterparts:

  Py_bank  = log(1 + SRC_bank / bankTarget),
  Py_labor = log(1 + SRC_labor / laborTarget),
  Py_Euler = log(1 - SRC_Euler).

These identities are exact in real arithmetic on positive economic
charts. In particular the full nonlinear row transformation depends
on endogenous bank/labor target denominators; a constant diagonal
rescaling is justified only in the Jacobian at a common root, not
as an off-root functional identity.

Theorems DO NOT identify original Python 33 economic inputs, calibrate
the full operator, prove SOURCE roots or derive interval bounds.
-/

namespace Ventura26LiquidityAllocation

/-- Any nonzero denominator gives the exact nonlinear
logarithmic normalization of a level-difference residual. -/
theorem sourceLogRatio_eq_logOnePlusLevel
    (A B : ℝ) (hB : B ≠ 0) :
    Real.log (A / B) =
      Real.log (1 + (A - B) / B) := by
  have hid : 1 + (A - B) / B = A / B := by
    field_simp [hB] <;> ring
  rw [hid]

#print axioms sourceLogRatio_eq_logOnePlusLevel

/-- The Euler original SOURCE `1-A/B` and Python `log(A/B)`
are related OFF ROOT, not only at economic zeros. -/
theorem sourceLogRatio_eq_logOneMinusEuler
    (A B : ℝ) :
    Real.log (A / B) =
      Real.log (1 - (1 - A / B)) := by
  have hid : 1 - (1 - A / B) = A / B := by ring
  rw [hid]

#print axioms sourceLogRatio_eq_logOneMinusEuler

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- The ACTUAL SOURCE bank-face row exactly produces the original
Python-shaped log ratio through a nonlinear normalization of its
level residual, at every off-root point with positive rollover target. -/
theorem sourceBankFace_actual_offRootLogTransformation
    (P : Primitives S) (d : LocalPrefixDateData)
    (hB : 0 <
      bankRenewalFactor P * d.controls.loanRate *
        d.currentBankFace / d.controls.inflation) :
    Real.log (d.nextBankFace /
        (bankRenewalFactor P * d.controls.loanRate *
          d.currentBankFace / d.controls.inflation)) =
      Real.log (1 +
        localReducedRemainingResidual P d (0 : Fin 11) /
          (bankRenewalFactor P * d.controls.loanRate *
            d.currentBankFace / d.controls.inflation)) := by
  change Real.log (d.nextBankFace /
      (bankRenewalFactor P * d.controls.loanRate *
        d.currentBankFace / d.controls.inflation)) =
    Real.log (1 + (d.nextBankFace -
      bankRenewalFactor P * d.controls.loanRate *
        d.currentBankFace / d.controls.inflation) /
          (bankRenewalFactor P * d.controls.loanRate *
            d.currentBankFace / d.controls.inflation))
  exact sourceLogRatio_eq_logOnePlusLevel _ _ (ne_of_gt hB)

#print axioms sourceBankFace_actual_offRootLogTransformation

/-- The ACTUAL SOURCE labor-supply level residual equals
the original Python-shaped log wage/target after the exact
nonlinear positive-target transformation, OFF ROOT. -/
theorem sourceLabor_actual_offRootLogTransformation
    (P : Primitives S) (d : LocalPrefixDateData)
    (hB : 0 <
      P.laborScale * d.controls.workerConsumption ^ P.workerRiskAversion *
        localPrefixAggregateLabor P d ^ P.laborCurvature) :
    Real.log (d.controls.wage /
        (P.laborScale * d.controls.workerConsumption ^
          P.workerRiskAversion *
          localPrefixAggregateLabor P d ^ P.laborCurvature)) =
      Real.log (1 + localReducedRemainingResidual P d (3 : Fin 11) /
        (P.laborScale * d.controls.workerConsumption ^
          P.workerRiskAversion *
          localPrefixAggregateLabor P d ^ P.laborCurvature)) := by
  change Real.log (d.controls.wage /
      (P.laborScale * d.controls.workerConsumption ^
        P.workerRiskAversion *
        localPrefixAggregateLabor P d ^ P.laborCurvature)) =
    Real.log (1 + (d.controls.wage -
      P.laborScale * d.controls.workerConsumption ^
        P.workerRiskAversion *
        localPrefixAggregateLabor P d ^ P.laborCurvature) /
      (P.laborScale * d.controls.workerConsumption ^
        P.workerRiskAversion *
        localPrefixAggregateLabor P d ^ P.laborCurvature))
  exact sourceLogRatio_eq_logOnePlusLevel _ _ (ne_of_gt hB)

#print axioms sourceLabor_actual_offRootLogTransformation

/-- The ORIGINAL SOURCE household deposit Euler equation `1-ratio`
transforms exactly into the original Python-shaped `log(ratio)`
under the real-log normalization, OFF ROOT. -/
theorem sourceDepositEuler_actual_offRootLogTransformation
    (P : Primitives S) (d : LocalPrefixDateData) :
    Real.log (
      ((P.workerDiscount *
        crraMarginal P.workerRiskAversion d.nextControls.workerConsumption /
          crraMarginal P.workerRiskAversion d.controls.workerConsumption) *
          d.controls.depositRate) /
          d.nextControls.inflation) =
      Real.log (1 - localReducedRemainingResidual P d (4 : Fin 11)) := by
  change Real.log (
      ((P.workerDiscount *
        crraMarginal P.workerRiskAversion d.nextControls.workerConsumption /
          crraMarginal P.workerRiskAversion d.controls.workerConsumption) *
          d.controls.depositRate) /
          d.nextControls.inflation) =
    Real.log (1 - (1 -
      ((P.workerDiscount *
        crraMarginal P.workerRiskAversion d.nextControls.workerConsumption /
          crraMarginal P.workerRiskAversion d.controls.workerConsumption) *
          d.controls.depositRate) /
          d.nextControls.inflation))
  exact sourceLogRatio_eq_logOneMinusEuler _ _

#print axioms sourceDepositEuler_actual_offRootLogTransformation

end Ventura26LiquidityAllocation
