import Ventura26LiquidityAllocation.SourcePinnedDateTwoLogIndexP0Candidate

/-!
# Original SOURCE level residuals vs original Python log normalizations

In original `code/irf/finite_irf.py`, `remaining_residuals`
has logarithmic normalizations for the bank-face rollover, labor/wage,
and household deposit Euler rows (0, 3, and 4). The corresponding
ACTUAL SOURCE `localReducedRemainingResidual` uses level differences
for rows 0 and 3, and 1 - ratio for row 4.

Thus SOURCE and Python residuals are NOT LITERALLY equal as real-valued
functions. Under strict positivity, they have equivalent ZERO SETS.
Any Jacobian comparison must also account for the nonconstant,
row-specific derivative scale, rather than asserting identical
Jacobians. We prove exact real algebra and then instantiate the
ACTUAL SOURCE remaining-row expressions.

This file makes NO claim that all 33 original Python formulas, inherited
data, shocks and binary64 operations equal Lean SOURCE expressions.
-/

namespace Ventura26LiquidityAllocation

/-- The exact positive-domain conversion of an economic level
difference into the Python-shaped logarithmic ratio. -/
theorem sourceLevelDifference_zero_iff_logRatio
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    a - b = 0 ↔ Real.log (a / b) = 0 := by
  constructor
  · intro h
    have hab : a = b := sub_eq_zero.mp h
    rw [hab, div_self (ne_of_gt hb)]
    exact Real.log_one
  · intro hlog
    have hratio : a / b = 1 :=
      Real.eq_one_of_pos_of_log_eq_zero (div_pos ha hb) hlog
    exact sub_eq_zero.mpr
      ((div_eq_one_iff_eq (ne_of_gt hb)).mp hratio)

#print axioms sourceLevelDifference_zero_iff_logRatio

/-- SOURCE `1 - ratio` and Python `log ratio` have exactly
the same positive-domain zeros, but OPPOSITE first-order
normalization at a root. -/
theorem sourceOneMinusRatio_zero_iff_logRatio
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    1 - a / b = 0 ↔ Real.log (a / b) = 0 := by
  constructor
  · intro h
    have hratio : a / b = 1 := (sub_eq_zero.mp h).symm
    rw [hratio]
    exact Real.log_one
  · intro hlog
    have hratio : a / b = 1 :=
      Real.eq_one_of_pos_of_log_eq_zero (div_pos ha hb) hlog
    rw [hratio]
    norm_num

#print axioms sourceOneMinusRatio_zero_iff_logRatio

/-- The first ACTUAL SOURCE bank-face remaining row is a level
transition; the original Python remaining residual uses
`log(next_state[4]/(s.aB*rl*state[4]/inflation))`.
The following is the precise positive-domain SOURCE zero-set
conversion BEFORE the additional SOURCE/Python parameter identity
`bankRenewalFactor P = s.aB` is established. -/
theorem sourceBankFaceLevelRow_zero_iff_pythonShapedLog
    {S : Type*} [Fintype S] (P : Primitives S)
    (d : LocalPrefixDateData)
    (hface : 0 < d.nextBankFace)
    (hrenew : 0 <
      bankRenewalFactor P * d.controls.loanRate *
        d.currentBankFace / d.controls.inflation) :
    localReducedRemainingResidual P d (0 : Fin 11) = 0 ↔
      Real.log (d.nextBankFace /
        (bankRenewalFactor P * d.controls.loanRate *
          d.currentBankFace / d.controls.inflation)) = 0 := by
  change
    d.nextBankFace -
      bankRenewalFactor P * d.controls.loanRate *
        d.currentBankFace / d.controls.inflation = 0 ↔
    Real.log (d.nextBankFace /
      (bankRenewalFactor P * d.controls.loanRate *
        d.currentBankFace / d.controls.inflation)) = 0
  exact sourceLevelDifference_zero_iff_logRatio
    d.nextBankFace
    (bankRenewalFactor P * d.controls.loanRate *
      d.currentBankFace / d.controls.inflation) hface hrenew

#print axioms sourceBankFaceLevelRow_zero_iff_pythonShapedLog

/-- Original SOURCE row 3 uses wage minus the labor supply target,
whereas the original Python row 3 uses log(wage/target).
They share zeros only on the corresponding positive chart. -/
theorem sourceLaborSupplyLevelRow_zero_iff_pythonShapedLog
    {S : Type*} [Fintype S] (P : Primitives S)
    (d : LocalPrefixDateData)
    (hwage : 0 < d.controls.wage)
    (htarget : 0 <
      P.laborScale * d.controls.workerConsumption ^ P.workerRiskAversion *
        localPrefixAggregateLabor P d ^ P.laborCurvature) :
    localReducedRemainingResidual P d (3 : Fin 11) = 0 ↔
      Real.log (d.controls.wage /
        (P.laborScale * d.controls.workerConsumption ^
          P.workerRiskAversion *
          localPrefixAggregateLabor P d ^ P.laborCurvature)) = 0 := by
  change
    d.controls.wage -
      P.laborScale * d.controls.workerConsumption ^ P.workerRiskAversion *
        localPrefixAggregateLabor P d ^ P.laborCurvature = 0 ↔
    Real.log (d.controls.wage /
      (P.laborScale * d.controls.workerConsumption ^
        P.workerRiskAversion *
        localPrefixAggregateLabor P d ^ P.laborCurvature)) = 0
  exact sourceLevelDifference_zero_iff_logRatio
    d.controls.wage
    (P.laborScale * d.controls.workerConsumption ^ P.workerRiskAversion *
      localPrefixAggregateLabor P d ^ P.laborCurvature)
    hwage htarget

#print axioms sourceLaborSupplyLevelRow_zero_iff_pythonShapedLog

/-- Original SOURCE row 4 uses `1 - householdSDF*rd/inflationNext`
and original Python row 4 uses
`log(rd*household_sdf/next_controls[5])`.
The source and Python-shaped row have the same zeros under positivity
but are not equal as functions. -/
theorem sourceHouseholdDepositLevelRow_zero_iff_pythonShapedLog
    {S : Type*} [Fintype S] (P : Primitives S)
    (d : LocalPrefixDateData)
    (hsdf : 0 <
      (P.workerDiscount *
        crraMarginal P.workerRiskAversion d.nextControls.workerConsumption /
          crraMarginal P.workerRiskAversion d.controls.workerConsumption) *
          d.controls.depositRate)
    (hinfl : 0 < d.nextControls.inflation) :
    localReducedRemainingResidual P d (4 : Fin 11) = 0 ↔
      Real.log (
        ((P.workerDiscount *
          crraMarginal P.workerRiskAversion d.nextControls.workerConsumption /
            crraMarginal P.workerRiskAversion d.controls.workerConsumption) *
            d.controls.depositRate) /
              d.nextControls.inflation) = 0 := by
  change
    1 -
      ((P.workerDiscount *
        crraMarginal P.workerRiskAversion d.nextControls.workerConsumption /
          crraMarginal P.workerRiskAversion d.controls.workerConsumption) *
          d.controls.depositRate) /
        d.nextControls.inflation = 0 ↔
    Real.log (
      ((P.workerDiscount *
        crraMarginal P.workerRiskAversion d.nextControls.workerConsumption /
          crraMarginal P.workerRiskAversion d.controls.workerConsumption) *
          d.controls.depositRate) /
        d.nextControls.inflation) = 0
  exact sourceOneMinusRatio_zero_iff_logRatio
    ((P.workerDiscount *
      crraMarginal P.workerRiskAversion d.nextControls.workerConsumption /
        crraMarginal P.workerRiskAversion d.controls.workerConsumption) *
        d.controls.depositRate)
    d.nextControls.inflation hsdf hinfl

#print axioms sourceHouseholdDepositLevelRow_zero_iff_pythonShapedLog

end Ventura26LiquidityAllocation
