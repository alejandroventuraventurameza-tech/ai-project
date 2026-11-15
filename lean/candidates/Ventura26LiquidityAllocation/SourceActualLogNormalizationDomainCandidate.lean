import Ventura26LiquidityAllocation.SourceSixNonlinearLogRowRootTransportCandidate

/-!
# The genuine SOURCE economic rows imply their logarithmic domains

The exact six-row nonlinear residual transform needs strict positive
arguments of log(1+SOURCElevel/target) for bank/labor and
log(1-SOURCEEuler) for household deposits.

This module DISCHARGES those domain assumptions for the ORIGINAL
SOURCE `localReducedRemainingResidual`, conditional only on economically
readable strictly positive levels and ratios. It does not postulate
the sign of the nonlinear log arguments independently.

At any date the actual source rows 0,3,4 are precisely:
  bank: nextBankFace - bankRenewalFlow;
  labor: wage - workerLaborTarget;
  Euler: 1 - householdSDF*depositRate/nextInflation.

Thus 1 + level residual/target = realized positive level/target,
and 1 - Euler residual = positive Euler ratio.

This is an OFF-ROOT real proof, not a SOURCE/Python match of the
numerical economic inputs, a SOURCE box enclosure or existence
of a full dynamic equilibrium.
-/

namespace Ventura26LiquidityAllocation

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- Strictly positive realized and target levels imply the correct
logarithmic normalization domain. Its proof treats B as a single
positive economic target, avoiding any assumption on its internal
division or factorization beyond B>0. -/
theorem sourcePositiveLevel_normalizedLogArgument
    (A B : ℝ) (hA : 0 < A) (hB : 0 < B) :
    0 < 1 + (A - B) / B := by
  have hBne : B ≠ 0 := ne_of_gt hB
  have hid : 1 + (A - B) / B = A / B := by
    field_simp [hBne] <;> ring
  rw [hid]
  exact div_pos hA hB

#print axioms sourcePositiveLevel_normalizedLogArgument

/-- A genuine SOURCE date bank-renewal row has a valid normalized
logarithm wherever the next nominal face and bank-renewal target
are strictly positive. -/
theorem sourceActualBank_logArgument_pos
    (P : Primitives S) (d : LocalPrefixDateData)
    (hnext : 0 < d.nextBankFace)
    (hflow : 0 <
      bankRenewalFactor P * d.controls.loanRate *
        d.currentBankFace / d.controls.inflation) :
    0 < 1 + localReducedRemainingResidual P d (0 : Fin 11) /
      (bankRenewalFactor P * d.controls.loanRate *
        d.currentBankFace / d.controls.inflation) := by
  change 0 < 1 +
    (d.nextBankFace -
      bankRenewalFactor P * d.controls.loanRate *
        d.currentBankFace / d.controls.inflation) /
      (bankRenewalFactor P * d.controls.loanRate *
        d.currentBankFace / d.controls.inflation)
  exact sourcePositiveLevel_normalizedLogArgument _ _ hnext hflow

#print axioms sourceActualBank_logArgument_pos

/-- A genuine SOURCE date labor-supply row has a valid normalized
logarithm if realized wages and the worker marginal labor target
are both strictly positive. -/
theorem sourceActualLabor_logArgument_pos
    (P : Primitives S) (d : LocalPrefixDateData)
    (hwage : 0 < d.controls.wage)
    (htarget : 0 <
      P.laborScale * d.controls.workerConsumption ^ P.workerRiskAversion *
        localPrefixAggregateLabor P d ^ P.laborCurvature) :
    0 < 1 + localReducedRemainingResidual P d (3 : Fin 11) /
      (P.laborScale * d.controls.workerConsumption ^ P.workerRiskAversion *
        localPrefixAggregateLabor P d ^ P.laborCurvature) := by
  change 0 < 1 +
    (d.controls.wage -
      P.laborScale * d.controls.workerConsumption ^ P.workerRiskAversion *
        localPrefixAggregateLabor P d ^ P.laborCurvature) /
      (P.laborScale * d.controls.workerConsumption ^ P.workerRiskAversion *
        localPrefixAggregateLabor P d ^ P.laborCurvature)
  exact sourcePositiveLevel_normalizedLogArgument _ _ hwage htarget

#print axioms sourceActualLabor_logArgument_pos

/-- The original SOURCE Euler residual is `1 - positiveRatio`.
The Python-shaped log(1-SOURCEEuler) has a strictly positive
argument whenever that economic Euler ratio is positive. -/
theorem sourceActualDepositEuler_logArgument_pos
    (P : Primitives S) (d : LocalPrefixDateData)
    (hratio : 0 <
      (P.workerDiscount *
        crraMarginal P.workerRiskAversion d.nextControls.workerConsumption /
          crraMarginal P.workerRiskAversion d.controls.workerConsumption) *
        d.controls.depositRate / d.nextControls.inflation) :
    0 < 1 - localReducedRemainingResidual P d (4 : Fin 11) := by
  change 0 < 1 -
    (1 -
      (P.workerDiscount *
        crraMarginal P.workerRiskAversion d.nextControls.workerConsumption /
          crraMarginal P.workerRiskAversion d.controls.workerConsumption) *
        d.controls.depositRate / d.nextControls.inflation)
  have hid : 1 -
    (1 -
      (P.workerDiscount *
        crraMarginal P.workerRiskAversion d.nextControls.workerConsumption /
          crraMarginal P.workerRiskAversion d.controls.workerConsumption) *
        d.controls.depositRate / d.nextControls.inflation) =
    (P.workerDiscount *
      crraMarginal P.workerRiskAversion d.nextControls.workerConsumption /
        crraMarginal P.workerRiskAversion d.controls.workerConsumption) *
      d.controls.depositRate / d.nextControls.inflation := by ring
  rw [hid]
  exact hratio

#print axioms sourceActualDepositEuler_logArgument_pos

end Ventura26LiquidityAllocation
