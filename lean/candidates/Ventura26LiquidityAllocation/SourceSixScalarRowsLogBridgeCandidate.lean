import Ventura26LiquidityAllocation.SourceCommonPledgeLogBridgeCandidate

/-!
# Three additional ORIGINAL SOURCE row families, both prefix dates

This module reads localReducedRemainingResidual directly: row 0 (bank
face renewal), row 3 (worker labor supply), and row 4 (household Euler).
The six date-specific rows of localReducedPrefixResidual are exposed by
definitional equality. Each level residual is equivalent to a normalized
logarithmic zero under explicit nonzero-denominator and positive-chart
hypotheses.

This does NOT prove equivalence with the Python implementation or its P0
tail. In particular, no SOURCE economic Jacobian inverse is claimed.
-/

namespace Ventura26LiquidityAllocation

noncomputable def sourceBankFaceTarget (P : Primitives LocalBridgePhase)
    (d : LocalPrefixDateData) : ℝ :=
  bankRenewalFactor P * d.controls.loanRate * d.currentBankFace /
    d.controls.inflation

noncomputable def sourceWorkerWageTarget (P : Primitives LocalBridgePhase)
    (d : LocalPrefixDateData) : ℝ :=
  P.laborScale * d.controls.workerConsumption ^ P.workerRiskAversion *
    localPrefixAggregateLabor P d ^ P.laborCurvature

noncomputable def sourceHouseholdEulerRatio
    (P : Primitives LocalBridgePhase) (d : LocalPrefixDateData) : ℝ :=
  (P.workerDiscount *
    crraMarginal P.workerRiskAversion d.nextControls.workerConsumption /
    crraMarginal P.workerRiskAversion d.controls.workerConsumption) *
    d.controls.depositRate / d.nextControls.inflation

/-- Source row, not a Python transcription: current bank face carried into
the next date under the bank renewal factor. -/
theorem sourceBankFace_level_row (P : Primitives LocalBridgePhase)
    (d : LocalPrefixDateData) :
    localReducedRemainingResidual P d 0 =
      d.nextBankFace - sourceBankFaceTarget P d := by
  rfl

#print axioms sourceBankFace_level_row

theorem sourceWorkerWage_level_row (P : Primitives LocalBridgePhase)
    (d : LocalPrefixDateData) :
    localReducedRemainingResidual P d 3 =
      d.controls.wage - sourceWorkerWageTarget P d := by
  rfl

#print axioms sourceWorkerWage_level_row

theorem sourceHouseholdEuler_level_row (P : Primitives LocalBridgePhase)
    (d : LocalPrefixDateData) :
    localReducedRemainingResidual P d 4 =
      1 - sourceHouseholdEulerRatio P d := by
  rfl

#print axioms sourceHouseholdEuler_level_row

/-- The actual SOURCE bank renewal residual has the same zero set as
its positive-domain log normalization. -/
theorem sourceBankFace_log_zero_iff (P : Primitives LocalBridgePhase)
    (d : LocalPrefixDateData)
    (hd : sourceBankFaceTarget P d ≠ 0)
    (hp : 0 < 1 + localReducedRemainingResidual P d 0 /
      sourceBankFaceTarget P d) :
    scalarLogResidual (sourceBankFaceTarget P d)
      (localReducedRemainingResidual P d 0) = 0 ↔
      localReducedRemainingResidual P d 0 = 0 := by
  constructor
  · intro h
    have hr := scalarLevelLog_roundtrip
      (sourceBankFaceTarget P d) (localReducedRemainingResidual P d 0) hd hp
    rw [h] at hr
    simpa [scalarLevelResidual] using hr.symm
  · intro h
    rw [h]
    simp [scalarLogResidual]

#print axioms sourceBankFace_log_zero_iff

theorem sourceWorkerWage_log_zero_iff (P : Primitives LocalBridgePhase)
    (d : LocalPrefixDateData)
    (hd : sourceWorkerWageTarget P d ≠ 0)
    (hp : 0 < 1 + localReducedRemainingResidual P d 3 /
      sourceWorkerWageTarget P d) :
    scalarLogResidual (sourceWorkerWageTarget P d)
      (localReducedRemainingResidual P d 3) = 0 ↔
      localReducedRemainingResidual P d 3 = 0 := by
  constructor
  · intro h
    have hr := scalarLevelLog_roundtrip
      (sourceWorkerWageTarget P d) (localReducedRemainingResidual P d 3) hd hp
    rw [h] at hr
    simpa [scalarLevelResidual] using hr.symm
  · intro h
    rw [h]
    simp [scalarLogResidual]

#print axioms sourceWorkerWage_log_zero_iff

/-- SOURCE worker Euler is 1-r, so the signed log normalization is used.
Here the canonical denominator is one; the positive condition says r>0. -/
theorem sourceHouseholdEuler_log_zero_iff (P : Primitives LocalBridgePhase)
    (d : LocalPrefixDateData)
    (hp : 0 < 1 - localReducedRemainingResidual P d 4) :
    negativeScalarLogResidual 1 (localReducedRemainingResidual P d 4) = 0 ↔
      localReducedRemainingResidual P d 4 = 0 := by
  constructor
  · intro h
    have hr := negativeScalarLevelLog_roundtrip
      1 (localReducedRemainingResidual P d 4) (by norm_num) (by simpa using hp)
    rw [h] at hr
    simpa [negativeScalarLevelResidual] using hr.symm
  · intro h
    rw [h]
    simp [negativeScalarLogResidual]

#print axioms sourceHouseholdEuler_log_zero_iff

/-- These are the actual time-zero/time-one reductions. The date-one
continuation remains an arbitrary SOURCE tail rule rather than P0. -/
theorem sourceBankFace_dateZero_row
    (branch : LocalPrefixBranch) (P : Primitives LocalBridgePhase)
    (I : InheritedState) (Z : LocalPrefixCoordinates)
    (dateOne recurrent : LocalBridgePhase)
    (tail : LocalPrefixContinuationRule) :
    localReducedPrefixResidual branch P I Z dateOne recurrent tail
      .bankEquityZero =
      localReducedRemainingResidual P (localPrefixDateZeroData P I Z dateOne) 0 := by
  rfl

#print axioms sourceBankFace_dateZero_row

theorem sourceBankFace_dateOne_row
    (branch : LocalPrefixBranch) (P : Primitives LocalBridgePhase)
    (I : InheritedState) (Z : LocalPrefixCoordinates)
    (dateOne recurrent : LocalBridgePhase)
    (tail : LocalPrefixContinuationRule) :
    localReducedPrefixResidual branch P I Z dateOne recurrent tail
      .bankEquityOne =
      localReducedRemainingResidual P
        (localPrefixDateOneData P Z dateOne recurrent tail) 0 := by
  rfl

#print axioms sourceBankFace_dateOne_row

theorem sourceWorkerWage_dateZero_row
    (branch : LocalPrefixBranch) (P : Primitives LocalBridgePhase)
    (I : InheritedState) (Z : LocalPrefixCoordinates)
    (dateOne recurrent : LocalBridgePhase)
    (tail : LocalPrefixContinuationRule) :
    localReducedPrefixResidual branch P I Z dateOne recurrent tail
      .workerLaborZero =
      localReducedRemainingResidual P (localPrefixDateZeroData P I Z dateOne) 3 := by
  rfl

#print axioms sourceWorkerWage_dateZero_row

theorem sourceWorkerWage_dateOne_row
    (branch : LocalPrefixBranch) (P : Primitives LocalBridgePhase)
    (I : InheritedState) (Z : LocalPrefixCoordinates)
    (dateOne recurrent : LocalBridgePhase)
    (tail : LocalPrefixContinuationRule) :
    localReducedPrefixResidual branch P I Z dateOne recurrent tail
      .workerLaborOne =
      localReducedRemainingResidual P
        (localPrefixDateOneData P Z dateOne recurrent tail) 3 := by
  rfl

#print axioms sourceWorkerWage_dateOne_row

theorem sourceHouseholdEuler_dateZero_row
    (branch : LocalPrefixBranch) (P : Primitives LocalBridgePhase)
    (I : InheritedState) (Z : LocalPrefixCoordinates)
    (dateOne recurrent : LocalBridgePhase)
    (tail : LocalPrefixContinuationRule) :
    localReducedPrefixResidual branch P I Z dateOne recurrent tail
      .householdEulerZero =
      localReducedRemainingResidual P (localPrefixDateZeroData P I Z dateOne) 4 := by
  rfl

#print axioms sourceHouseholdEuler_dateZero_row

theorem sourceHouseholdEuler_dateOne_row
    (branch : LocalPrefixBranch) (P : Primitives LocalBridgePhase)
    (I : InheritedState) (Z : LocalPrefixCoordinates)
    (dateOne recurrent : LocalBridgePhase)
    (tail : LocalPrefixContinuationRule) :
    localReducedPrefixResidual branch P I Z dateOne recurrent tail
      .householdEulerOne =
      localReducedRemainingResidual P
        (localPrefixDateOneData P Z dateOne recurrent tail) 4 := by
  rfl

#print axioms sourceHouseholdEuler_dateOne_row

end Ventura26LiquidityAllocation
