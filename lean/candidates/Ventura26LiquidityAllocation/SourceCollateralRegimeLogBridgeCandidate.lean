import Ventura26LiquidityAllocation.SourceSixScalarRowsLogBridgeCandidate

/-!
# Genuine SOURCE date-zero collateral regime rows: binding and slack L

These theorems normalize actual SOURCE reduced residuals. They do NOT
establish the collateral KKT system, branch correctness for a candidate
equilibrium, or equivalence to a Python residual or tail operator.
-/

namespace Ventura26LiquidityAllocation

noncomputable def sourceDateZeroPledgeTarget
    (P : Primitives LocalBridgePhase) (d : LocalPrefixDateData)
    (i : FirmType) : ℝ :=
  localPrefixPledgeUnit P d i * d.nextCapital i

/-- The SOURCE binding row is explicitly the physical face minus pledge
capacity; the branch-H or branch-L choice is economic, not algebraic. -/
theorem sourceBindingFirmRegime_exact_level
    (P : Primitives LocalBridgePhase) (d : LocalPrefixDateData)
    (i : FirmType) :
    localReducedFirmRegimeResidual .binding P d i =
      d.nextFace i - sourceDateZeroPledgeTarget P d i := by
  rfl

#print axioms sourceBindingFirmRegime_exact_level

/-- The slack-L SOURCE row is the zero-multiplier ratio constraint,
not the binding collateral capacity equation. -/
theorem sourceSlackFirmLRegime_exact_level
    (P : Primitives LocalBridgePhase) (d : LocalPrefixDateData) :
    localReducedFirmRegimeResidual .slack P d FirmType.L =
      d.controls.loanRate * localPrefixEntrepreneurSDF P d FirmType.L /
        d.nextControls.inflation - 1 := by
  rfl

#print axioms sourceSlackFirmLRegime_exact_level

/-- Binding-source collateral face residual and its log-normalized
counterpart have the same zeros in a positive ratio chart. -/
theorem sourceBindingFirmRegime_log_zero_iff
    (P : Primitives LocalBridgePhase) (d : LocalPrefixDateData)
    (i : FirmType)
    (hd : sourceDateZeroPledgeTarget P d i ≠ 0)
    (hp : 0 < 1 + localReducedFirmRegimeResidual .binding P d i /
      sourceDateZeroPledgeTarget P d i) :
    scalarLogResidual (sourceDateZeroPledgeTarget P d i)
      (localReducedFirmRegimeResidual .binding P d i) = 0 ↔
      localReducedFirmRegimeResidual .binding P d i = 0 := by
  constructor
  · intro h
    have hr := scalarLevelLog_roundtrip
      (sourceDateZeroPledgeTarget P d i)
      (localReducedFirmRegimeResidual .binding P d i) hd hp
    rw [h] at hr
    simpa [scalarLevelResidual] using hr.symm
  · intro h
    rw [h]
    simp [scalarLogResidual]

#print axioms sourceBindingFirmRegime_log_zero_iff

/-- The slack-L ratio itself must stay positive. Unlike the binding
case, normalization uses the fixed unit denominator. -/
theorem sourceSlackFirmLRegime_log_zero_iff
    (P : Primitives LocalBridgePhase) (d : LocalPrefixDateData)
    (hp : 0 < 1 + localReducedFirmRegimeResidual .slack P d FirmType.L) :
    scalarLogResidual 1
      (localReducedFirmRegimeResidual .slack P d FirmType.L) = 0 ↔
      localReducedFirmRegimeResidual .slack P d FirmType.L = 0 := by
  constructor
  · intro h
    have hr := scalarLevelLog_roundtrip 1
      (localReducedFirmRegimeResidual .slack P d FirmType.L)
      (by norm_num) (by simpa only [div_one] using hp)
    rw [h] at hr
    simpa [scalarLevelResidual] using hr.symm
  · intro h
    rw [h]
    simp [scalarLogResidual]

#print axioms sourceSlackFirmLRegime_log_zero_iff

/-- Branch and date are read from the genuine reduced SOURCE operator. -/
theorem sourceBindingDateZeroH_row
    (P : Primitives LocalBridgePhase) (I : InheritedState)
    (Z : LocalPrefixCoordinates) (dateOne recurrent : LocalBridgePhase)
    (tail : LocalPrefixContinuationRule) :
    localReducedPrefixResidual .binding P I Z dateOne recurrent tail
      .firmRegimeZeroH =
      localReducedFirmRegimeResidual .binding P
        (localPrefixDateZeroData P I Z dateOne) FirmType.H := by
  rfl

#print axioms sourceBindingDateZeroH_row

theorem sourceBindingDateZeroL_row
    (P : Primitives LocalBridgePhase) (I : InheritedState)
    (Z : LocalPrefixCoordinates) (dateOne recurrent : LocalBridgePhase)
    (tail : LocalPrefixContinuationRule) :
    localReducedPrefixResidual .binding P I Z dateOne recurrent tail
      .firmRegimeZeroL =
      localReducedFirmRegimeResidual .binding P
        (localPrefixDateZeroData P I Z dateOne) FirmType.L := by
  rfl

#print axioms sourceBindingDateZeroL_row

theorem sourceSlackDateZeroL_row
    (P : Primitives LocalBridgePhase) (I : InheritedState)
    (Z : LocalPrefixCoordinates) (dateOne recurrent : LocalBridgePhase)
    (tail : LocalPrefixContinuationRule) :
    localReducedPrefixResidual .slack P I Z dateOne recurrent tail
      .firmRegimeZeroL =
      localReducedFirmRegimeResidual .slack P
        (localPrefixDateZeroData P I Z dateOne) FirmType.L := by
  rfl

#print axioms sourceSlackDateZeroL_row

end Ventura26LiquidityAllocation
