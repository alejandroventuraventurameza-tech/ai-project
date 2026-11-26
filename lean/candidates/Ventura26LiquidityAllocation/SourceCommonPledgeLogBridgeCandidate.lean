import Ventura26LiquidityAllocation.NonlinearResidualRowmapExactCandidate

/-!
# First genuine SOURCE reduced row using exact nonlinear level/log algebra

This module instantiates the verified scalar inverse with the actual
`localReducedPrefixResidual` row `.commonPledgeOne` and the actual date-two
`tail` continuation, NOT a Python transcription.

The resulting equivalence is conditional on the positive-log domain.
No Python/SOURCE operator equality, continuation correctness or full
economic Jacobian inverse is inferred.
-/

namespace Ventura26LiquidityAllocation

/-- Actual nominal pledge target at date two, using the SOURCE continuation
rather than the numerical `P0` approximation. -/
noncomputable def sourceCommonPledgeTarget
    (P : Primitives LocalBridgePhase)
    (Z : LocalPrefixCoordinates)
    (tail : LocalPrefixContinuationRule) : ℝ :=
  (1 - P.depreciation) * (tail Z.stateTwo).inflation *
    (tail Z.stateTwo).capitalPrice

/-- The row under audit is the actual reduced SOURCE residual, not the
unreduced allocation residual with the same constructor. -/
theorem sourceCommonPledgeResidual_exact_level
    (branch : LocalPrefixBranch)
    (P : Primitives LocalBridgePhase) (I : InheritedState)
    (Z : LocalPrefixCoordinates) (dateOne recurrent : LocalBridgePhase)
    (tail : LocalPrefixContinuationRule) :
    localReducedPrefixResidual branch P I Z dateOne recurrent tail
        .commonPledgeOne =
      Z.stateTwo.commonPledgeValue - sourceCommonPledgeTarget P Z tail := by
  rfl

#print axioms sourceCommonPledgeResidual_exact_level

/-- The real logarithmic reconstruction is exact on the actual SOURCE
pledge row, provided the denominator is nonzero and the log argument
strictly positive. -/
theorem sourceCommonPledgeResidual_levelLog_roundtrip
    (branch : LocalPrefixBranch)
    (P : Primitives LocalBridgePhase) (I : InheritedState)
    (Z : LocalPrefixCoordinates) (dateOne recurrent : LocalBridgePhase)
    (tail : LocalPrefixContinuationRule)
    (hd : sourceCommonPledgeTarget P Z tail ≠ 0)
    (hp : 0 < 1 +
      localReducedPrefixResidual branch P I Z dateOne recurrent tail
        .commonPledgeOne / sourceCommonPledgeTarget P Z tail) :
    scalarLevelResidual (sourceCommonPledgeTarget P Z tail)
        (scalarLogResidual (sourceCommonPledgeTarget P Z tail)
          (localReducedPrefixResidual branch P I Z dateOne recurrent tail
            .commonPledgeOne)) =
      localReducedPrefixResidual branch P I Z dateOne recurrent tail
        .commonPledgeOne := by
  exact scalarLevelLog_roundtrip _ _ hd hp

#print axioms sourceCommonPledgeResidual_levelLog_roundtrip

/-- The SOURCE common-pledge row is zero if and only if its normalized
positive-domain logarithmic version vanishes. -/
theorem sourceCommonPledgeResidual_log_zero_iff
    (branch : LocalPrefixBranch)
    (P : Primitives LocalBridgePhase) (I : InheritedState)
    (Z : LocalPrefixCoordinates) (dateOne recurrent : LocalBridgePhase)
    (tail : LocalPrefixContinuationRule)
    (hd : sourceCommonPledgeTarget P Z tail ≠ 0)
    (hp : 0 < 1 +
      localReducedPrefixResidual branch P I Z dateOne recurrent tail
        .commonPledgeOne / sourceCommonPledgeTarget P Z tail) :
    scalarLogResidual (sourceCommonPledgeTarget P Z tail)
      (localReducedPrefixResidual branch P I Z dateOne recurrent tail
        .commonPledgeOne) = 0 ↔
      localReducedPrefixResidual branch P I Z dateOne recurrent tail
        .commonPledgeOne = 0 := by
  constructor
  · intro h
    have hr := sourceCommonPledgeResidual_levelLog_roundtrip
      branch P I Z dateOne recurrent tail hd hp
    rw [h] at hr
    simpa [scalarLevelResidual] using hr.symm
  · intro h
    rw [h]
    simp [scalarLogResidual]

#print axioms sourceCommonPledgeResidual_log_zero_iff

end Ventura26LiquidityAllocation
