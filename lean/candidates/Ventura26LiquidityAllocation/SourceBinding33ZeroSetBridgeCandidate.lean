import Ventura26LiquidityAllocation.SourceBindingZeroPolicySemanticCandidate

/-!
# Exact 33-row SOURCE zero-set bridge at the unperturbed binding benchmark

At y=0, the modified 33-row binding residual replaces only the
original firm-L collateral condition by its normalized slack.
The underlying SOURCE Primitives and other 32 equations must remain
exactly the same. Once that semantic bridge is established, the
modified system and original binding system have the exact same
33-row zero set whenever the literal pledge face is nonzero.

This result is local/prefix only. It does not imply full competitive
equilibrium, continuation C1 regularity, or Jacobian nonsingularity.
-/

namespace Ventura26LiquidityAllocation

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- One individual SOURCE modified binding row at zero policy is zero
if and only if the same original binding row is zero, provided the
true L pledge denominator is nonzero. -/
theorem sourceModifiedBinding33_zeroPolicy_row_zero_iff
    (P : Primitives S) (I : InheritedState)
    (Z0 : LocalPrefixCoordinates)
    (dateOne recurrent : S) (tail : LocalPrefixContinuationRule)
    (z : Fin 33 → ℝ) (row : Fin 33)
    (hne : sourceBindingLPledgeFace P (localPrefixLogChart Z0 z) ≠ 0) :
    (localBindingResidualWithSlack P I Z0 dateOne recurrent tail
      (ProposedLocalScalarEconomicSlice.reserveRemunerationSlice 0 0) z row = 0) ↔
    (localReducedPrefixResidual LocalPrefixBranch.binding P I
      (localPrefixLogChart Z0 z) dateOne recurrent tail
      (localPrefixEquationOfIndex row) = 0) := by
  rw [sourceModifiedBinding33_zeroPolicy_eachRow
    P I Z0 dateOne recurrent tail z row]
  by_cases hlabel :
      localPrefixEquationOfIndex row = LocalPrefixEquation.firmRegimeZeroL
  · simp only [if_pos hlabel]
    rw [hlabel]
    exact sourceBindingNormalizedSlackL_zero_iff_rawL_zero
      P I (localPrefixLogChart Z0 z) dateOne recurrent tail hne
  · simp only [if_neg hlabel]

#print axioms sourceModifiedBinding33_zeroPolicy_row_zero_iff

/-- The complete genuine 33-row modified binding-prefix system at
zero policy has exactly the same zeros as the original SOURCE
binding-branch economic system, on the nonzero-pledge domain. -/
theorem sourceModifiedBinding33_zeroPolicy_all_zero_iff
    (P : Primitives S) (I : InheritedState)
    (Z0 : LocalPrefixCoordinates)
    (dateOne recurrent : S) (tail : LocalPrefixContinuationRule)
    (z : Fin 33 → ℝ)
    (hne : sourceBindingLPledgeFace P (localPrefixLogChart Z0 z) ≠ 0) :
    (∀ row : Fin 33,
      localBindingResidualWithSlack P I Z0 dateOne recurrent tail
        (ProposedLocalScalarEconomicSlice.reserveRemunerationSlice 0 0)
        z row = 0) ↔
    (∀ row : Fin 33,
      localReducedPrefixResidual LocalPrefixBranch.binding P I
        (localPrefixLogChart Z0 z) dateOne recurrent tail
        (localPrefixEquationOfIndex row) = 0) := by
  constructor
  · intro h row
    exact (sourceModifiedBinding33_zeroPolicy_row_zero_iff
      P I Z0 dateOne recurrent tail z row hne).mp (h row)
  · intro h row
    exact (sourceModifiedBinding33_zeroPolicy_row_zero_iff
      P I Z0 dateOne recurrent tail z row hne).mpr (h row)

#print axioms sourceModifiedBinding33_zeroPolicy_all_zero_iff

end Ventura26LiquidityAllocation
