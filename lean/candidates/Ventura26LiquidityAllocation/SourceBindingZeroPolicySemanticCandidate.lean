import Ventura26LiquidityAllocation.SourceBindingSlackRowScalingCandidate

/-!
# Literal SOURCE zero-policy identity for the modified 33-equation binding system

The original SOURCE Jacobian is evaluated using primitives P; the
modified 33-row binding system uses Pv := initialIntervenedPrimitives
P (localScalarParameterIntervention y). This module checks the
critical economic semantic bridge at y=0, rather than silently
assuming that a numerical 33-row matrix has the same inputs.

It proves that at the true zero policy vector the intervened
Primitives are literally unchanged, and that every modified
binding row is the original SOURCE binding row except for the
one normalized L collateral equation. No source root, C1
regularity or rank certificate is claimed.
-/

namespace Ventura26LiquidityAllocation

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- Zero of the genuine four-tool intervention changes no SOURCE
primitive, including the date-zero calendar paths. -/
theorem sourceInitialIntervenedPrimitives_zero
    (P : Primitives S) :
    initialIntervenedPrimitives P zeroInitialPolicyIntervention = P := by
  cases P
  simp [initialIntervenedPrimitives, zeroInitialPolicyIntervention]

#print axioms sourceInitialIntervenedPrimitives_zero

/-- The exact normalized SOURCE reserve-remuneration slice at
s=h=0 induces precisely the zero four-tool intervention. -/
theorem sourceReserveRemunerationSlice_zero_primitives
    (P : Primitives S) :
    initialIntervenedPrimitives P
      (localScalarParameterIntervention
        (ProposedLocalScalarEconomicSlice.reserveRemunerationSlice 0 0)) =
      P := by
  simpa [ProposedLocalScalarEconomicSlice.reserveRemunerationSlice_zero,
    localScalarParameterIntervention, zeroInitialPolicyIntervention] using
      sourceInitialIntervenedPrimitives_zero P

#print axioms sourceReserveRemunerationSlice_zero_primitives

/-- At exactly zero reserve-remuneration and zero prescribed slack,
the literal SOURCE 33-row modified binding system uses the original
economic equations in all rows except the L date-zero binding
condition, where it uses its normalized collateral slack. -/
theorem sourceModifiedBinding33_zeroPolicy_eachRow
    (P : Primitives S) (I : InheritedState)
    (Z0 : LocalPrefixCoordinates)
    (dateOne recurrent : S) (tail : LocalPrefixContinuationRule)
    (z : Fin 33 → ℝ) (row : Fin 33) :
    localBindingResidualWithSlack P I Z0 dateOne recurrent tail
      (ProposedLocalScalarEconomicSlice.reserveRemunerationSlice 0 0) z row =
      if localPrefixEquationOfIndex row = LocalPrefixEquation.firmRegimeZeroL then
        localNormalizedSlackL P (localPrefixLogChart Z0 z)
      else
        localReducedPrefixResidual LocalPrefixBranch.binding P I
          (localPrefixLogChart Z0 z)
          dateOne recurrent tail (localPrefixEquationOfIndex row) := by
  have hP := sourceReserveRemunerationSlice_zero_primitives P
  have hP0 : initialIntervenedPrimitives P
      (localScalarParameterIntervention (0 : Fin 5 → ℝ)) = P := by
    simpa only [ProposedLocalScalarEconomicSlice.reserveRemunerationSlice_zero]
      using hP
  by_cases hrow :
      localPrefixEquationOfIndex row = LocalPrefixEquation.firmRegimeZeroL
  · simp [localBindingResidualWithSlack, hrow, hP0,
      ProposedLocalScalarEconomicSlice.reserveRemunerationSlice_zero]
  · simp [localBindingResidualWithSlack, hrow, hP0,
      ProposedLocalScalarEconomicSlice.reserveRemunerationSlice_zero]

#print axioms sourceModifiedBinding33_zeroPolicy_eachRow

end Ventura26LiquidityAllocation
