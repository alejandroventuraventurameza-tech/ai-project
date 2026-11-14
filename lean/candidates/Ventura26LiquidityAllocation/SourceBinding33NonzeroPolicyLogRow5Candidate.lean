import Ventura26LiquidityAllocation.SourceAugmented34NonzeroRemunerationBoundaryCandidate
import Ventura26LiquidityAllocation.NonlinearResidualRowmapExactCandidate

/-!
# Genuine SOURCE row 5: normalized collateral slack versus log-face residual

At the same positive economic SOURCE coordinate and ANY reserve-rate
innovation h, the first-33 augmented residual uses
S_L = 1 - face_L / Gamma_L.
The 33-row Python binding implementation uses the positive log-face
ratio log(face_L/Gamma_L). The exact source-side relation is

  log(face_L/Gamma_L) = log(1 - S_L).

In the positive-face domain, the log residual is zero iff S_L is zero.
This is proved using the genuine SOURCE primitives and collateral row
rather than executing or assuming equality to the Python engine.
-/

namespace Ventura26LiquidityAllocation

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- The SOURCE modified row-5 slack is unchanged by changing ONLY the
reserve-remuneration innovation h, with the log economic coordinates
held fixed. All indirect equilibrium effects remain possible. -/
theorem sourceBinding33_row5_fixed_coordinates_policy_invariant
    (P : Primitives S) (I : InheritedState) (Z0 : LocalPrefixCoordinates)
    (dateOne recurrent : S) (tail : LocalPrefixContinuationRule)
    (z : Fin 33 → ℝ) (h h' : ℝ) :
    localBindingResidualWithSlack P I Z0 dateOne recurrent tail
      (ProposedLocalScalarEconomicSlice.reserveRemunerationSlice 0 h)
      z (5 : Fin 33) =
    localBindingResidualWithSlack P I Z0 dateOne recurrent tail
      (ProposedLocalScalarEconomicSlice.reserveRemunerationSlice 0 h')
      z (5 : Fin 33) := by
  have h1 := sourceBinding33_nonzeroPolicy_eachRow
    P I Z0 dateOne recurrent tail z h (5 : Fin 33)
  have h2 := sourceBinding33_nonzeroPolicy_eachRow
    P I Z0 dateOne recurrent tail z h' (5 : Fin 33)
  simp only [localPrefixEquationOfIndex, if_true] at h1 h2
  rw [h1, h2]
  rfl

#print axioms sourceBinding33_row5_fixed_coordinates_policy_invariant

/-- SOURCE's literal L-binding nominal-face/pledge ratio equals
one minus the modified SOURCE normalized slack. No logarithm
and no positivity assumption is needed for this algebraic equality. -/
theorem sourceBinding33_nonzeroPolicy_faceRatio_eq_one_sub_slack
    (P : Primitives S) (I : InheritedState) (Z0 : LocalPrefixCoordinates)
    (dateOne recurrent : S) (tail : LocalPrefixContinuationRule)
    (z : Fin 33 → ℝ) (h : ℝ) :
    (localPrefixLogChart Z0 z).stateOne.firmFaceL /
      sourceBindingLPledgeFace (sourceReserveSlicePrimitives P h)
        (localPrefixLogChart Z0 z) =
    1 - localBindingResidualWithSlack P I Z0 dateOne recurrent tail
      (ProposedLocalScalarEconomicSlice.reserveRemunerationSlice 0 h)
      z (5 : Fin 33) := by
  have hrow := sourceBinding33_nonzeroPolicy_eachRow
    P I Z0 dateOne recurrent tail z h (5 : Fin 33)
  simp only [localPrefixEquationOfIndex, if_true] at hrow
  rw [hrow, sourceBindingNormalizedSlackL_eq_one_minus_pledge_ratio]
  ring

#print axioms sourceBinding33_nonzeroPolicy_faceRatio_eq_one_sub_slack

/-- Exact nonlinear SOURCE row-5 log normalization at ANY h.
This is the economic algebraic expression used by the Python binding
code; separate SOURCE/Python parameter identification is still OPEN. -/
theorem sourceBinding33_nonzeroPolicy_logFace_eq_logSlackComplement
    (P : Primitives S) (I : InheritedState) (Z0 : LocalPrefixCoordinates)
    (dateOne recurrent : S) (tail : LocalPrefixContinuationRule)
    (z : Fin 33 → ℝ) (h : ℝ) :
    Real.log ((localPrefixLogChart Z0 z).stateOne.firmFaceL /
      sourceBindingLPledgeFace (sourceReserveSlicePrimitives P h)
        (localPrefixLogChart Z0 z)) =
    Real.log (1 - localBindingResidualWithSlack P I Z0
      dateOne recurrent tail
      (ProposedLocalScalarEconomicSlice.reserveRemunerationSlice 0 h)
      z (5 : Fin 33)) := by
  rw [sourceBinding33_nonzeroPolicy_faceRatio_eq_one_sub_slack
    P I Z0 dateOne recurrent tail z h]

#print axioms sourceBinding33_nonzeroPolicy_logFace_eq_logSlackComplement

/-- Under the economically required positive nominal-face ratio,
the SOURCE log-face row vanishes exactly when the SOURCE augmented
normalized-slack row vanishes. The strict positivity hypothesis is
ESSENTIAL since real log alone is not globally injective. -/
theorem sourceBinding33_nonzeroPolicy_logFace_zero_iff_slack_zero
    (P : Primitives S) (I : InheritedState) (Z0 : LocalPrefixCoordinates)
    (dateOne recurrent : S) (tail : LocalPrefixContinuationRule)
    (z : Fin 33 → ℝ) (h : ℝ)
    (hp : 0 < (localPrefixLogChart Z0 z).stateOne.firmFaceL /
      sourceBindingLPledgeFace (sourceReserveSlicePrimitives P h)
        (localPrefixLogChart Z0 z)) :
    (Real.log ((localPrefixLogChart Z0 z).stateOne.firmFaceL /
      sourceBindingLPledgeFace (sourceReserveSlicePrimitives P h)
        (localPrefixLogChart Z0 z)) = 0) ↔
    (localBindingResidualWithSlack P I Z0 dateOne recurrent tail
      (ProposedLocalScalarEconomicSlice.reserveRemunerationSlice 0 h)
      z (5 : Fin 33) = 0) := by
  rw [sourceBinding33_nonzeroPolicy_logFace_eq_logSlackComplement]
  have hratio := sourceBinding33_nonzeroPolicy_faceRatio_eq_one_sub_slack
    P I Z0 dateOne recurrent tail z h
  rw [hratio] at hp
  constructor
  · intro hz
    have hx := Real.exp_log hp
    rw [hz] at hx
    norm_num at hx
    linarith
  · intro hz
    rw [hz]
    simp

#print axioms sourceBinding33_nonzeroPolicy_logFace_zero_iff_slack_zero

end Ventura26LiquidityAllocation
