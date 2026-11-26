import Ventura26LiquidityAllocation.LocalScalarEconomicSliceCandidate

/-!
# Exact source augmented 33+1 boundary-zero operator

A numerical interval box for 34 equations is not yet a certified bound
for the Lean source. This candidate only gives the exact source function
to which that numerical calculation must eventually be related.

The intervention changes the reserve-remuneration rule innovation only.
The last equation is the source normalized L funding dual, evaluated at
the SAME log-coordinate vector as the 33 modified binding-prefix rows.

No root, C1, derivative identity, Banach hypotheses, competitive
equilibrium or policy IRF is asserted in this module.
-/

namespace Ventura26LiquidityAllocation
namespace ProposedLocalScalarAugmented34Source

open ProposedLocalScalarEconomicSlice

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- A literal 34-equation object, represented as R^33 × R.
The external certificate uses the same coordinate order, with the policy
innovation h appended as the thirty-fourth unknown. -/
noncomputable def augmentedBoundaryZeroResidual
    (P : Primitives S) (I : InheritedState) (Z0 : LocalPrefixCoordinates)
    (dateOne recurrent : S) (tail : LocalPrefixContinuationRule)
    (z : Fin 33 → ℝ) (h : ℝ) : (Fin 33 → ℝ) × ℝ :=
  (fun row => localBindingResidualWithSlack P I Z0 dateOne recurrent tail
     (reserveRemunerationSlice 0 h) z row,
   localNormalizedCollateralDualL P (localPrefixLogChart Z0 z))

/-- Every one of the 33 augmented first-component equations is
literally the source modified binding-prefix residual at s=0. -/
theorem augmentedBoundaryZeroResidual_source_row
    (P : Primitives S) (I : InheritedState) (Z0 : LocalPrefixCoordinates)
    (dateOne recurrent : S) (tail : LocalPrefixContinuationRule)
    (z : Fin 33 → ℝ) (h : ℝ) (row : Fin 33) :
    (augmentedBoundaryZeroResidual P I Z0 dateOne recurrent tail z h).1 row =
      localBindingResidualWithSlack P I Z0 dateOne recurrent tail
        (reserveRemunerationSlice 0 h) z row := by
  rfl

/-- The thirty-fourth residual is the literal source L dual, not
the log-collateral face, a price spread or an arbitrary scalar. -/
theorem augmentedBoundaryZeroResidual_source_dual
    (P : Primitives S) (I : InheritedState) (Z0 : LocalPrefixCoordinates)
    (dateOne recurrent : S) (tail : LocalPrefixContinuationRule)
    (z : Fin 33 → ℝ) (h : ℝ) :
    (augmentedBoundaryZeroResidual P I Z0 dateOne recurrent tail z h).2 =
      localNormalizedCollateralDualL P (localPrefixLogChart Z0 z) := by
  rfl

/-- Direct remuneration dependence of the final marginal vanishes
when the 33 endogenous log coordinates are held fixed. This does not
say that the total equilibrium response is zero. -/
theorem augmentedBoundaryZeroResidual_dual_fixed_state
    (P : Primitives S) (I : InheritedState) (Z0 : LocalPrefixCoordinates)
    (dateOne recurrent : S) (tail : LocalPrefixContinuationRule)
    (z : Fin 33 → ℝ) (h h' : ℝ) :
    (augmentedBoundaryZeroResidual P I Z0 dateOne recurrent tail z h).2 =
      (augmentedBoundaryZeroResidual P I Z0 dateOne recurrent tail z h').2 := by
  rfl

/-- A zero of the augmented source map consists of all 33 literal
modified binding rows plus a zero normalized L funding dual. -/
theorem augmentedBoundaryZeroResidual_eq_zero_iff
    (P : Primitives S) (I : InheritedState) (Z0 : LocalPrefixCoordinates)
    (dateOne recurrent : S) (tail : LocalPrefixContinuationRule)
    (z : Fin 33 → ℝ) (h : ℝ) :
    augmentedBoundaryZeroResidual P I Z0 dateOne recurrent tail z h = (0, 0) ↔
      (∀ row : Fin 33,
        localBindingResidualWithSlack P I Z0 dateOne recurrent tail
          (reserveRemunerationSlice 0 h) z row = 0) ∧
      localNormalizedCollateralDualL P (localPrefixLogChart Z0 z) = 0 := by
  constructor
  · intro hz
    have hfirst := congrArg Prod.fst hz
    have hlast := congrArg Prod.snd hz
    constructor
    · intro row
      have hrow := congrFun hfirst row
      simpa only [augmentedBoundaryZeroResidual] using hrow
    · simpa only [augmentedBoundaryZeroResidual] using hlast
  · rintro ⟨hrows, hdual⟩
    apply Prod.ext
    · funext row
      exact hrows row
    · exact hdual

/-- The augmented experiment does not vary reserve quantity, encaje
or the corridor. This is a policy-label statement, not a rate response. -/
theorem augmentedBoundaryZeroResidual_policy_contract (h : ℝ) :
    (localScalarParameterIntervention
      (reserveRemunerationSlice 0 h)).reserveRateInnovation = h ∧
    (localScalarParameterIntervention
      (reserveRemunerationSlice 0 h)).reserveQuantityInnovation = 0 ∧
    (localScalarParameterIntervention
      (reserveRemunerationSlice 0 h)).reserveRequirement = 0 ∧
    (localScalarParameterIntervention
      (reserveRemunerationSlice 0 h)).corridorWidth = 0 := by
  exact reserveRemunerationSlice_policy_contract 0 h

#print axioms augmentedBoundaryZeroResidual_source_row
#print axioms augmentedBoundaryZeroResidual_source_dual
#print axioms augmentedBoundaryZeroResidual_dual_fixed_state
#print axioms augmentedBoundaryZeroResidual_eq_zero_iff
#print axioms augmentedBoundaryZeroResidual_policy_contract

end ProposedLocalScalarAugmented34Source
end Ventura26LiquidityAllocation
