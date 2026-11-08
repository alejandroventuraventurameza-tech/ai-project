import Ventura26LiquidityAllocation.LocalScalarAugmented34PositiveKktCandidate

/-!
# Recover all original binding-prefix equations from an augmented source zero

The modified 33-row equation system differs from the original B prefix
at the single L collateral regime row. At a zero of the 34-dimensional
augmented source, the prescribed slack is zero, so this row converts
back to its original binding face equation when the collateral
denominator is nonzero. Under positive source log coordinates and
positive L pledgeability, that denominator is nonzero.

The result covers EXACTLY 33 original reduced B equations at dates
zero and one. It is not a competitive equilibrium, a solution to
stochastic dynamic optimization, or a proof of distinct S/B branches.
-/

namespace Ventura26LiquidityAllocation
namespace ProposedLocalScalarAugmented34FullBinding

open ProposedLocalScalarAugmented34Source
open ProposedLocalScalarAugmented34PositiveKkt
open ProposedLocalScalarEconomicSlice

variable {S : Type*} [Fintype S] [DecidableEq S]

theorem augmented_zero_implies_all_original_binding_prefix_rows
    (P : Primitives S) (I : InheritedState) (Z0 : LocalPrefixCoordinates)
    (dateOne recurrent : S) (tail : LocalPrefixContinuationRule)
    (z : Fin 33 → ℝ) (h : ℝ)
    (hbase : LocalPrefixCoordinatesPositive Z0)
    (hpledge : 0 < P.pledgeability FirmType.L)
    (hdepr : P.depreciation < 1)
    (hroot : augmentedBoundaryZeroResidual
      P I Z0 dateOne recurrent tail z h = (0, 0)) :
    let y := reserveRemunerationSlice 0 h
    let Pv := initialIntervenedPrimitives P (localScalarParameterIntervention y)
    let Z := localPrefixLogChart Z0 z
    ∀ row : Fin 33,
      localReducedPrefixResidual LocalPrefixBranch.binding Pv I Z
        dateOne recurrent tail (localPrefixEquationOfIndex row) = 0 := by
  let y := reserveRemunerationSlice 0 h
  let Pv := initialIntervenedPrimitives P (localScalarParameterIntervention y)
  let Z := localPrefixLogChart Z0 z
  have hrows : ∀ row : Fin 33,
      localBindingResidualWithSlack P I Z0 dateOne recurrent tail y z row = 0 :=
    ((augmentedBoundaryZeroResidual_eq_zero_iff
      P I Z0 dateOne recurrent tail z h).mp hroot).1
  obtain ⟨_hKKT, hBface, _hSfunding, _hSEuler⟩ :=
    augmented_source_zero_recovers_original_L_under_positive_domain
      P I Z0 dateOne recurrent tail z h hbase hpledge hdepr hroot
  intro row
  by_cases hrow : localPrefixEquationOfIndex row = LocalPrefixEquation.firmRegimeZeroL
  · rw [hrow]
    exact hBface
  · have hmod := hrows row
    change (if localPrefixEquationOfIndex row =
      LocalPrefixEquation.firmRegimeZeroL then
        localNormalizedSlackL Pv Z - y 0
      else localReducedPrefixResidual LocalPrefixBranch.binding Pv I Z
        dateOne recurrent tail (localPrefixEquationOfIndex row)) = 0 at hmod
    simpa only [hrow, if_false] using hmod

#print axioms augmented_zero_implies_all_original_binding_prefix_rows

end ProposedLocalScalarAugmented34FullBinding
end Ventura26LiquidityAllocation
