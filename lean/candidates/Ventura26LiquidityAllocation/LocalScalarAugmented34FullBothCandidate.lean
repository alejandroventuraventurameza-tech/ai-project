import Ventura26LiquidityAllocation.LocalScalarAugmented34FullBindingCandidate

/-!
# Intersection of the full original 33-row S/B reduced prefix systems

The original 33-row slack and binding residuals differ ONLY in the
date-zero firm L capital Euler and regime rows. All remaining 31
source equations agree definitionally. The augmented 34-row zero
forces the binding 33 rows; with the source L funding dual exactly
zero, both slack-specific L rows also hold.

This is one and the same reduced prefix under both labels at a
DEGENERATE boundary. It is not the pair of distinct allocations
required by the manuscript's multiplicity claim; the continuation,
full optimization and stochastic equilibrium remain open.
-/

namespace Ventura26LiquidityAllocation
namespace ProposedLocalScalarAugmented34FullBoth

open ProposedLocalScalarAugmented34Source
open ProposedLocalScalarAugmented34PositiveKkt
open ProposedLocalScalarAugmented34FullBinding
open ProposedLocalScalarEconomicSlice

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- Only the two original date-zero L equations change across
the source's S and B active-set prefixes. -/
theorem original_prefix_rows_agree_except_date_zero_L
    (P : Primitives S) (I : InheritedState)
    (Z : LocalPrefixCoordinates) (dateOne recurrent : S)
    (tail : LocalPrefixContinuationRule)
    (equation : LocalPrefixEquation)
    (hEuler : equation ≠ LocalPrefixEquation.firmCapitalEulerZeroL)
    (hRegime : equation ≠ LocalPrefixEquation.firmRegimeZeroL) :
    localReducedPrefixResidual LocalPrefixBranch.slack P I Z
      dateOne recurrent tail equation =
    localReducedPrefixResidual LocalPrefixBranch.binding P I Z
      dateOne recurrent tail equation := by
  cases equation <;> simp [localReducedPrefixResidual,
    localReducedFirmCapitalEulerResidual,
    localReducedFirmRegimeResidual] at hEuler hRegime ⊢

/-- A source augmented zero at s=0 and positive economic levels
satisfies BOTH full original reduced source systems, for the SAME
coordinate point and the SAME monetary policy intervention.

This does not establish two equilibria and does not imply
global or dynamic optimality of any agent. -/
theorem augmented_zero_implies_all_original_S_and_B_prefix_rows
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
    (∀ row : Fin 33,
      localReducedPrefixResidual LocalPrefixBranch.binding Pv I Z
        dateOne recurrent tail (localPrefixEquationOfIndex row) = 0) ∧
    (∀ row : Fin 33,
      localReducedPrefixResidual LocalPrefixBranch.slack Pv I Z
        dateOne recurrent tail (localPrefixEquationOfIndex row) = 0) := by
  let y := reserveRemunerationSlice 0 h
  let Pv := initialIntervenedPrimitives P (localScalarParameterIntervention y)
  let Z := localPrefixLogChart Z0 z
  have hBall : ∀ row : Fin 33,
      localReducedPrefixResidual LocalPrefixBranch.binding Pv I Z
        dateOne recurrent tail (localPrefixEquationOfIndex row) = 0 :=
    augmented_zero_implies_all_original_binding_prefix_rows
      P I Z0 dateOne recurrent tail z h hbase hpledge hdepr hroot
  obtain ⟨_hKKT, _hBface, hSfunding, hSEuler⟩ :=
    augmented_source_zero_recovers_original_L_under_positive_domain
      P I Z0 dateOne recurrent tail z h hbase hpledge hdepr hroot
  refine ⟨hBall, ?_⟩
  intro row
  by_cases hEuler : localPrefixEquationOfIndex row =
      LocalPrefixEquation.firmCapitalEulerZeroL
  · rw [hEuler]
    exact hSEuler
  by_cases hRegime : localPrefixEquationOfIndex row =
      LocalPrefixEquation.firmRegimeZeroL
  · rw [hRegime]
    exact hSfunding
  rw [original_prefix_rows_agree_except_date_zero_L
    Pv I Z dateOne recurrent tail
      (localPrefixEquationOfIndex row) hEuler hRegime]
  exact hBall row

#print axioms original_prefix_rows_agree_except_date_zero_L
#print axioms augmented_zero_implies_all_original_S_and_B_prefix_rows

end ProposedLocalScalarAugmented34FullBoth
end Ventura26LiquidityAllocation
