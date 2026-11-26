import Ventura26LiquidityAllocation.LocalScalarAugmented34KktCandidate
import Ventura26LiquidityAllocation.LocalScalarPositiveLogChartDomainCandidate

/-!
# Recover original boundary L KKT without arbitrary rate/face assumptions

The log-coordinate system automatically gives a nonzero loan rate and
a nonzero pledged-value denominator when the baseline coordinates are
positive, pledgeability(L)>0 and depreciation<1. These economically
interpretable premises replace the ad hoc nonzero assumptions in the
preceding augmented-root-to-KKT theorem.

Only LOCAL DATE-ZERO firm L equations are recovered. The augmented
root is an intersection of the S/B first-order conditions, not a proof
of two distinct equilibria, bank optimality, or an infinite tail.
-/

namespace Ventura26LiquidityAllocation
namespace ProposedLocalScalarAugmented34PositiveKkt

open ProposedLocalScalarAugmented34Source
open ProposedLocalScalarAugmented34Kkt
open ProposedLocalScalarEconomicSlice
open ProposedLocalScalarPositiveLogChartDomain

variable {S : Type*} [Fintype S] [DecidableEq S]

theorem augmented_source_zero_recovers_original_L_under_positive_domain
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
    LocalScalarComplementarityL Pv Z ∧
    localReducedPrefixResidual LocalPrefixBranch.binding Pv I Z
      dateOne recurrent tail LocalPrefixEquation.firmRegimeZeroL = 0 ∧
    localReducedPrefixResidual LocalPrefixBranch.slack Pv I Z
      dateOne recurrent tail LocalPrefixEquation.firmRegimeZeroL = 0 ∧
    localReducedPrefixResidual LocalPrefixBranch.slack Pv I Z
      dateOne recurrent tail LocalPrefixEquation.firmCapitalEulerZeroL = 0 := by
  have hloan : (localPrefixLogChart Z0 z).controlsZero.loanRate ≠ 0 :=
    ne_of_gt (localPrefixLogChart_loanRate_pos Z0 hbase z)
  have hden :
      let y := reserveRemunerationSlice 0 h
      let Pv := initialIntervenedPrimitives P (localScalarParameterIntervention y)
      let Z := localPrefixLogChart Z0 z
      Pv.pledgeability FirmType.L * (1 - Pv.depreciation) *
        Z.controlsOne.inflation * Z.controlsOne.capitalPrice *
        Z.stateOne.capitalL ≠ 0 := by
    have hp := localPrefixLogChart_L_collateral_denominator_pos
      P Z0 hbase z hpledge hdepr
    change (initialIntervenedPrimitives P
      (localScalarParameterIntervention (reserveRemunerationSlice 0 h))).pledgeability
        FirmType.L *
      (1 - (initialIntervenedPrimitives P
        (localScalarParameterIntervention (reserveRemunerationSlice 0 h))).depreciation) *
      (localPrefixLogChart Z0 z).controlsOne.inflation *
      (localPrefixLogChart Z0 z).controlsOne.capitalPrice *
      (localPrefixLogChart Z0 z).stateOne.capitalL ≠ 0
    simpa only [initialIntervenedPrimitives] using (ne_of_gt hp)
  exact augmented_source_zero_recovers_boundary_L_conditions
    P I Z0 dateOne recurrent tail z h hroot hden hloan

#print axioms augmented_source_zero_recovers_original_L_under_positive_domain

end ProposedLocalScalarAugmented34PositiveKkt
end Ventura26LiquidityAllocation
