import Ventura26LiquidityAllocation.LocalScalarAugmented34SourceCandidate
import Ventura26LiquidityAllocation.LocalScalarOriginalBoundaryBBranchCandidate
import Ventura26LiquidityAllocation.LocalScalarOriginalEulerRowsCandidate

/-!
# Augmented exact zero -> original firm-L boundary KKT rows

The extra scalar equation mu_L = 0 is not a second equilibrium. At the
boundary it produces the DEGENERATE intersection of original slack and
binding local firm-L conditions. The source's modified row five
forces normalized collateral slack to vanish when the prescribed
slack s = 0. The funding marginal also vanishes by the 34th row.

With explicit nonzero denominators, this recovers the original
binding face row and the original slack funding/capital Euler rows.
It does NOT produce two DISTINCT competitive allocations or solve
the other agents' KKT and infinite-horizon feasibility.
-/

namespace Ventura26LiquidityAllocation
namespace ProposedLocalScalarAugmented34Kkt

open ProposedLocalScalarAugmented34Source
open ProposedLocalScalarEconomicSlice
open ProposedLocalScalarOriginalBoundaryBBranch
open ProposedLocalScalarOriginalEulerRows
open ProposedLocalScalarOriginalCollateralKktBridge

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- Every exact root of the 34-equation SOURCE system at prescribed
collateral slack zero recovers the original L collateral KKT block.
The binding face row requires a nonzero pledged-value denominator;
the original slack loan-Euler requires a nonzero loan rate.

Crucially, both local regimes meet at this root: this theorem
establishes their boundary intersection, NOT their separation. -/
theorem augmented_source_zero_recovers_boundary_L_conditions
    (P : Primitives S) (I : InheritedState) (Z0 : LocalPrefixCoordinates)
    (dateOne recurrent : S) (tail : LocalPrefixContinuationRule)
    (z : Fin 33 → ℝ) (h : ℝ)
    (hzero : augmentedBoundaryZeroResidual
      P I Z0 dateOne recurrent tail z h = (0, 0))
    (hden :
      let y := reserveRemunerationSlice 0 h
      let Pv := initialIntervenedPrimitives P (localScalarParameterIntervention y)
      let Z := localPrefixLogChart Z0 z
      Pv.pledgeability FirmType.L * (1 - Pv.depreciation) *
        Z.controlsOne.inflation * Z.controlsOne.capitalPrice *
        Z.stateOne.capitalL ≠ 0)
    (hloan : (localPrefixLogChart Z0 z).controlsZero.loanRate ≠ 0) :
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
  obtain ⟨hrows, hdualZero⟩ :=
    (augmentedBoundaryZeroResidual_eq_zero_iff
      P I Z0 dateOne recurrent tail z h).mp hzero
  let y := reserveRemunerationSlice 0 h
  let Pv := initialIntervenedPrimitives P (localScalarParameterIntervention y)
  let Z := localPrefixLogChart Z0 z
  have hrow5 :
      localBindingResidualWithSlack P I Z0 dateOne recurrent tail y z
        (5 : Fin 33) = 0 := hrows 5
  have hslack : localNormalizedSlackL Pv Z = 0 := by
    change localNormalizedSlackL Pv Z - y 0 = 0 at hrow5
    simpa [y] using hrow5
  have hdual : localNormalizedCollateralDualL Pv Z = 0 := by
    change localNormalizedCollateralDualL
      (initialIntervenedPrimitives P (localScalarParameterIntervention y)) Z = 0
    rw [normalizedCollateralDual_invariant_under_initial_intervention]
    exact hdualZero
  have hKKT : LocalScalarComplementarityL Pv Z := by
    change 0 ≤ localNormalizedSlackL Pv Z ∧
      0 ≤ localNormalizedCollateralDualL Pv Z ∧
      localNormalizedSlackL Pv Z * localNormalizedCollateralDualL Pv Z = 0
    simp [hslack, hdual]
  have hB :
      localReducedPrefixResidual LocalPrefixBranch.binding Pv I Z
        dateOne recurrent tail LocalPrefixEquation.firmRegimeZeroL = 0 :=
    source_binding_face_row_of_zero_normalized_slack
      Pv I Z dateOne recurrent tail hden hslack
  have hS :
      localReducedPrefixResidual LocalPrefixBranch.slack Pv I Z
        dateOne recurrent tail LocalPrefixEquation.firmRegimeZeroL = 0 :=
    source_original_S_funding_row_zero
      Pv I Z dateOne recurrent tail hloan hdual
  have hrow3 :
      localBindingResidualWithSlack P I Z0 dateOne recurrent tail y z
        (3 : Fin 33) = 0 := hrows 3
  have hBEuler :
      localReducedPrefixResidual LocalPrefixBranch.binding Pv I Z
        dateOne recurrent tail LocalPrefixEquation.firmCapitalEulerZeroL = 0 := by
    simpa [localBindingResidualWithSlack, localPrefixEquationOfIndex,
      y, Pv, Z] using hrow3
  have hSEuler :
      localReducedPrefixResidual LocalPrefixBranch.slack Pv I Z
        dateOne recurrent tail LocalPrefixEquation.firmCapitalEulerZeroL = 0 :=
    source_original_S_capital_euler_row_zero
      Pv I Z dateOne recurrent tail hBEuler hdual
  exact ⟨hKKT, hB, hS, hSEuler⟩

#print axioms augmented_source_zero_recovers_boundary_L_conditions

end ProposedLocalScalarAugmented34Kkt
end Ventura26LiquidityAllocation
