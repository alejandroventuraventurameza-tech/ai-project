import Ventura26LiquidityAllocation.LocalScalarOriginalCollateralKktBridgeCandidate

/-!
# Boundary scalar root -> original B-regime collateral face equation

The source 33-row auxiliary system replaces the original L binding
collateral face equation with a normalized slack = prescribed scalar
equation. If that prescribed slack is zero, then the original B face
equation follows, PROVIDED the pledge denominator is nonzero.

We do not silently infer denominator positivity or face feasibility
from mere existence of an auxiliary root. This is a precise additional
economic-domain condition, to be discharged later from positivity of
the selected source coordinates and primitive parameters.
-/

namespace Ventura26LiquidityAllocation
namespace ProposedLocalScalarOriginalBoundaryBBranch

open ProposedLocalScalarEconomicSlice
open ProposedLocalScalarOriginalCollateralKktBridge

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- Zero normalized slack yields the original B-regime L pledge-face
row, provided the denominator of the normalized constraint is nonzero.
This is the literal date-zero source equation, not a free proxy. -/
theorem source_binding_face_row_of_zero_normalized_slack
    (P : Primitives S) (I : InheritedState)
    (Z : LocalPrefixCoordinates) (dateOne recurrent : S)
    (tail : LocalPrefixContinuationRule)
    (hden : P.pledgeability FirmType.L * (1 - P.depreciation) *
      Z.controlsOne.inflation * Z.controlsOne.capitalPrice *
      Z.stateOne.capitalL ≠ 0)
    (hslack : localNormalizedSlackL P Z = 0) :
    localReducedPrefixResidual LocalPrefixBranch.binding P I Z
      dateOne recurrent tail LocalPrefixEquation.firmRegimeZeroL = 0 := by
  let denom : ℝ :=
    P.pledgeability FirmType.L * (1 - P.depreciation) *
      Z.controlsOne.inflation * Z.controlsOne.capitalPrice *
      Z.stateOne.capitalL
  have hfrac : Z.stateOne.firmFaceL / denom = 1 := by
    change 1 - Z.stateOne.firmFaceL / denom = 0 at hslack
    linarith only [hslack]
  have hface : Z.stateOne.firmFaceL = denom := by
    have hden' : denom ≠ 0 := hden
    have hface' : Z.stateOne.firmFaceL = 1 * denom :=
      (div_eq_iff hden').mp hfrac
    simpa using hface'
  change Z.stateOne.firmFaceL -
    (P.pledgeability FirmType.L * (1 - P.depreciation) *
      Z.controlsOne.inflation * Z.controlsOne.capitalPrice) *
      Z.stateOne.capitalL = 0
  dsimp [denom] at hface
  rw [hface]
  ring

/-- The same result applied to the source's actual five-dimensional
reserve-remuneration slice at the B boundary s=0. Here the auxiliary
row 5 is the only hypothesis about the modified 33 equations. -/
theorem economic_boundary_B_row_from_source_row_five
    (P : Primitives S) (I : InheritedState) (Z0 : LocalPrefixCoordinates)
    (dateOne recurrent : S) (tail : LocalPrefixContinuationRule)
    (solutionLog : (Fin 5 → ℝ) → (Fin 33 → ℝ))
    (h : ℝ)
    (hrow : localBindingResidualWithSlack P I Z0 dateOne recurrent tail
      (reserveRemunerationSlice 0 h)
      (solutionLog (reserveRemunerationSlice 0 h)) (5 : Fin 33) = 0)
    (hden :
      let y := reserveRemunerationSlice 0 h
      let Pv := initialIntervenedPrimitives P (localScalarParameterIntervention y)
      let Z := localPrefixLogChart Z0 (solutionLog y)
      Pv.pledgeability FirmType.L * (1 - Pv.depreciation) *
        Z.controlsOne.inflation * Z.controlsOne.capitalPrice *
        Z.stateOne.capitalL ≠ 0) :
    let y := reserveRemunerationSlice 0 h
    let Pv := initialIntervenedPrimitives P (localScalarParameterIntervention y)
    let Z := localPrefixLogChart Z0 (solutionLog y)
    localReducedPrefixResidual LocalPrefixBranch.binding Pv I Z
      dateOne recurrent tail LocalPrefixEquation.firmRegimeZeroL = 0 := by
  let y := reserveRemunerationSlice 0 h
  let Pv := initialIntervenedPrimitives P (localScalarParameterIntervention y)
  let Z := localPrefixLogChart Z0 (solutionLog y)
  have hslack : localNormalizedSlackL Pv Z = (0 : ℝ) :=
    source_row_five_recovers_normalized_slack
      P I Z0 dateOne recurrent tail solutionLog 0 h hrow
  exact source_binding_face_row_of_zero_normalized_slack
    Pv I Z dateOne recurrent tail hden hslack

#print axioms source_binding_face_row_of_zero_normalized_slack
#print axioms economic_boundary_B_row_from_source_row_five

end ProposedLocalScalarOriginalBoundaryBBranch
end Ventura26LiquidityAllocation
