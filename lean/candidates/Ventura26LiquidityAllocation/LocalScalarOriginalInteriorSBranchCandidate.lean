import Ventura26LiquidityAllocation.LocalScalarOriginalCollateralKktBridgeCandidate
import Ventura26LiquidityAllocation.LocalScalarOriginalEulerRowsCandidate

/-!
# Interior scalar root -> original two S-regime firm-L rows and KKT

The source's 33-row modified system is built in the binding regime,
except that row 5 is replaced by the PRESCRIBED normalized collateral
slack. An interior root has s>0 and M(s,h)=0. The actual source
row 5 identifies s with the recovered collateral slack, hence the
literal L KKT dual vanishes. Row 3 then transfers from the source
binding Euler form to the original S form.

This module makes the economic branch interpretation precise for the
date-zero L firm and requires a nonzero loan rate. It does NOT claim
that the remaining dynamic allocation, terminal tails, all-agent
optimality or the equilibrium existence problem have been solved.
-/

namespace Ventura26LiquidityAllocation
namespace ProposedLocalScalarOriginalInteriorSBranch

open ProposedLocalScalarEconomicSlice
open ProposedLocalScalarOriginalCollateralKktBridge
open ProposedLocalScalarOriginalEulerRows
open ProposedScalarComplementarityMultiplicity

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- On the actual reduced source coordinates, a positive scalar
complementarity root together with modified source rows 3 and 5
satisfies the literal firm-L collateral KKT block, the original
S-regime funding row, and the original S-regime capital Euler row.
The nonzero loan rate is needed for the funding-row equivalence. -/
theorem interior_root_recovers_original_S_firm_L_rows
    (P : Primitives S) (I : InheritedState) (Z0 : LocalPrefixCoordinates)
    (dateOne recurrent : S) (tail : LocalPrefixContinuationRule)
    (solutionLog : (Fin 5 → ℝ) → (Fin 33 → ℝ))
    (s h : ℝ) (hs : 0 < s)
    (hrow3 : localBindingResidualWithSlack P I Z0 dateOne recurrent tail
      (reserveRemunerationSlice s h)
      (solutionLog (reserveRemunerationSlice s h)) (3 : Fin 33) = 0)
    (hrow5 : localBindingResidualWithSlack P I Z0 dateOne recurrent tail
      (reserveRemunerationSlice s h)
      (solutionLog (reserveRemunerationSlice s h)) (5 : Fin 33) = 0)
    (hscalar : ScalarComplementarity
      (fun x => economicReserveRemunerationMarginal P Z0 solutionLog x h) s)
    (hloan : (localPrefixLogChart Z0
      (solutionLog (reserveRemunerationSlice s h))).controlsZero.loanRate ≠ 0) :
    let y := reserveRemunerationSlice s h
    let Pv := initialIntervenedPrimitives P (localScalarParameterIntervention y)
    let Z := localPrefixLogChart Z0 (solutionLog y)
    LocalScalarComplementarityL Pv Z ∧
    localReducedPrefixResidual LocalPrefixBranch.slack Pv I Z
      dateOne recurrent tail LocalPrefixEquation.firmRegimeZeroL = 0 ∧
    localReducedPrefixResidual LocalPrefixBranch.slack Pv I Z
      dateOne recurrent tail LocalPrefixEquation.firmCapitalEulerZeroL = 0 := by
  let y := reserveRemunerationSlice s h
  let Pv := initialIntervenedPrimitives P (localScalarParameterIntervention y)
  let Z := localPrefixLogChart Z0 (solutionLog y)
  have hKKT : LocalScalarComplementarityL Pv Z :=
    source_scalar_complementarity_recovers_original_L_KKT
      P I Z0 dateOne recurrent tail solutionLog s h hrow5 hscalar
  have hslack : localNormalizedSlackL Pv Z = s :=
    source_row_five_recovers_normalized_slack
      P I Z0 dateOne recurrent tail solutionLog s h hrow5
  have hslackpos : 0 < localNormalizedSlackL Pv Z := by
    rw [hslack]
    exact hs
  have hdual : localNormalizedCollateralDualL Pv Z = 0 := by
    rcases mul_eq_zero.mp hKKT.2.2 with hzeroSlack | hzeroDual
    · exact False.elim ((ne_of_gt hslackpos) hzeroSlack)
    · exact hzeroDual
  have hB : localReducedPrefixResidual LocalPrefixBranch.binding Pv I Z
      dateOne recurrent tail LocalPrefixEquation.firmCapitalEulerZeroL = 0 := by
    simpa [localBindingResidualWithSlack, localPrefixEquationOfIndex,
      y, Pv, Z] using hrow3
  refine ⟨hKKT, ?_, ?_⟩
  · exact source_original_S_funding_row_zero Pv I Z
      dateOne recurrent tail hloan hdual
  · exact source_original_S_capital_euler_row_zero Pv I Z
      dateOne recurrent tail hB hdual

#print axioms interior_root_recovers_original_S_firm_L_rows

end ProposedLocalScalarOriginalInteriorSBranch
end Ventura26LiquidityAllocation
