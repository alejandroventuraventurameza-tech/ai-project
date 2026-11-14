import Ventura26LiquidityAllocation.LocalScalarOriginalInteriorSBranchCandidate
import Ventura26LiquidityAllocation.LocalScalarOriginalBoundaryBBranchCandidate

/-!
# Positivity of the 33 original economic levels in the actual log chart

If the source reference Z0 has positive 33 coordinates, every chart
point Z_j=Z0_j*exp z_j is positive, without restrictions on z.

This discharges the formerly separate nonzero LOAN RATE assumption in
the S-row recovery and the nonzero collateral pledge denominator in
the B-row recovery, under two economically meaningful primitive
conditions: L pledgeability strictly positive and depreciation <1.

No positive-domain witness for the actual baseline Z0 or primitive
parameters is manufactured here. The source Jacobian certificate
explicitly carries LocalPrefixCoordinatesPositive Z0 as a premise.
-/

namespace Ventura26LiquidityAllocation
namespace ProposedLocalScalarPositiveLogChartDomain

open ProposedLocalScalarOriginalInteriorSBranch
open ProposedLocalScalarOriginalBoundaryBBranch
open ProposedLocalScalarEconomicSlice

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- The 33 economic coordinates reconstructed from the 33-vector
are the exact original components, in the order in EconomicModel. -/
theorem localPrefixCoordinatesVector_ofVector_at
    (x : Fin 33 → ℝ) (j : Fin 33) :
    localPrefixCoordinatesVector (localPrefixCoordinatesOfVector x) j = x j := by
  fin_cases j <;> rfl

/-- All 33 original positive economic coordinates remain positive
under arbitrary log perturbations, not only infinitesimal ones. -/
theorem localPrefixLogChart_positive
    (Z0 : LocalPrefixCoordinates)
    (hbase : LocalPrefixCoordinatesPositive Z0)
    (z : Fin 33 → ℝ) :
    LocalPrefixCoordinatesPositive (localPrefixLogChart Z0 z) := by
  intro j
  change 0 < localPrefixCoordinatesVector (localPrefixLogChart Z0 z) j
  rw [localPrefixLogChart, localPrefixCoordinatesVector_ofVector_at]
  exact mul_pos (hbase j) (Real.exp_pos (z j))

/-- Index 15 of the exact 33-vector is the date-zero gross loan rate. -/
theorem localPrefixLogChart_loanRate_pos
    (Z0 : LocalPrefixCoordinates)
    (hbase : LocalPrefixCoordinatesPositive Z0)
    (z : Fin 33 → ℝ) :
    0 < (localPrefixLogChart Z0 z).controlsZero.loanRate := by
  have h := localPrefixLogChart_positive Z0 hbase z (15 : Fin 33)
  exact h

/-- Index 1 is L's installed capital at date one, indexes 28 and 29
are the date-one inflation and capital price. -/
theorem localPrefixLogChart_collateral_components_pos
    (Z0 : LocalPrefixCoordinates)
    (hbase : LocalPrefixCoordinatesPositive Z0)
    (z : Fin 33 → ℝ) :
    0 < (localPrefixLogChart Z0 z).stateOne.capitalL ∧
    0 < (localPrefixLogChart Z0 z).controlsOne.inflation ∧
    0 < (localPrefixLogChart Z0 z).controlsOne.capitalPrice := by
  have hc := localPrefixLogChart_positive Z0 hbase z
  exact ⟨hc (1 : Fin 33), hc (28 : Fin 33), hc (29 : Fin 33)⟩

/-- The pledge denominator of the ORIGINAL B firm-L face equation
cannot vanish if pledgeability is positive, depreciation is below
one, and the exact log chart is based at positive coordinates. -/
theorem localPrefixLogChart_L_collateral_denominator_pos
    (P : Primitives S) (Z0 : LocalPrefixCoordinates)
    (hbase : LocalPrefixCoordinatesPositive Z0)
    (z : Fin 33 → ℝ)
    (hpledge : 0 < P.pledgeability FirmType.L)
    (hdepr : P.depreciation < 1) :
    0 < P.pledgeability FirmType.L * (1 - P.depreciation) *
      (localPrefixLogChart Z0 z).controlsOne.inflation *
      (localPrefixLogChart Z0 z).controlsOne.capitalPrice *
      (localPrefixLogChart Z0 z).stateOne.capitalL := by
  obtain ⟨hcapital, hinfl, hprice⟩ :=
    localPrefixLogChart_collateral_components_pos Z0 hbase z
  have hret : 0 < 1 - P.depreciation := by linarith
  exact mul_pos (mul_pos (mul_pos (mul_pos hpledge hret) hinfl) hprice) hcapital

/-- The loan rate required for the original S funding Euler row is
automatically nonzero in any positive log chart. -/
theorem economic_log_solution_loanRate_ne_zero
    (Z0 : LocalPrefixCoordinates)
    (hbase : LocalPrefixCoordinatesPositive Z0)
    (solutionLog : (Fin 5 → ℝ) → (Fin 33 → ℝ))
    (s h : ℝ) :
    (localPrefixLogChart Z0
      (solutionLog (reserveRemunerationSlice s h))).controlsZero.loanRate ≠ 0 := by
  exact ne_of_gt (localPrefixLogChart_loanRate_pos Z0 hbase
    (solutionLog (reserveRemunerationSlice s h)))

/-- The denominator premise used for the original B collateral row
is automatic on the source policy slice once the primitive domain
and the original 33 positive baseline coordinates are given. -/
theorem economic_log_solution_B_denominator_ne_zero
    (P : Primitives S) (Z0 : LocalPrefixCoordinates)
    (hbase : LocalPrefixCoordinatesPositive Z0)
    (solutionLog : (Fin 5 → ℝ) → (Fin 33 → ℝ))
    (h : ℝ)
    (hpledge : 0 < P.pledgeability FirmType.L)
    (hdepr : P.depreciation < 1) :
    let y := reserveRemunerationSlice 0 h
    let Pv := initialIntervenedPrimitives P (localScalarParameterIntervention y)
    let Z := localPrefixLogChart Z0 (solutionLog y)
    Pv.pledgeability FirmType.L * (1 - Pv.depreciation) *
      Z.controlsOne.inflation * Z.controlsOne.capitalPrice *
      Z.stateOne.capitalL ≠ 0 := by
  have hpos := localPrefixLogChart_L_collateral_denominator_pos
    P Z0 hbase (solutionLog (reserveRemunerationSlice 0 h))
    hpledge hdepr
  change (initialIntervenedPrimitives P
    (localScalarParameterIntervention (reserveRemunerationSlice 0 h))).pledgeability
      FirmType.L *
    (1 - (initialIntervenedPrimitives P
      (localScalarParameterIntervention (reserveRemunerationSlice 0 h))).depreciation) *
    (localPrefixLogChart Z0
      (solutionLog (reserveRemunerationSlice 0 h))).controlsOne.inflation *
    (localPrefixLogChart Z0
      (solutionLog (reserveRemunerationSlice 0 h))).controlsOne.capitalPrice *
    (localPrefixLogChart Z0
      (solutionLog (reserveRemunerationSlice 0 h))).stateOne.capitalL ≠ 0
  simpa only [initialIntervenedPrimitives] using (ne_of_gt hpos)

#print axioms localPrefixCoordinatesVector_ofVector_at
#print axioms localPrefixLogChart_positive
#print axioms localPrefixLogChart_loanRate_pos
#print axioms localPrefixLogChart_collateral_components_pos
#print axioms localPrefixLogChart_L_collateral_denominator_pos
#print axioms economic_log_solution_loanRate_ne_zero
#print axioms economic_log_solution_B_denominator_ne_zero

end ProposedLocalScalarPositiveLogChartDomain
end Ventura26LiquidityAllocation
