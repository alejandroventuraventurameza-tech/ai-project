import Ventura26LiquidityAllocation.FrozenInheritanceImpactPrefixCandidate

/-!
# SOURCE's endogenous inherited firm promises: exact budget-row diagnostic

This is a stress test, NOT a candidate complete fixed-inheritance
equilibrium: retain the old SOURCE date-zero capital and current controls,
but restore the original inherited entrepreneurial promises (firmFace).
The resulting original firm-budget residuals are positive *in the
aggregate*. It shows why the old reduced prefix cannot simply be relabeled
as an unanticipated shock. When constructing the genuine frozen-state
equilibrium, *all current prices, investment and consumption are unknown*
and must be jointly re-solved.

The exact affine budget identity holds for any source date data. The
uniform >0.11 aggregate gap below uses a previously certified source
inequality, not floating point evaluation or a new numerical axiom.
-/

namespace Ventura26LiquidityAllocation
namespace ProposedFrozenInheritanceFirmBudgetDiagnostic

open ProposedStationaryPrimitives
open ProposedStationaryInheritedState
open ProposedStationaryRealScale
open ProposedBoundaryResourceRoot
open ProposedBoundaryBridge
open ProposedBoundaryFullPrefix
open ProposedFirmFaceUniformGap
open ProposedFrozenInheritanceImpactPrefix

/-- This constructor restores ONLY the original firm's inherited
promises; installed capital and the old policy-dependent impact controls
are intentionally left unchanged for an isolated accounting test. -/
noncomputable def firmFacesOnlyFrozenZero (G R : ℝ) :
    LocalPrefixDateData :=
  { boundaryZeroData G R with inheritedFace := firmFace }

/-- Original SOURCE firm-budget accounting is exactly affine in
inherited nominal firm face, holding all contemporaneous choices fixed.
This algebra requires no positivity, optimality, equilibrium or root. -/
theorem original_firm_budget_residual_affine_in_inherited_face
    (P : Primitives LocalBridgePhase) (d : LocalPrefixDateData)
    (faces : FirmType → ℝ) (i : FirmType) :
    localReducedFirmBudgetResidual P
        { d with inheritedFace := faces } i =
      localReducedFirmBudgetResidual P d i +
        (faces i - d.inheritedFace i) / d.controls.inflation := by
  have hProfit :
      localPrefixOperatingProfit P
        { d with inheritedFace := faces } i =
      localPrefixOperatingProfit P d i := by rfl
  unfold localReducedFirmBudgetResidual localPrefixFirmWealth
  dsimp only
  rw [hProfit]
  ring

/-- The old SOURCE budget row was zero precisely because it wrote its
inherited firm promise as the residual. Restore the true predecessor's
face WITHOUT changing the old impact decisions, and the row becomes
that nominal-promise discrepancy itself (date-zero inflation is 1). -/
theorem frozen_firm_face_budget_row_exact
    (G R : ℝ) (i : FirmType) (hR : 0 < R) :
    localReducedFirmBudgetResidual (boundaryPrimitives G R)
      (firmFacesOnlyFrozenZero G R) i =
    firmFace i -
      boundaryInheritedFace G R (boundaryZeroSeed G R) i := by
  have hOldBudget :
      localReducedFirmBudgetResidual (boundaryPrimitives G R)
        (boundaryZeroData G R) i = 0 :=
    (boundary_zero_firm_rows G R hR .binding i).1
  have hInflation : (boundaryZeroData G R).controls.inflation = 1 := by rfl
  have hOldFace : (boundaryZeroData G R).inheritedFace i =
      boundaryInheritedFace G R (boundaryZeroSeed G R) i := by rfl
  calc
    localReducedFirmBudgetResidual (boundaryPrimitives G R)
        (firmFacesOnlyFrozenZero G R) i =
      localReducedFirmBudgetResidual (boundaryPrimitives G R)
        (boundaryZeroData G R) i +
        (firmFace i - (boundaryZeroData G R).inheritedFace i) /
          (boundaryZeroData G R).controls.inflation := by
            exact original_firm_budget_residual_affine_in_inherited_face
              (boundaryPrimitives G R) (boundaryZeroData G R) firmFace i
    _ = firmFace i -
        boundaryInheritedFace G R (boundaryZeroSeed G R) i := by
          rw [hOldBudget, hInflation, hOldFace]
          ring

/-- QUANTITATIVE FAILURE of the old SOURCE prefix if its face stocks
are not recomputed: even under the SOURCE capital/controls (rather than
the genuinely frozen capital), the mass-weighted sum of the original
date-zero entrepreneurial budget residuals exceeds 0.11. -/
theorem face_only_frozen_aggregate_firm_budget_gt_11_percent
    (G R : ℝ)
    (hlo : (1029135 / 1000000 : ℝ) ≤ R)
    (hhi : R ≤ (1029136 / 1000000 : ℝ)) :
    (11 / 100 : ℝ) <
      (∑ i, (primitives G).mass i *
        localReducedFirmBudgetResidual (boundaryPrimitives G R)
          (firmFacesOnlyFrozenZero G R) i) := by
  have hRpos : 0 < R := lt_of_lt_of_le (by norm_num) hlo
  have hH := frozen_firm_face_budget_row_exact G R .H hRpos
  have hL := frozen_firm_face_budget_row_exact G R .L hRpos
  have hSame :
      (∑ i, (primitives G).mass i *
        localReducedFirmBudgetResidual (boundaryPrimitives G R)
          (firmFacesOnlyFrozenZero G R) i) =
      (∑ i, (primitives G).mass i *
        ((inheritedState G).firmFace i -
          boundaryInheritedFace G R (boundaryZeroSeed G R) i)) := by
    simp only [sum_firmType_eq_H_add_L]
    rw [hH, hL]
    rfl
  rw [hSame]
  exact source_uniform_firm_face_decline_gt_11_percent G R hlo hhi

/-- In particular both original SOURCE date-zero firm budgets cannot
still hold after restoring the old faces while keeping the old
impact choices fixed. It is NOT a no-equilibrium result for the new
fixed-inheritance model, whose 33 coordinates remain endogenous. -/
theorem old_SOURCE_controls_not_both_budget_feasible_after_face_freeze
    (G R : ℝ)
    (hlo : (1029135 / 1000000 : ℝ) ≤ R)
    (hhi : R ≤ (1029136 / 1000000 : ℝ)) :
    ¬ (localReducedFirmBudgetResidual (boundaryPrimitives G R)
          (firmFacesOnlyFrozenZero G R) .H = 0 ∧
        localReducedFirmBudgetResidual (boundaryPrimitives G R)
          (firmFacesOnlyFrozenZero G R) .L = 0) := by
  intro hBoth
  have hAggregate :=
    face_only_frozen_aggregate_firm_budget_gt_11_percent G R hlo hhi
  rw [sum_firmType_eq_H_add_L] at hAggregate
  rw [hBoth.1, hBoth.2] at hAggregate
  norm_num at hAggregate

#print axioms original_firm_budget_residual_affine_in_inherited_face
#print axioms frozen_firm_face_budget_row_exact
#print axioms face_only_frozen_aggregate_firm_budget_gt_11_percent
#print axioms old_SOURCE_controls_not_both_budget_feasible_after_face_freeze

end ProposedFrozenInheritanceFirmBudgetDiagnostic
end Ventura26LiquidityAllocation
