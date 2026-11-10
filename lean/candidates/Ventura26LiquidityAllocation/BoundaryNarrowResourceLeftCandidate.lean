import Ventura26LiquidityAllocation.BoundaryNarrowDepositBoxCandidate

/-!
# Exact SOURCE narrow-left real capital and normalized-output enclosures

The goal is a direct SOURCE-side resource-residual sign, not another
conditional no-equilibrium theorem. This candidate derives two component
bounds by rational cross multiplication and fifteenth-power comparison.
All original stationary quantities remain tied to the SOURCE primitives;
neither a fitted root nor the independent interval audit enters as an axiom.

This file must pass the pinned boundary CI and the transitive axiom audit
before either claimed bound is marked kernel-checked.
-/

namespace Ventura26LiquidityAllocation
namespace ProposedBoundaryNarrowResourceLeft

open ProposedStationaryBank
open ProposedStationaryRealScale
open ProposedBoundaryBridge
open ProposedBoundaryResourceRoot
open ProposedBoundaryEndpointBoxes
open ProposedBoundaryNormalizationBridge
open ProposedBoundaryNarrowDepositBox

/-- Narrow SOURCE capital scaling, obtained from the sharp SOURCE bank
user-cost box and the exact continuation-value/capital-price formula. -/
theorem source_narrow_left_capital_scale_box :
    (99780498 / 100000000 : ℝ) <
      boundaryCapitalScale (1029135 / 1000000 : ℝ) ∧
    boundaryCapitalScale (1029135 / 1000000 : ℝ) <
      (99780499 / 100000000 : ℝ) := by
  let R : ℝ := 1029135 / 1000000
  have hRpos : 0 < R := by
    dsimp [R]
    norm_num
  rcases (boundary_source_user_cost_sharp_boxes).2 with
    ⟨huLlo, huLhi⟩
  have hJ : liquidationValue = (3159 / 3200 : ℝ) := by
    norm_num [liquidationValue, capitalPrice]
  have hV :
      continuationReturn .L =
        userCost .L + (3159 / 3200 : ℝ) := by
    unfold continuationReturn
    rw [hJ]
  have hden :
      0 < 2 * continuationReturn .L - (41 / 40 : ℝ) * R := by
    rw [hV]
    dsimp [R]
    linarith only [huLlo]
  change (99780498 / 100000000 : ℝ) < boundaryCapitalScale R ∧
    boundaryCapitalScale R < (99780499 / 100000000 : ℝ)
  rw [boundaryCapitalScale_rewrite R (ne_of_gt hRpos)]
  constructor
  · apply (lt_div_iff₀ hden).2
    rw [hV]
    dsimp [R]
    linarith only [huLhi]
  · apply (div_lt_iff₀ hden).2
    rw [hV]
    dsimp [R]
    linarith only [huLlo]

/-- Narrow upper enclosure of SOURCE normalized output at the LEFT
resource endpoint. The 15th-root upper inequality is derived from
an exact integer-power comparison, so no floating-point proof step
or independent surrogate output function is invoked. -/
theorem source_narrow_left_normalized_output_upper :
    normalizedOutput (1029135 / 1000000 : ℝ) <
      (1335240 / 100000 : ℝ) := by
  let R : ℝ := 1029135 / 1000000
  have hRmem : R ∈ boundaryInterval := by
    change boundaryLo ≤ R ∧ R ≤ boundaryHi
    dsimp [R]
    norm_num [boundaryLo, boundaryHi]
  have hspos : 0 < boundaryCapitalScale R :=
    (boundary_scale_and_investment_domain hRmem).1
  have hrdpos : 0 < boundaryDepositRate R :=
    lt_trans (by norm_num : (0 : ℝ) < 10271879 / 10000000)
      source_narrow_left_deposit_rate_box.1
  have hsupper := source_narrow_left_capital_scale_box.2
  have hrdupper := source_narrow_left_deposit_rate_box.2
  have hspow :
      boundaryCapitalScale R ^ (8 : ℕ) <
        (99780499 / 100000000 : ℝ) ^ (8 : ℕ) := by
    gcongr
  have hscaledDeposit :
      (99 / 100 : ℝ) * boundaryDepositRate R <
        (99 / 100 : ℝ) * (10271880 / 10000000 : ℝ) :=
    mul_lt_mul_of_pos_left hrdupper (by norm_num)
  have hdpow :
      ((99 / 100 : ℝ) * boundaryDepositRate R) ^ (5 : ℕ) <
        ((99 / 100 : ℝ) * (10271880 / 10000000 : ℝ)) ^ (5 : ℕ) := by
    gcongr
  let x : ℝ :=
    boundaryCapitalScale R ^ (8 : ℕ) *
      ((99 / 100 : ℝ) * boundaryDepositRate R) ^ (5 : ℕ)
  have hx : 0 ≤ x := by
    dsimp [x]
    exact mul_nonneg (pow_nonneg hspos.le _)
      (pow_nonneg (mul_nonneg (by norm_num) hrdpos.le) _)
  have hm1 :
      boundaryCapitalScale R ^ (8 : ℕ) *
          ((99 / 100 : ℝ) * boundaryDepositRate R) ^ (5 : ℕ) <
      (99780499 / 100000000 : ℝ) ^ (8 : ℕ) *
          ((99 / 100 : ℝ) * boundaryDepositRate R) ^ (5 : ℕ) :=
    mul_lt_mul_of_pos_right hspow
      (pow_pos (mul_pos (by norm_num) hrdpos) _)
  have hm2 :
      (99780499 / 100000000 : ℝ) ^ (8 : ℕ) *
          ((99 / 100 : ℝ) * boundaryDepositRate R) ^ (5 : ℕ) <
      (99780499 / 100000000 : ℝ) ^ (8 : ℕ) *
          ((99 / 100 : ℝ) * (10271880 / 10000000 : ℝ)) ^ (5 : ℕ) :=
    mul_lt_mul_of_pos_left hdpow (by norm_num)
  have hpoly : x ≤ (100443 / 100000 : ℝ) ^ (15 : ℕ) := by
    calc
      x <
        (99780499 / 100000000 : ℝ) ^ (8 : ℕ) *
          ((99 / 100 : ℝ) * (10271880 / 10000000 : ℝ)) ^ (5 : ℕ) :=
        lt_trans hm1 hm2
      _ ≤ (100443 / 100000 : ℝ) ^ (15 : ℕ) := by norm_num
  have hroot : x ^ (1 / 15 : ℝ) ≤ (100443 / 100000 : ℝ) :=
    (fifteenth_root_between 0 (100443 / 100000 : ℝ) x
      (by norm_num) (by norm_num) hx
      (by simpa using hx) hpoly).2
  have hYpos : 0 < outputScale :=
    aggregate_scales_pos.2.1
  have hYhi := boundary_source_output_scale_sharp_box.2
  change outputScale * x ^ (1 / 15 : ℝ) <
    (1335240 / 100000 : ℝ)
  calc
    outputScale * x ^ (1 / 15 : ℝ) ≤
        outputScale * (100443 / 100000 : ℝ) :=
      mul_le_mul_of_nonneg_left hroot hYpos.le
    _ < (13293504 / 1000000 : ℝ) * (100443 / 100000 : ℝ) :=
      mul_lt_mul_of_pos_right hYhi (by norm_num)
    _ < (1335240 / 100000 : ℝ) := by norm_num

#print axioms source_narrow_left_capital_scale_box
#print axioms source_narrow_left_normalized_output_upper

end ProposedBoundaryNarrowResourceLeft
end Ventura26LiquidityAllocation
