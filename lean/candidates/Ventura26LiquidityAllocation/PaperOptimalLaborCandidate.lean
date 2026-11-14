import Ventura26LiquidityAllocation.PaperAllocationSourceAlgebraBridgeCandidate

/-!
# Lemma 4.3: conditional global optimality of labor across two firms

With capital fixed and COMMON Cobb-Douglas elasticities, this module
derives the weighted global bound on micro output, not merely the
first-order allocation or a definition of aggregate output.

The theorem is stated using nonnegative normalized labor multipliers
xH,xL. The separate change of variables from arbitrary original labor
allocations remains a source-interface bridge obligation.

No dynamic competitive-equilibrium or monetary comparative static is
claimed.
-/

namespace Ventura26LiquidityAllocation
namespace ProposedPaperOptimalLabor

/-- With fixed positive weights and a linear labor budget, diminishing
returns to labor ensure that the normalized allocation xH=xL=1 is a
GLOBAL optimum. Proof reduces to the already checked three-factor
weighted AM-GM inequality with a=0,d=1-b. -/
theorem normalized_labor_global_bound
    (wH wL xH xL b : ℝ)
    (hwH : 0 < wH) (hwL : 0 < wL)
    (hxH : 0 ≤ xH) (hxL : 0 ≤ xL)
    (hb0 : 0 < b) (hb1 : b < 1)
    (hbudget : wH * xH + wL * xL = wH + wL) :
    wH * xH ^ b + wL * xL ^ b ≤ wH + wL := by
  have hcapital : wH * (1 : ℝ) + wL * 1 = wH + wL := by ring
  have hbound :=
    ProposedPaperAllocationEfficiencySupport.normalized_two_type_output_le_benchmark
      (0 : ℝ) b (1 - b) wH wL 1 1 xH xL
      (by norm_num) hb0.le (by linarith)
      (by ring) hwH.le hwL.le
      (by norm_num) (by norm_num) hxH hxL hcapital hbudget
  simpa using hbound

/-- Evaluate the ORIGINAL individual Cobb-Douglas technology at
a proportional labor allocation, further scaled by x≥0. -/
theorem source_output_with_scaled_labor
    (A k L G a b x : ℝ)
    (hA : 0 < A) (hk : 0 < k)
    (hL : 0 < L) (hG : 0 < G)
    (hb : b < 1) (hx : 0 ≤ x) :
    let g := A ^ (1 / (1 - b)) * k ^ (a / (1 - b))
    A * k ^ a * (L * g / G * x) ^ b =
      (L / G) ^ b * g * x ^ b := by
  let g : ℝ := A ^ (1 / (1 - b)) * k ^ (a / (1 - b))
  change A * k ^ a * (L * g / G * x) ^ b =
    (L / G) ^ b * g * x ^ b
  have hg : 0 < g := by
    dsimp [g]
    exact mul_pos (Real.rpow_pos_of_pos hA _) (Real.rpow_pos_of_pos hk _)
  have hbase : A * k ^ a * (L * g / G) ^ b =
      (L / G) ^ b * g :=
    ProposedPaperAllocationSourceAlgebraBridge.source_output_at_weighted_labor
      A k L G a b hA hk hL hG hb
  have hscale : (L * g / G * x) ^ b =
      (L * g / G) ^ b * x ^ b :=
    Real.mul_rpow (div_pos (mul_pos hL hg) hG).le hx
  calc
    A * k ^ a * (L * g / G * x) ^ b =
      (A * k ^ a * (L * g / G) ^ b) * x ^ b := by
        rw [hscale]
        ring
    _ = (L / G) ^ b * g * x ^ b := by rw [hbase]

/-- A full GLOBAL output bound for the original, two-type
Cobb-Douglas technology with fixed capital and normalized labor
multipliers satisfying the EXACT weighted labor budget. This avoids
assuming the paper's aggregate Y formula as a definition. -/
theorem source_two_type_global_labor_optimality
    (vH vL AH AL kH kL L a b xH xL : ℝ)
    (hvH : 0 < vH) (hvL : 0 < vL)
    (hAH : 0 < AH) (hAL : 0 < AL)
    (hkH : 0 < kH) (hkL : 0 < kL)
    (hL : 0 < L)
    (hb0 : 0 < b) (hb1 : b < 1)
    (hxH : 0 ≤ xH) (hxL : 0 ≤ xL)
    (hbudget :
      let gH := AH ^ (1 / (1 - b)) * kH ^ (a / (1 - b))
      let gL := AL ^ (1 / (1 - b)) * kL ^ (a / (1 - b))
      vH * gH * xH + vL * gL * xL = vH * gH + vL * gL) :
    let gH := AH ^ (1 / (1 - b)) * kH ^ (a / (1 - b))
    let gL := AL ^ (1 / (1 - b)) * kL ^ (a / (1 - b))
    let G := vH * gH + vL * gL
    vH * (AH * kH ^ a * (L * gH / G * xH) ^ b) +
      vL * (AL * kL ^ a * (L * gL / G * xL) ^ b) ≤
      L ^ b * G ^ (1 - b) := by
  let gH : ℝ := AH ^ (1 / (1 - b)) * kH ^ (a / (1 - b))
  let gL : ℝ := AL ^ (1 / (1 - b)) * kL ^ (a / (1 - b))
  let G : ℝ := vH * gH + vL * gL
  change vH * (AH * kH ^ a * (L * gH / G * xH) ^ b) +
      vL * (AL * kL ^ a * (L * gL / G * xL) ^ b) ≤
      L ^ b * G ^ (1 - b)
  have hgH : 0 < gH := by
    dsimp [gH]
    exact mul_pos (Real.rpow_pos_of_pos hAH _) (Real.rpow_pos_of_pos hkH _)
  have hgL : 0 < gL := by
    dsimp [gL]
    exact mul_pos (Real.rpow_pos_of_pos hAL _) (Real.rpow_pos_of_pos hkL _)
  have hG : 0 < G := by
    dsimp [G]
    exact add_pos (mul_pos hvH hgH) (mul_pos hvL hgL)
  have hnormalizedBudget :
      (vH * gH) * xH + (vL * gL) * xL =
        (vH * gH) + (vL * gL) := by
    calc
      (vH * gH) * xH + (vL * gL) * xL =
          vH * gH * xH + vL * gL * xL := by ring
      _ = vH * gH + vL * gL := hbudget
  have hnorm :
      (vH * gH) * xH ^ b + (vL * gL) * xL ^ b ≤
        (vH * gH) + (vL * gL) :=
    normalized_labor_global_bound
      (vH * gH) (vL * gL) xH xL b
      (mul_pos hvH hgH) (mul_pos hvL hgL)
      hxH hxL hb0 hb1 hnormalizedBudget
  have hfirmH : AH * kH ^ a * (L * gH / G * xH) ^ b =
      (L / G) ^ b * gH * xH ^ b :=
    source_output_with_scaled_labor
      AH kH L G a b xH hAH hkH hL hG hb1 hxH
  have hfirmL : AL * kL ^ a * (L * gL / G * xL) ^ b =
      (L / G) ^ b * gL * xL ^ b :=
    source_output_with_scaled_labor
      AL kL L G a b xL hAL hkL hL hG hb1 hxL
  calc
    vH * (AH * kH ^ a * (L * gH / G * xH) ^ b) +
        vL * (AL * kL ^ a * (L * gL / G * xL) ^ b) =
      (L / G) ^ b *
        ((vH * gH) * xH ^ b + (vL * gL) * xL ^ b) := by
          rw [hfirmH, hfirmL]
          ring
    _ ≤ (L / G) ^ b * (vH * gH + vL * gL) :=
      mul_le_mul_of_nonneg_left hnorm (Real.rpow_nonneg (div_pos hL hG).le b)
    _ = L ^ b * G ^ (1 - b) := by
      change (L / G) ^ b * G = L ^ b * G ^ (1 - b)
      exact ProposedPaperAllocationSourceAlgebraBridge.positive_labor_aggregate_power
        L G b hL hG

/-- The upper bound is actually attained, not merely an upper
bound: use xH=xL=1 and the source production identity. -/
theorem source_labor_global_bound_attained
    (vH vL AH AL kH kL L a b : ℝ)
    (hvH : 0 < vH) (hvL : 0 < vL)
    (hAH : 0 < AH) (hAL : 0 < AL)
    (hkH : 0 < kH) (hkL : 0 < kL)
    (hL : 0 < L) (hb : b < 1) :
    let gH := AH ^ (1 / (1 - b)) * kH ^ (a / (1 - b))
    let gL := AL ^ (1 / (1 - b)) * kL ^ (a / (1 - b))
    let G := vH * gH + vL * gL
    vH * (AH * kH ^ a * (L * gH / G * (1 : ℝ)) ^ b) +
      vL * (AL * kL ^ a * (L * gL / G * (1 : ℝ)) ^ b) =
      L ^ b * G ^ (1 - b) := by
  let gH : ℝ := AH ^ (1 / (1 - b)) * kH ^ (a / (1 - b))
  let gL : ℝ := AL ^ (1 / (1 - b)) * kL ^ (a / (1 - b))
  let G : ℝ := vH * gH + vL * gL
  change vH * (AH * kH ^ a * (L * gH / G * (1 : ℝ)) ^ b) +
      vL * (AL * kL ^ a * (L * gL / G * (1 : ℝ)) ^ b) =
      L ^ b * G ^ (1 - b)
  simp only [mul_one]
  exact ProposedPaperAllocationSourceAlgebraBridge.source_two_type_output_at_optimal_labor
    vH vL AH AL kH kL L a b hvH hvL hAH hAL hkH hkL hL hb

#print axioms normalized_labor_global_bound
#print axioms source_output_with_scaled_labor
#print axioms source_two_type_global_labor_optimality
#print axioms source_labor_global_bound_attained

end ProposedPaperOptimalLabor
end Ventura26LiquidityAllocation
