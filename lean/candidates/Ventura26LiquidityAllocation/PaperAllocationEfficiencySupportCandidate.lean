import Ventura26LiquidityAllocation.PaperInterface
import Mathlib.Analysis.MeanInequalities

/-!
# Lemma 4.3: global supporting inequality for two-type efficient allocation

This independent lemma converts normalized fixed-aggregate constraints into
a GLOBAL output bound using the three-factor weighted arithmetic/geometric
mean inequality, not merely first-order conditions. It also proves the
non-negativity of the associated normalized log-output gap and checks that
the proposed efficient distribution exhausts both aggregate resources.

The source-model bridge still must identify its Cobb-Douglas output, capital,
labor and productivity normalizations with the mathematical objects below.
This file does NOT prove the entire original allocationLossIdentitySpec:
the exact rpow change of variables and optimal-labor expression have not
yet been transported to the source interface.
-/

namespace Ventura26LiquidityAllocation
namespace ProposedPaperAllocationEfficiencySupport

/-- Fixed weighted capital and labor budgets force the normalized
two-type Cobb-Douglas output below the efficient unit-input benchmark.
The exponents a,b,d are nonnegative and sum to one; both firm types
share the same exponents. This is global, not just an Euler/KKT test. -/
theorem normalized_two_type_output_le_benchmark
    (a b d wH wL xH xL yH yL : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hd : 0 ≤ d)
    (hsum : a + b + d = 1)
    (hwH : 0 ≤ wH) (hwL : 0 ≤ wL)
    (hxH : 0 ≤ xH) (hxL : 0 ≤ xL)
    (hyH : 0 ≤ yH) (hyL : 0 ≤ yL)
    (hcapital : wH * xH + wL * xL = wH + wL)
    (hlabor : wH * yH + wL * yL = wH + wL) :
    wH * (xH ^ a * yH ^ b) +
        wL * (xL ^ a * yL ^ b) ≤ wH + wL := by
  have hH : xH ^ a * yH ^ b ≤ a * xH + b * yH + d := by
    have h := Real.geom_mean_le_arith_mean3_weighted
      ha hb hd hxH hyH (by norm_num : (0 : ℝ) ≤ 1) hsum
    simpa using h
  have hL : xL ^ a * yL ^ b ≤ a * xL + b * yL + d := by
    have h := Real.geom_mean_le_arith_mean3_weighted
      ha hb hd hxL hyL (by norm_num : (0 : ℝ) ≤ 1) hsum
    simpa using h
  calc
    wH * (xH ^ a * yH ^ b) + wL * (xL ^ a * yL ^ b) ≤
        wH * (a * xH + b * yH + d) +
          wL * (a * xL + b * yL + d) :=
      add_le_add
        (mul_le_mul_of_nonneg_left hH hwH)
        (mul_le_mul_of_nonneg_left hL hwL)
    _ = a * (wH * xH + wL * xL) +
        b * (wH * yH + wL * yL) + d * (wH + wL) := by ring
    _ = (a + b + d) * (wH + wL) := by
      rw [hcapital, hlabor]
      ring
    _ = wH + wL := by rw [hsum]; ring

/-- The efficient normalized allocation xH=xL=yH=yL=1 attains the
global frontier established by normalized_two_type_output_le_benchmark. -/
theorem normalized_benchmark_attained
    (a b wH wL : ℝ) :
    wH * ((1 : ℝ) ^ a * (1 : ℝ) ^ b) +
      wL * ((1 : ℝ) ^ a * (1 : ℝ) ^ b) = wH + wL := by
  simp

/-- Positive individual positions permit taking the logarithm of the
global production inequality, yielding nonnegative conditional output loss.
This is a theorem about the NORMALIZED production problem, not yet the
original source function \mathscr L(k). -/
theorem normalized_log_loss_nonneg
    (a b d wH wL xH xL yH yL : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hd : 0 ≤ d)
    (hsum : a + b + d = 1)
    (hwH : 0 < wH) (hwL : 0 < wL)
    (hxH : 0 < xH) (hxL : 0 < xL)
    (hyH : 0 < yH) (hyL : 0 < yL)
    (hcapital : wH * xH + wL * xL = wH + wL)
    (hlabor : wH * yH + wL * yL = wH + wL) :
    0 ≤ Real.log (wH + wL) -
      Real.log (wH * (xH ^ a * yH ^ b) +
        wL * (xL ^ a * yL ^ b)) := by
  have hposH : 0 < xH ^ a * yH ^ b :=
    mul_pos (Real.rpow_pos_of_pos hxH a)
      (Real.rpow_pos_of_pos hyH b)
  have hposL : 0 < xL ^ a * yL ^ b :=
    mul_pos (Real.rpow_pos_of_pos hxL a)
      (Real.rpow_pos_of_pos hyL b)
  have hY :
      0 < wH * (xH ^ a * yH ^ b) +
        wL * (xL ^ a * yL ^ b) := by positivity
  have hbound := normalized_two_type_output_le_benchmark
    a b d wH wL xH xL yH yL ha hb hd hsum
    hwH.le hwL.le hxH.le hxL.le hyH.le hyL.le
    hcapital hlabor
  exact sub_nonneg.mpr (Real.log_le_log hY hbound)

/-- The proposed efficient capital and labor allocations share each
aggregate according to positive productivity weights zH,zL and masses
vH,vL. This is exact budget clearing; it does not impose profitability. -/
theorem efficient_candidate_clears_resources
    (vH vL zH zL K L : ℝ)
    (hZ : vH * zH + vL * zL ≠ 0) :
    vH * (K * zH / (vH * zH + vL * zL)) +
        vL * (K * zL / (vH * zH + vL * zL)) = K ∧
      vH * (L * zH / (vH * zH + vL * zL)) +
        vL * (L * zL / (vH * zH + vL * zL)) = L := by
  constructor
  · field_simp [hZ]
    ring
  · field_simp [hZ]
    ring

#print axioms normalized_two_type_output_le_benchmark
#print axioms normalized_benchmark_attained
#print axioms normalized_log_loss_nonneg
#print axioms efficient_candidate_clears_resources

end ProposedPaperAllocationEfficiencySupport
end Ventura26LiquidityAllocation
