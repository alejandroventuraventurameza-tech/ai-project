import Ventura26LiquidityAllocation.PaperOptimalLaborCandidate

/-!
# Lemma 4.3: arbitrary physical labor allocations to normalized optimality

This module removes the last assumed normalized labor-budget constraint.
Any nonnegative original labor allocation with the physical aggregate
labor identity is reparameterized by x_i = ell_i G / (L g_i).
The global output inequality is derived from the original two-firm
Cobb-Douglas productions, not from an assumed definition of Y.

This proves GLOBAL labor optimality for FIXED capital. It does not
yet connect the joint capital/labor efficiency frontier, derivatives
of loss, or the infinite-horizon competitive equilibrium.
-/

namespace Ventura26LiquidityAllocation
namespace ProposedPaperOriginalLaborGlobal

/-- Given any nonnegative labor allocation satisfying the original
resource budget, original micro output is bounded by the output
of labor optimally allocated across firms with fixed capital.

All A_i, k_i, v_i and L are strictly positive. The two types share
labor elasticity 0 < beta < 1 and capital elasticity alpha.
The candidate reaches the bound by the separately proved theorem
source_labor_global_bound_attained. -/
theorem original_two_type_labor_global_bound
    (vH vL AH AL kH kL ellH ellL L a b : ℝ)
    (hvH : 0 < vH) (hvL : 0 < vL)
    (hAH : 0 < AH) (hAL : 0 < AL)
    (hkH : 0 < kH) (hkL : 0 < kL)
    (hL : 0 < L)
    (hellH : 0 ≤ ellH) (hellL : 0 ≤ ellL)
    (hb0 : 0 < b) (hb1 : b < 1)
    (hbudget : vH * ellH + vL * ellL = L) :
    vH * (AH * kH ^ a * ellH ^ b) +
      vL * (AL * kL ^ a * ellL ^ b) ≤
      L ^ b *
        (vH * (AH ^ (1 / (1 - b)) * kH ^ (a / (1 - b))) +
          vL * (AL ^ (1 / (1 - b)) * kL ^ (a / (1 - b)))) ^ (1 - b) := by
  let gH : ℝ := AH ^ (1 / (1 - b)) * kH ^ (a / (1 - b))
  let gL : ℝ := AL ^ (1 / (1 - b)) * kL ^ (a / (1 - b))
  let G : ℝ := vH * gH + vL * gL
  let xH : ℝ := ellH * G / (L * gH)
  let xL : ℝ := ellL * G / (L * gL)

  have hgH : 0 < gH := by
    dsimp [gH]
    exact mul_pos (Real.rpow_pos_of_pos hAH _) (Real.rpow_pos_of_pos hkH _)
  have hgL : 0 < gL := by
    dsimp [gL]
    exact mul_pos (Real.rpow_pos_of_pos hAL _) (Real.rpow_pos_of_pos hkL _)
  have hG : 0 < G := by
    dsimp [G]
    exact add_pos (mul_pos hvH hgH) (mul_pos hvL hgL)
  have hxH : 0 ≤ xH := by
    dsimp [xH]
    exact div_nonneg (mul_nonneg hellH hG.le) (mul_nonneg hL.le hgH.le)
  have hxL : 0 ≤ xL := by
    dsimp [xL]
    exact div_nonneg (mul_nonneg hellL hG.le) (mul_nonneg hL.le hgL.le)

  have hscaledH : L * gH / G * xH = ellH := by
    dsimp [xH]
    field_simp [ne_of_gt hL, ne_of_gt hgH, ne_of_gt hG] <;> ring
  have hscaledL : L * gL / G * xL = ellL := by
    dsimp [xL]
    field_simp [ne_of_gt hL, ne_of_gt hgL, ne_of_gt hG] <;> ring

  have hweightH : vH * gH * xH = (G / L) * (vH * ellH) := by
    dsimp [xH]
    field_simp [ne_of_gt hL, ne_of_gt hgH] <;> ring
  have hweightL : vL * gL * xL = (G / L) * (vL * ellL) := by
    dsimp [xL]
    field_simp [ne_of_gt hL, ne_of_gt hgL] <;> ring
  have hnormalizedBudget :
      vH * gH * xH + vL * gL * xL = vH * gH + vL * gL := by
    calc
      vH * gH * xH + vL * gL * xL =
          (G / L) * (vH * ellH + vL * ellL) := by
        rw [hweightH, hweightL]
        ring
      _ = (G / L) * L := by rw [hbudget]
      _ = vH * gH + vL * gL := by
        dsimp [G]
        field_simp [ne_of_gt hL] <;> ring

  have hbound :
      vH * (AH * kH ^ a * (L * gH / G * xH) ^ b) +
        vL * (AL * kL ^ a * (L * gL / G * xL) ^ b) ≤
        L ^ b * G ^ (1 - b) := by
    exact ProposedPaperOptimalLabor.source_two_type_global_labor_optimality
      vH vL AH AL kH kL L a b xH xL
      hvH hvL hAH hAL hkH hkL hL hb0 hb1 hxH hxL
      (by simpa only [gH, gL] using hnormalizedBudget)
  calc
    vH * (AH * kH ^ a * ellH ^ b) +
        vL * (AL * kL ^ a * ellL ^ b) =
      vH * (AH * kH ^ a * (L * gH / G * xH) ^ b) +
        vL * (AL * kL ^ a * (L * gL / G * xL) ^ b) := by
          rw [hscaledH, hscaledL]
    _ ≤ L ^ b * G ^ (1 - b) := hbound

/-- Original optimal labor allocation attains the upper bound; when
labor is scaled proportional to source g_i, output equals the
physical production frontier conditional on fixed capital. -/
theorem original_labor_candidate_attains_global_bound
    (vH vL AH AL kH kL L a b : ℝ)
    (hvH : 0 < vH) (hvL : 0 < vL)
    (hAH : 0 < AH) (hAL : 0 < AL)
    (hkH : 0 < kH) (hkL : 0 < kL)
    (hL : 0 < L) (hb : b < 1) :
    let gH := AH ^ (1 / (1 - b)) * kH ^ (a / (1 - b))
    let gL := AL ^ (1 / (1 - b)) * kL ^ (a / (1 - b))
    let G := vH * gH + vL * gL
    vH * (AH * kH ^ a * (L * gH / G) ^ b) +
      vL * (AL * kL ^ a * (L * gL / G) ^ b) =
      L ^ b * G ^ (1 - b) :=
  ProposedPaperAllocationSourceAlgebraBridge.source_two_type_output_at_optimal_labor
    vH vL AH AL kH kL L a b hvH hvL hAH hAL hkH hkL hL hb

#print axioms original_two_type_labor_global_bound
#print axioms original_labor_candidate_attains_global_bound

end ProposedPaperOriginalLaborGlobal
end Ventura26LiquidityAllocation
