import Ventura26LiquidityAllocation.CurrentCompactRobustTelescoping

/-!
# Lemma 5.2: an arbitrary admissible majorant dominates every nearby matrix

Source paper: ai-project@bac3c6255da39cd1169a965df35bb5e9a230e6e8,
paper/body_compact_after.tex (lem:compact_robust_tail_power).

This theorem is a universal mathematical bridge:
- A and F can be ANY real 6x6 matrices, without commutativity.
- δ≥0 and ‖A-F‖∞≤δ.
- A real sequence a_n with a_0≥1 and the RECURRENCE UPPER BOUND
  a_n ≥ ‖F^n‖∞ + δ*Σ_{j<n} ‖F^j‖∞ a_(n-1-j)
  dominates ‖A^n‖∞ for EVERY n.

The finite numerical assertions a_48<49/50 and max a_0..a_47<7
are not hypotheses of this lemma; they must be established separately
for the pinned decimal F0 before the full quantitative Lemma 5.2 holds.

This statement does not assume that the SOURCE DSGE Jacobian lies
within 10^-4 of decimal F0.
-/

open scoped Matrix Matrix.Norms.Operator

namespace Ventura26LiquidityAllocation
namespace CurrentCompact

/-- Universal quantitative majorant domination for arbitrary real
6x6 A and F, with the source's noncommutative telescoping convention. -/
theorem matrix_robust_majorant_induction
    (A F : Matrix (Fin 6) (Fin 6) ℝ)
    (δ : ℝ) (a : ℕ → ℝ)
    (hδ : 0 ≤ δ) (hGap : ‖A - F‖ ≤ δ)
    (hZero : 1 ≤ a 0)
    (hStep : ∀ n : ℕ, 0 < n →
      ‖F ^ n‖ +
        ∑ j ∈ Finset.range n,
          (‖F ^ j‖ * δ) * a (n - 1 - j) ≤ a n)
    (n : ℕ) :
    ‖A ^ n‖ ≤ a n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      cases n with
      | zero =>
          simpa using hZero
      | succ n =>
          have hSum :
              (∑ j ∈ Finset.range (n + 1),
                (‖F ^ j‖ * ‖A - F‖) * ‖A ^ (n + 1 - 1 - j)‖) ≤
                ∑ j ∈ Finset.range (n + 1),
                  (‖F ^ j‖ * δ) * a (n + 1 - 1 - j) := by
            apply Finset.sum_le_sum
            intro j hj
            have hjlt : j < n + 1 := Finset.mem_range.mp hj
            have hindex : n + 1 - 1 - j = n - j := by omega
            have hPrev : ‖A ^ (n - j)‖ ≤ a (n - j) :=
              ih (n - j) (by omega)
            have hCoeff :
                ‖F ^ j‖ * ‖A - F‖ ≤ ‖F ^ j‖ * δ :=
              mul_le_mul_of_nonneg_left hGap (norm_nonneg _)
            have hPosCoeff : 0 ≤ ‖F ^ j‖ * δ :=
              mul_nonneg (norm_nonneg _) hδ
            simp only [hindex]
            calc
              (‖F ^ j‖ * ‖A - F‖) * ‖A ^ (n - j)‖ ≤
                  (‖F ^ j‖ * δ) * ‖A ^ (n - j)‖ :=
                    mul_le_mul_of_nonneg_right hCoeff (norm_nonneg _)
              _ ≤ (‖F ^ j‖ * δ) * a (n - j) :=
                    mul_le_mul_of_nonneg_left hPrev hPosCoeff
          calc
            ‖A ^ (n + 1)‖ ≤ ‖F ^ (n + 1)‖ +
                ∑ j ∈ Finset.range (n + 1),
                  (‖F ^ j‖ * ‖A - F‖) * ‖A ^ (n + 1 - 1 - j)‖ :=
                    matrix_power_norm_telescoping A F (n + 1)
            _ ≤ ‖F ^ (n + 1)‖ +
                ∑ j ∈ Finset.range (n + 1),
                  (‖F ^ j‖ * δ) * a (n + 1 - 1 - j) := by
                    simpa only [add_comm] using
                      (add_le_add_left hSum (‖F ^ (n + 1)‖))
            _ ≤ a (n + 1) := hStep (n + 1) (by omega)

#print axioms matrix_robust_majorant_induction

end CurrentCompact
end Ventura26LiquidityAllocation
