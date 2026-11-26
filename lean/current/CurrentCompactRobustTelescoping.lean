import Mathlib

/-!
# Appendix Lemma 5.2: exact noncommutative matrix-power telescoping

Source: ai-project@bac3c6255da39cd1169a965df35bb5e9a230e6e8,
paper/body_compact_after.tex, label lem:compact_robust_tail_power.

The following two lemmas prove the genuine universal matrix identities
for arbitrary real 6x6 matrices A and F, using the induced row-sum
operator norm. No numerical 48-step certificate is assumed here.

These lemmas are ONLY the analytic telescoping component of Lemma 5.2.
They do not by themselves establish the stringent rational upper bounds
a_48<49/50 and max_{r<48}a_r<7, nor identify F with the SOURCE DSGE
Jacobian. The externally verified rational recursion must be linked
separately to Lean for a full source-specific proof.
-/

open scoped Matrix Matrix.Norms.Operator

namespace Ventura26LiquidityAllocation
namespace CurrentCompact

/-- Exact telescoping identity for arbitrary noncommuting matrices.
Index j counts powers of F on the left; reversing the finite sum gives
the equivalent index order in the article's proof. -/
theorem matrix_pow_difference_telescoping
    (A F : Matrix (Fin 6) (Fin 6) ℝ) (n : ℕ) :
    A ^ n - F ^ n =
      ∑ j ∈ Finset.range n, F ^ j * (A - F) * A ^ (n - 1 - j) := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      have hRec :
          A ^ (n + 1) - F ^ (n + 1) =
            (A - F) * A ^ n + F * (A ^ n - F ^ n) := by
        rw [pow_succ' A n, pow_succ' F n]
        noncomm_ring
      have hSumShift :
          F * (∑ j ∈ Finset.range n,
                  F ^ j * (A - F) * A ^ (n - 1 - j)) =
            ∑ j ∈ Finset.range n,
              F ^ (j + 1) * (A - F) * A ^ (n - 1 - j) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        rw [pow_succ']
        noncomm_ring
      calc
        A ^ (n + 1) - F ^ (n + 1) =
            (A - F) * A ^ n + F * (A ^ n - F ^ n) := hRec
        _ = (A - F) * A ^ n +
              ∑ j ∈ Finset.range n,
                F ^ (j + 1) * (A - F) * A ^ (n - 1 - j) := by
              rw [ih, hSumShift]
        _ = ∑ j ∈ Finset.range (n + 1),
              F ^ j * (A - F) * A ^ (n + 1 - 1 - j) := by
              rw [Finset.sum_range_succ']
              simp only [pow_zero, one_mul, Nat.add_sub_cancel_right, Nat.sub_zero]
              congr 1
              apply Finset.sum_congr rfl
              intro j hj
              have heq : n + 1 - 1 - (j + 1) = n - 1 - j := by omega
              rw [heq]

/-- General norm inequality underlying robust finite-horizon bounds.
Every term is a true matrix operator norm, not a scalar proxy. -/
theorem matrix_power_norm_telescoping
    (A F : Matrix (Fin 6) (Fin 6) ℝ) (n : ℕ) :
    ‖A ^ n‖ ≤ ‖F ^ n‖ +
      ∑ j ∈ Finset.range n,
        (‖F ^ j‖ * ‖A - F‖) * ‖A ^ (n - 1 - j)‖ := by
  calc
    ‖A ^ n‖ = ‖F ^ n + (A ^ n - F ^ n)‖ := by
      congr 1
      abel
    _ ≤ ‖F ^ n‖ + ‖A ^ n - F ^ n‖ := norm_add_le _ _
    _ = ‖F ^ n‖ +
          ‖∑ j ∈ Finset.range n,
            F ^ j * (A - F) * A ^ (n - 1 - j)‖ := by
          rw [matrix_pow_difference_telescoping]
    _ ≤ ‖F ^ n‖ +
          ∑ j ∈ Finset.range n,
            ‖F ^ j * (A - F) * A ^ (n - 1 - j)‖ := by
          exact add_le_add_left (norm_sum_le _ _) _
    _ ≤ ‖F ^ n‖ +
          ∑ j ∈ Finset.range n,
            (‖F ^ j‖ * ‖A - F‖) * ‖A ^ (n - 1 - j)‖ := by
          apply add_le_add_left
          apply Finset.sum_le_sum
          intro j hj
          calc
            ‖F ^ j * (A - F) * A ^ (n - 1 - j)‖ ≤
                ‖F ^ j * (A - F)‖ * ‖A ^ (n - 1 - j)‖ :=
                  norm_mul_le _ _
            _ ≤ (‖F ^ j‖ * ‖A - F‖) * ‖A ^ (n - 1 - j)‖ :=
                  mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)

#print axioms matrix_pow_difference_telescoping
#print axioms matrix_power_norm_telescoping

end CurrentCompact
end Ventura26LiquidityAllocation
