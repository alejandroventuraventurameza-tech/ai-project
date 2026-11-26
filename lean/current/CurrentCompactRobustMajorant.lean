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


/-- Geometric decay from the robust constants of the compact paper.
The matrix is arbitrary, but the two finite norm bounds are hypotheses. -/
theorem matrix_robust_block48_decay_of_norm_bounds
    (A : Matrix (Fin 6) (Fin 6) ℝ)
    (hBlock : ‖A ^ 48‖ < (49 / 50 : ℝ))
    (hTransient : ∀ r : ℕ, r < 48 → ‖A ^ r‖ < (7 : ℝ))
    (k : ℕ) (x : Fin 6 → ℝ) :
    ‖(A ^ k) *ᵥ x‖ ≤
      (7 : ℝ) * (49 / 50 : ℝ) ^ (k / 48) * ‖x‖ := by
  let m : ℕ := k / 48
  let r : ℕ := k % 48
  have hr : r < 48 := by
    dsimp [r]
    exact Nat.mod_lt _ (by omega)
  have hk : k = 48 * m + r := by
    dsimp [m, r]
    omega
  have hPowerIdentity : A ^ k = (A ^ 48) ^ m * A ^ r := by
    calc
      A ^ k = A ^ (48 * m + r) := by rw [← hk]
      _ = (A ^ 48) ^ m * A ^ r := by rw [pow_add, pow_mul]
  have hMainPower : ‖(A ^ 48) ^ m‖ ≤ (49 / 50 : ℝ) ^ m := by
    calc
      ‖(A ^ 48) ^ m‖ ≤ ‖A ^ 48‖ ^ m := norm_pow_le _ _
      _ ≤ (49 / 50 : ℝ) ^ m := by
        exact pow_le_pow_left₀ (norm_nonneg _) hBlock.le _
  have hTransientBound : ‖A ^ r‖ ≤ (7 : ℝ) :=
    (hTransient r hr).le
  have hMatrix :
      ‖A ^ k‖ ≤ (7 : ℝ) * (49 / 50 : ℝ) ^ (k / 48) := by
    calc
      ‖A ^ k‖ = ‖(A ^ 48) ^ m * A ^ r‖ := by rw [hPowerIdentity]
      _ ≤ ‖(A ^ 48) ^ m‖ * ‖A ^ r‖ := norm_mul_le _ _
      _ ≤ (49 / 50 : ℝ) ^ m * (7 : ℝ) := by
        exact mul_le_mul hMainPower hTransientBound (norm_nonneg _)
          (pow_nonneg (by norm_num) _)
      _ = (7 : ℝ) * (49 / 50 : ℝ) ^ (k / 48) := by
        dsimp [m]
        ring
  calc
    ‖(A ^ k) *ᵥ x‖ ≤ ‖A ^ k‖ * ‖x‖ :=
      Matrix.linfty_opNorm_mulVec _ _
    _ ≤ ((7 : ℝ) * (49 / 50 : ℝ) ^ (k / 48)) * ‖x‖ :=
      mul_le_mul_of_nonneg_right hMatrix (norm_nonneg x)
    _ = (7 : ℝ) * (49 / 50 : ℝ) ^ (k / 48) * ‖x‖ := rfl

/-- Uniform statement for every real 6x6 A within 10^-4 of F,
conditional ONLY on existence of a sequence satisfying the source
majorant recursion and its finite inequalities.

The existence and finite numerical bounds of that source-specific
sequence are not proved in this declaration. -/
theorem lemma52_conditional_uniform_decay
    (F A : Matrix (Fin 6) (Fin 6) ℝ)
    (a : ℕ → ℝ)
    (hGap : ‖A - F‖ ≤ (1 / 10000 : ℝ))
    (hZero : (1 : ℝ) ≤ a 0)
    (hStep : ∀ n : ℕ, 0 < n →
      ‖F ^ n‖ +
        ∑ j ∈ Finset.range n,
          (‖F ^ j‖ * (1 / 10000 : ℝ)) * a (n - 1 - j) ≤ a n)
    (h48 : a 48 < (49 / 50 : ℝ))
    (hTransient : ∀ r : ℕ, r < 48 → a r < (7 : ℝ))
    (k : ℕ) (x : Fin 6 → ℝ) :
    ‖(A ^ k) *ᵥ x‖ ≤
      (7 : ℝ) * (49 / 50 : ℝ) ^ (k / 48) * ‖x‖ := by
  have hDelta : (0 : ℝ) ≤ 1 / 10000 := by norm_num
  have hBound48 : ‖A ^ 48‖ < (49 / 50 : ℝ) :=
    lt_of_le_of_lt
      (matrix_robust_majorant_induction A F (1 / 10000) a
        hDelta hGap hZero hStep 48) h48
  have hBoundTransient : ∀ r : ℕ, r < 48 → ‖A ^ r‖ < (7 : ℝ) := by
    intro r hr
    exact lt_of_le_of_lt
      (matrix_robust_majorant_induction A F (1 / 10000) a
        hDelta hGap hZero hStep r)
      (hTransient r hr)
  exact matrix_robust_block48_decay_of_norm_bounds
    A hBound48 hBoundTransient k x

#print axioms matrix_robust_block48_decay_of_norm_bounds
#print axioms lemma52_conditional_uniform_decay

#print axioms matrix_robust_majorant_induction

end CurrentCompact
end Ventura26LiquidityAllocation
