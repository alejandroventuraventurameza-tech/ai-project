import Ventura26LiquidityAllocation.CurrentCompactRobustMajorant

/-!
# Lemma 5.2: finite-horizon majorant induction and universal 48-block decay

A 49-entry certificate is sufficient for the Lemma 5.2 conclusion:
the robust recurrence needs to be checked only for n=1,...,48,
not for all natural numbers. This removes an unnecessary hypothetical
infinite extension of the finite numeric table.

Both results below are general mathematical theorems about arbitrary
noncommuting real 6x6 matrices and ANY real majorant function. The
source-specific F0 and the rational table are instantiated elsewhere.
-/

open scoped Matrix Matrix.Norms.Operator

namespace Ventura26LiquidityAllocation
namespace CurrentCompact

/-- Finite 48-step domination: a table whose entries satisfy the
majorant recursion only through n=48 bounds A^n through n=48. -/
theorem matrix_robust_majorant_finite_48
    (A F : Matrix (Fin 6) (Fin 6) ℝ)
    (δ : ℝ) (a : ℕ → ℝ)
    (hδ : 0 ≤ δ)
    (hGap : ‖A - F‖ ≤ δ)
    (hZero : 1 ≤ a 0)
    (hStep : ∀ n : ℕ, 0 < n → n ≤ 48 →
      ‖F ^ n‖ +
        ∑ j ∈ Finset.range n,
          (‖F ^ j‖ * δ) * a (n - 1 - j) ≤ a n) :
    ∀ n : ℕ, n ≤ 48 → ‖A ^ n‖ ≤ a n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro hn
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
              ih (n - j) (by omega) (by omega)
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
            _ ≤ a (n + 1) := hStep (n + 1) (by omega) hn

/-- Uniform geometric decay for every A in the stated norm ball.
The finite majorant table conditions are explicit hypotheses here. -/
theorem lemma52_uniform_of_finite_majorant
    (F A : Matrix (Fin 6) (Fin 6) ℝ)
    (a : ℕ → ℝ)
    (hGap : ‖A - F‖ ≤ (1 / 10000 : ℝ))
    (hZero : (1 : ℝ) ≤ a 0)
    (hStep : ∀ n : ℕ, 0 < n → n ≤ 48 →
      ‖F ^ n‖ +
        ∑ j ∈ Finset.range n,
          (‖F ^ j‖ * (1 / 10000 : ℝ)) * a (n - 1 - j) ≤ a n)
    (h48 : a 48 < (49 / 50 : ℝ))
    (hTransient : ∀ r : ℕ, r < 48 → a r < (7 : ℝ))
    (k : ℕ) (x : Fin 6 → ℝ) :
    ‖(A ^ k) *ᵥ x‖ ≤
      (7 : ℝ) * (49 / 50 : ℝ) ^ (k / 48) * ‖x‖ := by
  have hδ : (0 : ℝ) ≤ 1 / 10000 := by norm_num
  have hMaj := matrix_robust_majorant_finite_48
    A F (1 / 10000) a hδ hGap hZero hStep
  have hBlock : ‖A ^ 48‖ < (49 / 50 : ℝ) :=
    lt_of_le_of_lt (hMaj 48 (by omega)) h48
  have hTrans : ∀ r : ℕ, r < 48 → ‖A ^ r‖ < (7 : ℝ) := by
    intro r hr
    exact lt_of_le_of_lt (hMaj r (by omega)) (hTransient r hr)
  exact matrix_robust_block48_decay_of_norm_bounds A hBlock hTrans k x

#print axioms matrix_robust_majorant_finite_48
#print axioms lemma52_uniform_of_finite_majorant

end CurrentCompact
end Ventura26LiquidityAllocation
