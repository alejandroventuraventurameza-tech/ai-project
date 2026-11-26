import Mathlib

/-!
# Signed integer interval propagation for exact matrix powers

An all-n induction underlying the 49-frame outward interval certificate
of the pinned decimal F0. It is VALID FOR ARBITRARY integer 6x6 matrices
and scales: it does not use approximate floating-point computations.

Given A_int = 10^P * F0, interval endpoints L_n,U_n in integer units
10^(-D), and exact directed inequalities for each step, it proves:
  L_n * (10^P)^n ≤ 10^D * A_int^n ≤ U_n * (10^P)^n
entrywise for n≤48. All comparisons are in the ordered ring ℤ.

This theorem is a proof of certificate *soundness*, not a claim that
the 49 numerical table checks have passed kernel verification.
-/

open scoped Matrix

namespace Ventura26LiquidityAllocation
namespace CurrentCompact

private theorem interval_mul_term_int
    (a l u x s : ℤ)
    (hl : l * s ≤ x) (hu : x ≤ u * s) :
    (a * (if 0 ≤ a then l else u)) * s ≤ a * x ∧
      a * x ≤ (a * (if 0 ≤ a then u else l)) * s := by
  by_cases ha : 0 ≤ a
  · simp only [if_pos ha]
    constructor
    · calc
        (a * l) * s = a * (l * s) := by ring
        _ ≤ a * x := mul_le_mul_of_nonneg_left hl ha
    · calc
        a * x ≤ a * (u * s) := mul_le_mul_of_nonneg_left hu ha
        _ = (a * u) * s := by ring
  · have haNeg : a ≤ 0 := le_of_lt (lt_of_not_ge ha)
    simp only [if_neg ha]
    constructor
    · calc
        (a * u) * s = a * (u * s) := by ring
        _ ≤ a * x := mul_le_mul_of_nonpos_left hu haNeg
    · calc
        a * x ≤ a * (l * s) := mul_le_mul_of_nonpos_left hl haNeg
        _ = (a * l) * s := by ring

/-- Directed integer step certificates entail exact enclosure of all
integer matrix powers, even when the matrix has mixed-sign entries. -/
theorem interval_matrix_powers_sound
    (B : Matrix (Fin 6) (Fin 6) ℤ)
    (sourceScale intervalScale : ℤ)
    (hScale : 0 < sourceScale)
    (lo hi : ℕ → Matrix (Fin 6) (Fin 6) ℤ)
    (hBase : ∀ i j : Fin 6,
       lo 0 i j = (if i = j then intervalScale else 0) ∧
       hi 0 i j = (if i = j then intervalScale else 0))
    (hSteps : ∀ n : ℕ, n < 48 → ∀ i j : Fin 6,
       sourceScale * lo (n + 1) i j ≤
         ∑ k : Fin 6,
           B i k * (if 0 ≤ B i k then lo n k j else hi n k j) ∧
       (∑ k : Fin 6,
           B i k * (if 0 ≤ B i k then hi n k j else lo n k j)) ≤
           sourceScale * hi (n + 1) i j)
    (n : ℕ) (hn : n ≤ 48) :
    ∀ i j : Fin 6,
      lo n i j * sourceScale ^ n ≤
        intervalScale * (B ^ n) i j ∧
      intervalScale * (B ^ n) i j ≤
        hi n i j * sourceScale ^ n := by
  induction n with
  | zero =>
      intro i j
      obtain ⟨hlo, hhi⟩ := hBase i j
      simp only [pow_zero, one_mul, mul_one]
      rw [hlo, hhi]
      by_cases hEq : i = j
      · subst j
        simp [Matrix.one_apply]
      · simp [Matrix.one_apply, hEq]
  | succ n ih =>
      intro i j
      have hN : n ≤ 48 := by omega
      have hStrict : n < 48 := by omega
      have hPrev := ih hN
      have hCert := hSteps n hStrict i j
      have hPositive : 0 ≤ sourceScale ^ n := pow_nonneg hScale.le n
      have hPowerSum :
          intervalScale * (B ^ (n + 1)) i j =
            ∑ k : Fin 6, B i k * (intervalScale * (B ^ n) k j) := by
        rw [pow_succ']
        simp only [Matrix.mul_apply, dotProduct, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k hk
        ring
      have hLowSum :
          (∑ k : Fin 6,
            B i k * (if 0 ≤ B i k then lo n k j else hi n k j)) *
            sourceScale ^ n ≤
              intervalScale * (B ^ (n + 1)) i j := by
        calc
          _ = ∑ k : Fin 6,
              (B i k * (if 0 ≤ B i k then lo n k j else hi n k j)) *
                sourceScale ^ n := by rw [Finset.sum_mul]
          _ ≤ ∑ k : Fin 6,
              B i k * (intervalScale * (B ^ n) k j) := by
                apply Finset.sum_le_sum
                intro k hk
                exact (interval_mul_term_int
                  (B i k) (lo n k j) (hi n k j)
                  (intervalScale * (B ^ n) k j) (sourceScale ^ n)
                  (hPrev k j).1 (hPrev k j).2).1
          _ = intervalScale * (B ^ (n + 1)) i j := hPowerSum.symm
      have hHighSum :
          intervalScale * (B ^ (n + 1)) i j ≤
            (∑ k : Fin 6,
              B i k * (if 0 ≤ B i k then hi n k j else lo n k j)) *
              sourceScale ^ n := by
        calc
          _ = ∑ k : Fin 6,
              B i k * (intervalScale * (B ^ n) k j) := hPowerSum
          _ ≤ ∑ k : Fin 6,
              (B i k * (if 0 ≤ B i k then hi n k j else lo n k j)) *
                sourceScale ^ n := by
                apply Finset.sum_le_sum
                intro k hk
                exact (interval_mul_term_int
                  (B i k) (lo n k j) (hi n k j)
                  (intervalScale * (B ^ n) k j) (sourceScale ^ n)
                  (hPrev k j).1 (hPrev k j).2).2
          _ = (∑ k : Fin 6,
              B i k * (if 0 ≤ B i k then hi n k j else lo n k j)) *
                sourceScale ^ n := by rw [Finset.sum_mul]
      constructor
      · calc
          lo (n + 1) i j * sourceScale ^ (n + 1) =
              (sourceScale * lo (n + 1) i j) * sourceScale ^ n := by
                rw [pow_succ]
                ring
          _ ≤ (∑ k : Fin 6,
              B i k * (if 0 ≤ B i k then lo n k j else hi n k j)) *
                sourceScale ^ n :=
                  mul_le_mul_of_nonneg_right hCert.1 hPositive
          _ ≤ intervalScale * (B ^ (n + 1)) i j := hLowSum
      · calc
          intervalScale * (B ^ (n + 1)) i j ≤
            (∑ k : Fin 6,
              B i k * (if 0 ≤ B i k then hi n k j else lo n k j)) *
                sourceScale ^ n := hHighSum
          _ ≤ (sourceScale * hi (n + 1) i j) * sourceScale ^ n :=
                mul_le_mul_of_nonneg_right hCert.2 hPositive
          _ = hi (n + 1) i j * sourceScale ^ (n + 1) := by
                rw [pow_succ]
                ring

#print axioms interval_matrix_powers_sound

end CurrentCompact
end Ventura26LiquidityAllocation
