import Ventura26LiquidityAllocation.ScalarComplementarityMultiplicityCandidate

/-!
# Local complementarity near the boundary: no global monotonicity premise

The older scalar candidate assumes strict antitonicity on the ENTIRE
nonnegative half-line and assumes a positive root already exists.

This module proves the genuinely LOCAL result. For a fixed interval [0, eps],
continuity, strict antitonicity on that interval, and a sign crossing
M(0) > 0 > M(eps) produce an interior root via the intermediate value
theorem, and exactly the two local complementary solutions 0 and that root.

This is an order/topology theorem only. The source-model Schur complement,
IFT validity, endpoint signs, and the identification of scalar solutions
with competitive allocations remain separate obligations.
-/

namespace Ventura26LiquidityAllocation
namespace ProposedLocalScalarComplementarity

open ProposedScalarComplementarityMultiplicity

/-- An interior root exists and the only complementary solutions in the
specified local interval are the boundary and that interior root. Unlike
the earlier global lemma, neither monotonicity beyond eps nor the
existence of a root is assumed. -/
theorem local_scalar_complementarity_exactly_two_of_crossing
    (M : ℝ → ℝ) (eps : ℝ)
    (heps : 0 < eps)
    (hcont : ContinuousOn M (Set.Icc (0 : ℝ) eps))
    (hanti : StrictAntiOn M (Set.Icc (0 : ℝ) eps))
    (hM0 : 0 < M 0) (hMeps : M eps < 0) :
    ∃ r : ℝ, 0 < r ∧ r < eps ∧ M r = 0 ∧
      (∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) eps →
        (ScalarComplementarity M s ↔ s = 0 ∨ s = r)) := by
  have hImage : (0 : ℝ) ∈ M '' Set.Icc (0 : ℝ) eps :=
    (intermediate_value_Icc' (le_of_lt heps) hcont)
      ⟨le_of_lt hMeps, le_of_lt hM0⟩
  rcases hImage with ⟨r, hrI, hroot⟩
  have hrpos : 0 < r := by
    by_contra h
    have hrle : r ≤ 0 := le_of_not_gt h
    have hr0 : r = 0 := le_antisymm hrle hrI.1
    rw [hr0] at hroot
    linarith
  have hrlt : r < eps := by
    by_contra h
    have hle : eps ≤ r := le_of_not_gt h
    have hreps : r = eps := le_antisymm hrI.2 hle
    rw [hreps] at hroot
    linarith
  have hroot_unique : ∀ s : ℝ,
      s ∈ Set.Icc (0 : ℝ) eps → M s = 0 → s = r := by
    intro s hsI hsRoot
    rcases lt_trichotomy s r with hlt | heq | hgt
    · have hstrict : M r < M s := hanti hsI hrI hlt
      rw [hroot, hsRoot] at hstrict
      exact False.elim ((lt_irrefl (0 : ℝ)) hstrict)
    · exact heq
    · have hstrict : M s < M r := hanti hrI hsI hgt
      rw [hroot, hsRoot] at hstrict
      exact False.elim ((lt_irrefl (0 : ℝ)) hstrict)
  refine ⟨r, hrpos, hrlt, hroot, ?_⟩
  intro s hsI
  constructor
  · intro hs
    rcases hs with ⟨_hsnonneg, _hMnonneg, hprod⟩
    rcases mul_eq_zero.mp hprod with hs0 | hMs0
    · exact Or.inl hs0
    · exact Or.inr (hroot_unique s hsI hMs0)
  · intro hs
    rcases hs with hs0 | hsr
    · subst s
      exact ⟨le_refl (0 : ℝ), le_of_lt hM0, by simp⟩
    · subst s
      exact ⟨le_of_lt hrpos, by simp [hroot], by simp [hroot]⟩

/-- A negative marginal at the boundary eliminates complementary solutions
WITHIN the interval when the marginal is strictly decreasing there.
No exclusion outside that interval is claimed. -/
theorem no_local_scalar_complementarity_of_negative_boundary
    (M : ℝ → ℝ) (eps : ℝ)
    (hanti : StrictAntiOn M (Set.Icc (0 : ℝ) eps))
    (hM0 : M 0 < 0) :
    ¬ ∃ s : ℝ, s ∈ Set.Icc (0 : ℝ) eps ∧
      ScalarComplementarity M s := by
  rintro ⟨s, hsI, hs⟩
  rcases eq_or_lt_of_le hsI.1 with hzero | hpos
  · rw [← hzero] at hs
    exact (not_le_of_gt hM0) hs.2.1
  · have hzeromem : (0 : ℝ) ∈ Set.Icc (0 : ℝ) eps :=
      ⟨le_refl (0 : ℝ), le_trans hsI.1 hsI.2⟩
    have hstrict : M s < M 0 := hanti hzeromem hsI hpos
    have hsM : 0 ≤ M s := hs.2.1
    linarith

#print axioms local_scalar_complementarity_exactly_two_of_crossing
#print axioms no_local_scalar_complementarity_of_negative_boundary

end ProposedLocalScalarComplementarity
end Ventura26LiquidityAllocation
