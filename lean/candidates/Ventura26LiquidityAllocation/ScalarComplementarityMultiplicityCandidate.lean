import Ventura26LiquidityAllocation.EconomicModel

/-!
# Scalar complementarity: exactly two reduced roots under explicit hypotheses

This is an independent scalar-order lemma for a reduced complementarity
relation. It is NOT a proof of a DSGE equilibrium, not a proof that the actual
Schur complement is strictly decreasing or has a positive root, and not a
repair of PaperInterface.localMacroMultiplicitySpec.

The original Lean interface's literal uniqueness is refuted in
Proposition42RefutationCandidate because collateralDual is unconstrained
by CompetitiveEquilibrium. Here we deliberately have no Allocation carrier.
-/

namespace Ventura26LiquidityAllocation
namespace ProposedScalarComplementarityMultiplicity

/-- Nonnegative scalar slack and nonnegative reduced marginal value, with
complementary slackness, for a one-dimensional reduced local problem. -/
def ScalarComplementarity (M : ℝ → ℝ) (s : ℝ) : Prop :=
  0 ≤ s ∧ 0 ≤ M s ∧ s * M s = 0

/-- A positive interior root is the only possible strictly positive
complementarity slack if the reduced marginal function is strictly decreasing
on nonnegative slack. -/
theorem scalar_solution_is_boundary_or_positive_root
    (M : ℝ → ℝ) (r : ℝ)
    (hanti : StrictAntiOn M (Set.Ici (0 : ℝ)))
    (hr : 0 < r)
    (hroot : M r = 0)
    (s : ℝ)
    (hs : ScalarComplementarity M s) :
    s = 0 ∨ s = r := by
  rcases hs with ⟨hsnonneg, _hmnonneg, hprod⟩
  rcases mul_eq_zero.mp hprod with hs0 | hms
  · exact Or.inl hs0
  · right
    have hsmem : s ∈ Set.Ici (0 : ℝ) := hsnonneg
    have hrmem : r ∈ Set.Ici (0 : ℝ) := le_of_lt hr
    rcases lt_trichotomy s r with hlt | heq | hgt
    · have hstrict : M r < M s := hanti hsmem hrmem hlt
      rw [hroot, hms] at hstrict
      exact False.elim ((lt_irrefl (0 : ℝ)) hstrict)
    · exact heq
    · have hstrict : M s < M r := hanti hrmem hsmem hgt
      rw [hroot, hms] at hstrict
      exact False.elim ((lt_irrefl (0 : ℝ)) hstrict)

/-- Exactly two solutions of this *reduced scalar complementarity*
relation. The positive root is an EXPLICIT premise, not a consequence
of the numerical certificate, and this result does not prove
existence or uniqueness of economic allocations. -/
theorem scalar_complementarity_exactly_two
    (M : ℝ → ℝ) (r : ℝ)
    (hanti : StrictAntiOn M (Set.Ici (0 : ℝ)))
    (hr : 0 < r) (hM0 : 0 < M 0) (hroot : M r = 0) :
    ∀ s : ℝ, ScalarComplementarity M s ↔ s = 0 ∨ s = r := by
  intro s
  constructor
  · exact scalar_solution_is_boundary_or_positive_root M r hanti hr hroot s
  · intro h
    rcases h with h0 | h1
    · subst s
      exact ⟨le_refl (0 : ℝ), le_of_lt hM0, by simp⟩
    · subst s
      exact ⟨le_of_lt hr, by simp [hroot], by simp [hroot]⟩

/-- The opposite sign at the boundary rules out nonnegative
complementarity solutions when the same strict antitonicity holds. -/
theorem no_scalar_complementarity_of_negative_boundary
    (M : ℝ → ℝ)
    (hanti : StrictAntiOn M (Set.Ici (0 : ℝ)))
    (hM0 : M 0 < 0) :
    ¬ ∃ s : ℝ, ScalarComplementarity M s := by
  rintro ⟨s, hsnonneg, hmnonneg, _hprod⟩
  rcases eq_or_lt_of_le hsnonneg with hzero | hpos
  · rw [← hzero] at hmnonneg
    linarith
  · have hzmem : (0 : ℝ) ∈ Set.Ici (0 : ℝ) := by simp
    have hsmem : s ∈ Set.Ici (0 : ℝ) := hsnonneg
    have hlt : M s < M 0 := hanti hzmem hsmem hpos
    linarith

#print axioms scalar_complementarity_exactly_two
#print axioms no_scalar_complementarity_of_negative_boundary

end ProposedScalarComplementarityMultiplicity
end Ventura26LiquidityAllocation
