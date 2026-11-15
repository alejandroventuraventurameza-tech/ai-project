import Ventura26LiquidityAllocation.SourceTwoDateMonetaryBankShearInverseCandidate

/-!
# Two-date banking row shear: kernel and injectivity transport

A purely algebraic prerequisite for transporting regularity between
candidate 33-dimensional Jacobians. A shear E does not change the
kernel of ANY map L into 33-dimensional real row space:
E (L z) = 0 iff L z = 0. It also preserves injectivity.

CAUTION: The result does NOT claim that the original SOURCE and
Python Jacobians actually satisfy J_python = E . J_source.
Their source-code correspondence, OTC rate slopes, admissible
domains and specific row normalizations still require audit.
-/

namespace Ventura26LiquidityAllocation

/-- Exact preservation of the null set of an arbitrary 33-output
map after applying the verified two-date monetary row shear. -/
theorem sourceTwoDateBankShear_kernel_iff
    (a0 b0 a1 b1 : ℝ)
    (L : (Fin 33 → ℝ) → (Fin 33 → ℝ))
    (z : Fin 33 → ℝ) :
    sourceTwoDateMonetaryBankRowShear a0 b0 a1 b1 (L z) = 0 ↔
      L z = 0 := by
  exact sourceTwoDateMonetaryBankRowShear_zero_iff a0 b0 a1 b1 (L z)

#print axioms sourceTwoDateBankShear_kernel_iff

/-- Injectivity (and thus, for an actual linear endomorphism,
full-column-rank regularity) is invariant under the two-date shear.
Linearity of L is NOT assumed and is NOT established here. -/
theorem sourceTwoDateBankShear_injective_iff
    (a0 b0 a1 b1 : ℝ)
    (L : (Fin 33 → ℝ) → (Fin 33 → ℝ)) :
    Function.Injective
      (fun z => sourceTwoDateMonetaryBankRowShear a0 b0 a1 b1 (L z)) ↔
      Function.Injective L := by
  constructor
  · intro h x y hxy
    apply h
    rw [hxy]
  · intro h x y hxy
    apply h
    exact sourceTwoDateMonetaryBankRowShear_injective
      a0 b0 a1 b1 hxy

#print axioms sourceTwoDateBankShear_injective_iff

end Ventura26LiquidityAllocation
