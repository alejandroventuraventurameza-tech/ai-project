import Ventura26LiquidityAllocation.Proposition42KKTIdentificationCandidate

/-!
# Conditional construction of the normalized scalar collateral multiplier

If a variational inequality establishes a nonnegative capital Euler primal
gap and the collateral coefficient is positive, there is a nonnegative
scalar multiplier solving the algebraic capital row. This does not claim
that the original Allocation.collateralDual is already identified or
that the variational inequality has been discharged.
-/

namespace Ventura26LiquidityAllocation
namespace ProposedScalarKKTMultiplierConstruction

open ProposedProposition42KKTIdentification

variable {S : Type*} [Fintype S] [DecidableEq S]

noncomputable def normalizedCapitalCollateralDual
    (P : Primitives S) (X : Allocation S) (i : FirmType)
    (t : ℕ) (h : History S t) (s : S) : ℝ :=
  capitalEulerPrimalGap P X i t h s /
    capitalEulerCollateralUnit P X i t h s

theorem normalizedCapitalCollateralDual_nonneg
    (P : Primitives S) (X : Allocation S) (i : FirmType)
    (t : ℕ) (h : History S t) (s : S)
    (hgap : 0 ≤ capitalEulerPrimalGap P X i t h s)
    (hunit : 0 < capitalEulerCollateralUnit P X i t h s) :
    0 ≤ normalizedCapitalCollateralDual P X i t h s := by
  unfold normalizedCapitalCollateralDual
  exact div_nonneg hgap (le_of_lt hunit)

theorem normalizedCapitalCollateralDual_capitalRow
    (P : Primitives S) (X : Allocation S) (i : FirmType)
    (t : ℕ) (h : History S t) (s : S)
    (hunit : capitalEulerCollateralUnit P X i t h s ≠ 0) :
    capitalEulerPrimalGap P X i t h s -
      normalizedCapitalCollateralDual P X i t h s *
        capitalEulerCollateralUnit P X i t h s = 0 := by
  unfold normalizedCapitalCollateralDual
  field_simp [hunit]

theorem exists_nonnegative_scalar_capitalDual
    (P : Primitives S) (X : Allocation S) (i : FirmType)
    (t : ℕ) (h : History S t) (s : S)
    (hgap : 0 ≤ capitalEulerPrimalGap P X i t h s)
    (hunit : 0 < capitalEulerCollateralUnit P X i t h s) :
    ∃ mu : ℝ, 0 ≤ mu ∧
      capitalEulerPrimalGap P X i t h s -
        mu * capitalEulerCollateralUnit P X i t h s = 0 := by
  refine ⟨normalizedCapitalCollateralDual P X i t h s, ?_, ?_⟩
  · exact normalizedCapitalCollateralDual_nonneg P X i t h s hgap hunit
  · exact normalizedCapitalCollateralDual_capitalRow P X i t h s
      (ne_of_gt hunit)

end ProposedScalarKKTMultiplierConstruction
end Ventura26LiquidityAllocation
