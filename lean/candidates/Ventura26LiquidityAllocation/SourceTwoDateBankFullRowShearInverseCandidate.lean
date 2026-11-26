import Ventura26LiquidityAllocation.SourceTwoDateBankFiveRowShearCandidate

/-!
# Full banking row-shear inverse and injectivity transfer

This theorem combines the explicitly checked inverse of the two-date
SOURCE balance shear (monetary policy rows 12,13,28,29 and balance
rows 16,32) with the four-price-row inverse (14,15,30,31).
The resulting full output transformation is injective for ANY real
coefficients, including coefficients determined at a common root.

This does NOT establish the actual economic SOURCE/Python Jacobian
identity or assert any Jacobian has trivial kernel.
-/

namespace Ventura26LiquidityAllocation

/-- Explicit undo: remove balance-row shear, then pricing-row shear. -/
def sourceTwoDateBankFullRowShearUndo
    (loan0 deposit0 loan1 deposit1
      rate0 quantity0 rate1 quantity1 : ℝ)
    (v : Fin 33 → ℝ) : Fin 33 → ℝ :=
  sourceTwoDateBankPricingRowShear
    (-loan0) (-deposit0) (-loan1) (-deposit1)
    (sourceTwoDateMonetaryBankRowShearUndo
      rate0 quantity0 rate1 quantity1 v)

/-- The full 33-output operator has an explicit left inverse. -/
theorem sourceTwoDateBankFullRowShear_undo
    (loan0 deposit0 loan1 deposit1
      rate0 quantity0 rate1 quantity1 : ℝ)
    (v : Fin 33 → ℝ) :
    sourceTwoDateBankFullRowShearUndo
      loan0 deposit0 loan1 deposit1
      rate0 quantity0 rate1 quantity1
      (sourceTwoDateBankFiveRowShear
        loan0 deposit0 loan1 deposit1
        rate0 quantity0 rate1 quantity1 v) = v := by
  unfold sourceTwoDateBankFullRowShearUndo
    sourceTwoDateBankFiveRowShear
  rw [sourceTwoDateMonetaryBankRowShear_undo,
    sourceTwoDateBankPricingRowShear_inverse]

#print axioms sourceTwoDateBankFullRowShear_undo

/-- The full banking shear is injective on residual vectors. -/
theorem sourceTwoDateBankFullRowShear_injective
    (loan0 deposit0 loan1 deposit1
      rate0 quantity0 rate1 quantity1 : ℝ) :
    Function.Injective
      (sourceTwoDateBankFiveRowShear
        loan0 deposit0 loan1 deposit1
        rate0 quantity0 rate1 quantity1) := by
  intro v w h
  have hi := congrArg
    (sourceTwoDateBankFullRowShearUndo
      loan0 deposit0 loan1 deposit1
      rate0 quantity0 rate1 quantity1) h
  simpa only [sourceTwoDateBankFullRowShear_undo] using hi

#print axioms sourceTwoDateBankFullRowShear_injective

/-- An arbitrary map into the 33 SOURCE rows is injective iff
its outputs are transformed by the full banking shear. -/
theorem sourceTwoDateBankFullRowShear_preserves_injectivity
    (loan0 deposit0 loan1 deposit1
      rate0 quantity0 rate1 quantity1 : ℝ)
    (L : (Fin 33 → ℝ) → Fin 33 → ℝ) :
    Function.Injective
        (fun z => sourceTwoDateBankFiveRowShear
          loan0 deposit0 loan1 deposit1
          rate0 quantity0 rate1 quantity1 (L z)) ↔
      Function.Injective L := by
  constructor
  · intro h x y hxy
    apply h
    exact congrArg
      (sourceTwoDateBankFiveRowShear
        loan0 deposit0 loan1 deposit1
        rate0 quantity0 rate1 quantity1) hxy
  · intro h x y hxy
    apply h
    exact (sourceTwoDateBankFullRowShear_injective
      loan0 deposit0 loan1 deposit1
      rate0 quantity0 rate1 quantity1) hxy

#print axioms sourceTwoDateBankFullRowShear_preserves_injectivity

end Ventura26LiquidityAllocation
