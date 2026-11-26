import Ventura26LiquidityAllocation.SourceTwoDateBankJacobianKernelCandidate

/-!
# Two-date SOURCE bank row shear: explicit two-sided inverse

The previous module establishes U (E v) = v. This companion
checks the reverse composition E (U v) = v, and therefore a
true bijection on the 33-output vector space. This remains an
abstract row operator, not a certificate of Python row parity.
-/

namespace Ventura26LiquidityAllocation

/-- Applying an arbitrary date-zero shear and then its negative
recovers the original 33-output vector. -/
theorem sourceMonetaryBankRowShear_right_inverse
    (a b : ℝ) (v : Fin 33 → ℝ) :
    sourceMonetaryBankRowShear a b
      (sourceMonetaryBankRowShear (-a) (-b) v) = v := by
  simpa only [neg_neg] using
    (sourceMonetaryBankRowShear_inverse (-a) (-b) v)

#print axioms sourceMonetaryBankRowShear_right_inverse

/-- The corresponding date-one identity uses rows 28, 29 and 32. -/
theorem sourceDateOneMonetaryBankRowShear_right_inverse
    (a b : ℝ) (v : Fin 33 → ℝ) :
    sourceDateOneMonetaryBankRowShear a b
      (sourceDateOneMonetaryBankRowShear (-a) (-b) v) = v := by
  simpa only [neg_neg] using
    (sourceDateOneMonetaryBankRowShear_inverse (-a) (-b) v)

#print axioms sourceDateOneMonetaryBankRowShear_right_inverse

/-- The recorded two-date undo is a right inverse as well as a
left inverse, since date-zero and date-one compositions reverse
in the proper order. -/
theorem sourceTwoDateMonetaryBankRowShear_right_inverse
    (a0 b0 a1 b1 : ℝ) (v : Fin 33 → ℝ) :
    sourceTwoDateMonetaryBankRowShear a0 b0 a1 b1
      (sourceTwoDateMonetaryBankRowShearUndo a0 b0 a1 b1 v) = v := by
  unfold sourceTwoDateMonetaryBankRowShear
    sourceTwoDateMonetaryBankRowShearUndo
  rw [sourceMonetaryBankRowShear_right_inverse,
    sourceDateOneMonetaryBankRowShear_right_inverse]

#print axioms sourceTwoDateMonetaryBankRowShear_right_inverse

/-- Explicit two-sided inverse entails surjectivity on the
33-output real vector space. -/
theorem sourceTwoDateMonetaryBankRowShear_surjective
    (a0 b0 a1 b1 : ℝ) :
    Function.Surjective
      (sourceTwoDateMonetaryBankRowShear a0 b0 a1 b1) := by
  intro v
  refine ⟨sourceTwoDateMonetaryBankRowShearUndo a0 b0 a1 b1 v, ?_⟩
  exact sourceTwoDateMonetaryBankRowShear_right_inverse a0 b0 a1 b1 v

#print axioms sourceTwoDateMonetaryBankRowShear_surjective

end Ventura26LiquidityAllocation
