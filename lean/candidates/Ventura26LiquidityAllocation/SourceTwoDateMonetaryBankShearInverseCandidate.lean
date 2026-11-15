import Ventura26LiquidityAllocation.SourceTwoDateMonetaryBankRowShearCandidate

/-!
# Two-date SOURCE monetary row shear: exact inverse and literal row labels

This module strengthens the abstract 33-output two-date row transform
with an explicit inverse and audits the six affected equation labels
against EconomicModel.localPrefixEquationOfIndex. The result is
independent of a candidate equilibrium and does not establish that
the frozen Python auxiliary has an identical Jacobian.
-/

namespace Ventura26LiquidityAllocation

/-- Literal SOURCE label for the date-zero policy-rate row. -/
theorem sourceBankShear_index_rate_zero :
    localPrefixEquationOfIndex (12 : Fin 33) =
      LocalPrefixEquation.reserveRateRuleZero := by rfl

/-- Literal SOURCE label for the date-zero policy-quantity row. -/
theorem sourceBankShear_index_quantity_zero :
    localPrefixEquationOfIndex (13 : Fin 33) =
      LocalPrefixEquation.reserveQuantityRuleZero := by rfl

/-- Literal SOURCE label for the date-zero bank-balance row. -/
theorem sourceBankShear_index_balance_zero :
    localPrefixEquationOfIndex (16 : Fin 33) =
      LocalPrefixEquation.bankBalanceZero := by rfl

/-- Literal SOURCE label for the date-one policy-rate row. -/
theorem sourceBankShear_index_rate_one :
    localPrefixEquationOfIndex (28 : Fin 33) =
      LocalPrefixEquation.reserveRateRuleOne := by rfl

/-- Literal SOURCE label for the date-one policy-quantity row. -/
theorem sourceBankShear_index_quantity_one :
    localPrefixEquationOfIndex (29 : Fin 33) =
      LocalPrefixEquation.reserveQuantityRuleOne := by rfl

/-- Literal SOURCE label for the date-one bank-balance row. -/
theorem sourceBankShear_index_balance_one :
    localPrefixEquationOfIndex (32 : Fin 33) =
      LocalPrefixEquation.bankBalanceOne := by rfl

/-- Undo the date-one shear first and then the date-zero shear. -/
def sourceTwoDateMonetaryBankRowShearUndo
    (a0 b0 a1 b1 : ℝ) (v : Fin 33 → ℝ) : Fin 33 → ℝ :=
  sourceMonetaryBankRowShear (-a0) (-b0)
    (sourceDateOneMonetaryBankRowShear (-a1) (-b1) v)

/-- Full left inverse of the two-date 33-output monetary row shear. -/
theorem sourceTwoDateMonetaryBankRowShear_undo
    (a0 b0 a1 b1 : ℝ) (v : Fin 33 → ℝ) :
    sourceTwoDateMonetaryBankRowShearUndo a0 b0 a1 b1
      (sourceTwoDateMonetaryBankRowShear a0 b0 a1 b1 v) = v := by
  unfold sourceTwoDateMonetaryBankRowShearUndo
    sourceTwoDateMonetaryBankRowShear
  rw [sourceDateOneMonetaryBankRowShear_inverse,
    sourceMonetaryBankRowShear_inverse]

#print axioms sourceTwoDateMonetaryBankRowShear_undo

/-- Therefore the two-date SOURCE row shear is injective. -/
theorem sourceTwoDateMonetaryBankRowShear_injective
    (a0 b0 a1 b1 : ℝ) :
    Function.Injective
      (sourceTwoDateMonetaryBankRowShear a0 b0 a1 b1) := by
  intro v w h
  have hv := congrArg
    (sourceTwoDateMonetaryBankRowShearUndo a0 b0 a1 b1) h
  simpa only [sourceTwoDateMonetaryBankRowShear_undo] using hv

#print axioms sourceTwoDateMonetaryBankRowShear_injective

end Ventura26LiquidityAllocation
