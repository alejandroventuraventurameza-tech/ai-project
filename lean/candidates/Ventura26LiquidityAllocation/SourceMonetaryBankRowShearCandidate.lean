import Ventura26LiquidityAllocation.SourceEconomicBankPolicyRootParityCandidate

/-!
# Invertible monetary cross-row shear on a 33-output Jacobian row vector

An algebraic 33-row operator: row 16 receives coefficients times rows
12 and 13; all other rows are preserved. Its inverse is the shear
with opposite coefficients. This is the linear-algebra prerequisite
for any future SOURCE/Python Jacobian comparison.

This file does NOT prove that the genuine Python Jacobian differs
from SOURCE by exactly this shear. The coefficients of such a
structural identity must be computed at a shared economic root,
with original row conventions and normalization accounted for.
-/

namespace Ventura26LiquidityAllocation

/-- Add arbitrary multiples of the two monetary policy rows
(indices 12 and 13) to the bank-balance row (index 16).
These are the ACTUAL date-zero SOURCE 33-output indices, as recorded
in EconomicModel.localPrefixEquationOfIndex. Date-one analogous rows
are 28, 29 and 32, not modified in this one-row shear. -/
def sourceMonetaryBankRowShear
    (a b : ℝ) (v : Fin 33 → ℝ) : Fin 33 → ℝ :=
  fun i => if i = 16 then v i + a * v 12 + b * v 13 else v i

/-- This shear has an explicit left and right inverse, obtained
by negating its coefficients. -/
theorem sourceMonetaryBankRowShear_inverse
    (a b : ℝ) (v : Fin 33 → ℝ) :
    sourceMonetaryBankRowShear (-a) (-b)
      (sourceMonetaryBankRowShear a b v) = v := by
  funext i
  by_cases hi : i = (16 : Fin 33)
  · subst i
    simp [sourceMonetaryBankRowShear]
    ring
  · simp [sourceMonetaryBankRowShear, hi]

#print axioms sourceMonetaryBankRowShear_inverse

/-- Zero sets are preserved by the 33-row shear. This does not
prove the existence of a SOURCE root. -/
theorem sourceMonetaryBankRowShear_zero_iff
    (a b : ℝ) (v : Fin 33 → ℝ) :
    sourceMonetaryBankRowShear a b v = 0 ↔ v = 0 := by
  constructor
  · intro h
    have hinv := sourceMonetaryBankRowShear_inverse a b v
    rw [h] at hinv
    have hz : sourceMonetaryBankRowShear (-a) (-b)
        (0 : Fin 33 → ℝ) = 0 := by
      funext j
      simp [sourceMonetaryBankRowShear]
    rw [hz] at hinv
    exact hinv.symm
  · intro h
    subst v
    funext i
    simp [sourceMonetaryBankRowShear]

#print axioms sourceMonetaryBankRowShear_zero_iff

end Ventura26LiquidityAllocation
