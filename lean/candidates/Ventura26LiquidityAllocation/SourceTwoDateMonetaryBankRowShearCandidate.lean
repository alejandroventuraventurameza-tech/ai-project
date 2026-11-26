import Ventura26LiquidityAllocation.SourceMonetaryBankRowShearCandidate

/-!
# Date-one monetary bank-row shear in the original SOURCE 33-row order

EconomicModel.localPrefixEquationOfIndex maps date-one reserve-rate,
reserve-quantity, and bank-balance equations to indices 28, 29, 32.
The date-zero analog uses indices 12, 13, 16 and is established in
SourceMonetaryBankRowShearCandidate.

The statements here are algebraic row operations, not a claimed
equality to the original Python auxiliary Jacobian. The economic
off-root transformation and all domain assumptions remain to be shown.
-/

namespace Ventura26LiquidityAllocation

/-- Row 32 receives arbitrary multiples of the two date-one
monetary policy rows while the other 32 rows remain unchanged. -/
def sourceDateOneMonetaryBankRowShear
    (a b : ℝ) (v : Fin 33 → ℝ) : Fin 33 → ℝ :=
  fun i => if i = 32 then v i + a * v 28 + b * v 29 else v i

/-- Explicit inverse of the date-one monetary row shear. -/
theorem sourceDateOneMonetaryBankRowShear_inverse
    (a b : ℝ) (v : Fin 33 → ℝ) :
    sourceDateOneMonetaryBankRowShear (-a) (-b)
      (sourceDateOneMonetaryBankRowShear a b v) = v := by
  funext i
  by_cases hi : i = (32 : Fin 33)
  · subst i
    simp [sourceDateOneMonetaryBankRowShear]
    ring
  · simp [sourceDateOneMonetaryBankRowShear, hi]

#print axioms sourceDateOneMonetaryBankRowShear_inverse

/-- The date-one shear preserves the zero set of an arbitrary
33-output vector. It does not establish that a root exists. -/
theorem sourceDateOneMonetaryBankRowShear_zero_iff
    (a b : ℝ) (v : Fin 33 → ℝ) :
    sourceDateOneMonetaryBankRowShear a b v = 0 ↔ v = 0 := by
  constructor
  · intro h
    have hinv := sourceDateOneMonetaryBankRowShear_inverse a b v
    rw [h] at hinv
    have hz : sourceDateOneMonetaryBankRowShear (-a) (-b)
        (0 : Fin 33 → ℝ) = 0 := by
      funext j
      simp [sourceDateOneMonetaryBankRowShear]
    rw [hz] at hinv
    exact hinv.symm
  · intro h
    subst v
    funext i
    simp [sourceDateOneMonetaryBankRowShear]

#print axioms sourceDateOneMonetaryBankRowShear_zero_iff

/-- Compose the date-zero and date-one shears. The two economic
dates are kept distinct; coefficients may differ by date. -/
def sourceTwoDateMonetaryBankRowShear
    (a0 b0 a1 b1 : ℝ) (v : Fin 33 → ℝ) : Fin 33 → ℝ :=
  sourceDateOneMonetaryBankRowShear a1 b1
    (sourceMonetaryBankRowShear a0 b0 v)

/-- The composite zero set is identical to the original 33-row
zero set; this follows without an assumption that either
economic source system has a solution. -/
theorem sourceTwoDateMonetaryBankRowShear_zero_iff
    (a0 b0 a1 b1 : ℝ) (v : Fin 33 → ℝ) :
    sourceTwoDateMonetaryBankRowShear a0 b0 a1 b1 v = 0 ↔ v = 0 := by
  unfold sourceTwoDateMonetaryBankRowShear
  rw [sourceDateOneMonetaryBankRowShear_zero_iff,
    sourceMonetaryBankRowShear_zero_iff]

#print axioms sourceTwoDateMonetaryBankRowShear_zero_iff

end Ventura26LiquidityAllocation
