import Ventura26LiquidityAllocation.SourceBankBalanceTwoPolicyJacobianShearCandidate
import Ventura26LiquidityAllocation.SourceTwoDateBankJacobianKernelCandidate

/-!
# Joint two-date SOURCE bank pricing and balance row operator

Original SOURCE 33-row indices:
 date zero: rate=12, quantity=13, loan=14, deposit=15, balance=16
 date one:  rate=28, quantity=29, loan=30, deposit=31, balance=32

The pricing shear below modifies four bank pricing rows by multiples
of the respective monetary RATE row. The previously checked balance
shear modifies bank balance rows by rate and QUANTITY policy rows.

This is an abstract, explicit, invertible 33-row transformation.
It will only be an economic Jacobian bridge after the SOURCE/Python
off-root row derivatives, normalizations and parameter identification
are separately proved. No full-rank assertion is made for SOURCE.
-/

namespace Ventura26LiquidityAllocation

/-- Modify four pricing equations with contemporaneous policy-rate
row multiples while leaving all other SOURCE rows intact. -/
def sourceTwoDateBankPricingRowShear
    (loan0 deposit0 loan1 deposit1 : ℝ)
    (v : Fin 33 → ℝ) : Fin 33 → ℝ :=
  fun i =>
    if i = 14 then v i + loan0 * v 12
    else if i = 15 then v i + deposit0 * v 12
    else if i = 30 then v i + loan1 * v 28
    else if i = 31 then v i + deposit1 * v 28
    else v i

/-- Pricing row shear is undone by negating its four coefficients. -/
theorem sourceTwoDateBankPricingRowShear_inverse
    (loan0 deposit0 loan1 deposit1 : ℝ)
    (v : Fin 33 → ℝ) :
    sourceTwoDateBankPricingRowShear
      (-loan0) (-deposit0) (-loan1) (-deposit1)
      (sourceTwoDateBankPricingRowShear
        loan0 deposit0 loan1 deposit1 v) = v := by
  funext i
  fin_cases i <;> norm_num [sourceTwoDateBankPricingRowShear] <;> ring

#print axioms sourceTwoDateBankPricingRowShear_inverse

/-- A pricing row shear cannot create or destroy a zero residual. -/
theorem sourceTwoDateBankPricingRowShear_zero_iff
    (loan0 deposit0 loan1 deposit1 : ℝ)
    (v : Fin 33 → ℝ) :
    sourceTwoDateBankPricingRowShear
      loan0 deposit0 loan1 deposit1 v = 0 ↔ v = 0 := by
  constructor
  · intro h
    have hi := sourceTwoDateBankPricingRowShear_inverse
      loan0 deposit0 loan1 deposit1 v
    rw [h] at hi
    have hz : sourceTwoDateBankPricingRowShear
        (-loan0) (-deposit0) (-loan1) (-deposit1)
        (0 : Fin 33 → ℝ) = 0 := by
      funext i
      simp [sourceTwoDateBankPricingRowShear]
    rw [hz] at hi
    exact hi.symm
  · intro h
    subst v
    funext i
    simp [sourceTwoDateBankPricingRowShear]

#print axioms sourceTwoDateBankPricingRowShear_zero_iff

/-- Full abstract banking row operation: pricing on rows
14,15,30,31 and balance on rows 16,32, with policy rows unchanged. -/
def sourceTwoDateBankFiveRowShear
    (loan0 deposit0 loan1 deposit1
      rate0 quantity0 rate1 quantity1 : ℝ)
    (v : Fin 33 → ℝ) : Fin 33 → ℝ :=
  sourceTwoDateMonetaryBankRowShear
    rate0 quantity0 rate1 quantity1
    (sourceTwoDateBankPricingRowShear
      loan0 deposit0 loan1 deposit1 v)

/-- The entire abstract banking 6-row change preserves the
33-component zero set, for arbitrary real coefficients. -/
theorem sourceTwoDateBankFiveRowShear_zero_iff
    (loan0 deposit0 loan1 deposit1
      rate0 quantity0 rate1 quantity1 : ℝ)
    (v : Fin 33 → ℝ) :
    sourceTwoDateBankFiveRowShear
      loan0 deposit0 loan1 deposit1
      rate0 quantity0 rate1 quantity1 v = 0 ↔ v = 0 := by
  unfold sourceTwoDateBankFiveRowShear
  rw [sourceTwoDateMonetaryBankRowShear_zero_iff,
    sourceTwoDateBankPricingRowShear_zero_iff]

#print axioms sourceTwoDateBankFiveRowShear_zero_iff

end Ventura26LiquidityAllocation
