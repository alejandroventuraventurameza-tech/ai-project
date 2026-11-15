import Ventura26LiquidityAllocation.Source33BankEconomicRowDispatchCandidate
import Ventura26LiquidityAllocation.SourceTwoDateBankFullRowShearInverseCandidate

/-!
# Certified SOURCE 33-row dispatch integrated with full banking shear

The Lean dispatch certified by GitHub Actions run 43734185240,
commit ce9bf84d11988a791a7197ea485e8cb5d0c529be, identifies
both dates' rate, quantity, loan, deposit and balance equations in
the ORIGINAL EconomicModel.localReducedPrefixResidualVector.

This module now applies the already certified full six-banking-row
operator to that ACTUAL economic residual vector and to its ACTUAL
Frechet derivative in the positive-log coordinate chart.

The second theorem is a linear-algebraic injectivity equivalence
for applying the shear to SOURCE's derivative at a point. It does
NOT claim this sheared operator is the derivative of the frozen
Python residuals. The economic SOURCE/Python off-root derivative
identification and certified inverse bounds remain open.
-/

namespace Ventura26LiquidityAllocation

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- The certified SOURCE dispatch instantiated on the original
33-vector: loan, deposit and balance rows of date zero. -/
theorem sourceEconomicPrefix33_bankRowsZero_fromCertifiedDispatch
    (branch : LocalPrefixBranch) (P : Primitives S) (I : InheritedState)
    (dateOne recurrent : S) (tail : LocalPrefixContinuationRule)
    (z : Fin 33 → ℝ) :
    (localReducedPrefixResidualVector branch P I dateOne recurrent tail
        z (14 : Fin 33) =
      localReducedRemainingResidual P
        (localPrefixDateZeroData P I
          (localPrefixCoordinatesOfVector z) dateOne) 8) ∧
    (localReducedPrefixResidualVector branch P I dateOne recurrent tail
        z (15 : Fin 33) =
      localReducedRemainingResidual P
        (localPrefixDateZeroData P I
          (localPrefixCoordinatesOfVector z) dateOne) 9) ∧
    (localReducedPrefixResidualVector branch P I dateOne recurrent tail
        z (16 : Fin 33) =
      localReducedRemainingResidual P
        (localPrefixDateZeroData P I
          (localPrefixCoordinatesOfVector z) dateOne) 10) := by
  simpa only [localReducedPrefixResidualVector,
    localPrefixEquationOfIndex] using
    (sourcePrefix33_bankRowsZero_original branch P I
      (localPrefixCoordinatesOfVector z) dateOne recurrent tail)

#print axioms sourceEconomicPrefix33_bankRowsZero_fromCertifiedDispatch

/-- The certified SOURCE dispatch instantiated on the original
33-vector: loan, deposit and balance rows of date one. -/
theorem sourceEconomicPrefix33_bankRowsOne_fromCertifiedDispatch
    (branch : LocalPrefixBranch) (P : Primitives S) (I : InheritedState)
    (dateOne recurrent : S) (tail : LocalPrefixContinuationRule)
    (z : Fin 33 → ℝ) :
    (localReducedPrefixResidualVector branch P I dateOne recurrent tail
        z (30 : Fin 33) =
      localReducedRemainingResidual P
        (localPrefixDateOneData P
          (localPrefixCoordinatesOfVector z) dateOne recurrent tail) 8) ∧
    (localReducedPrefixResidualVector branch P I dateOne recurrent tail
        z (31 : Fin 33) =
      localReducedRemainingResidual P
        (localPrefixDateOneData P
          (localPrefixCoordinatesOfVector z) dateOne recurrent tail) 9) ∧
    (localReducedPrefixResidualVector branch P I dateOne recurrent tail
        z (32 : Fin 33) =
      localReducedRemainingResidual P
        (localPrefixDateOneData P
          (localPrefixCoordinatesOfVector z) dateOne recurrent tail) 10) := by
  simpa only [localReducedPrefixResidualVector,
    localPrefixEquationOfIndex] using
    (sourcePrefix33_bankRowsOne_original branch P I
      (localPrefixCoordinatesOfVector z) dateOne recurrent tail)

#print axioms sourceEconomicPrefix33_bankRowsOne_fromCertifiedDispatch

/-- Explicit SOURCE reduced residual vector, now transformed by
the date-zero/date-one bank-price and bank-balance row shear. -/
noncomputable def sourceEconomicPrefix33BankShearedResidual
    (branch : LocalPrefixBranch) (P : Primitives S) (I : InheritedState)
    (dateOne recurrent : S) (tail : LocalPrefixContinuationRule)
    (loan0 deposit0 loan1 deposit1
      rate0 quantity0 rate1 quantity1 : ℝ)
    (z : Fin 33 → ℝ) : Fin 33 → ℝ :=
  sourceTwoDateBankFiveRowShear
    loan0 deposit0 loan1 deposit1
    rate0 quantity0 rate1 quantity1
    (localReducedPrefixResidualVector branch P I dateOne recurrent tail z)

/-- The genuine SOURCE system has the same zero set as its
explicitly sheared 33-equation banking representation. No root
existence is assumed or asserted. -/
theorem sourceEconomicPrefix33BankShearedResidual_zero_iff
    (branch : LocalPrefixBranch) (P : Primitives S) (I : InheritedState)
    (dateOne recurrent : S) (tail : LocalPrefixContinuationRule)
    (loan0 deposit0 loan1 deposit1
      rate0 quantity0 rate1 quantity1 : ℝ)
    (z : Fin 33 → ℝ) :
    sourceEconomicPrefix33BankShearedResidual
      branch P I dateOne recurrent tail
      loan0 deposit0 loan1 deposit1 rate0 quantity0 rate1 quantity1 z = 0 ↔
    localReducedPrefixResidualVector
      branch P I dateOne recurrent tail z = 0 := by
  exact sourceTwoDateBankFiveRowShear_zero_iff
    loan0 deposit0 loan1 deposit1
    rate0 quantity0 rate1 quantity1
    (localReducedPrefixResidualVector branch P I dateOne recurrent tail z)

#print axioms sourceEconomicPrefix33BankShearedResidual_zero_iff

/-- In the original 33-dimensional SOURCE positive-log chart, the
sheared ACTUAL SOURCE Frechet derivative is injective exactly when
the untransformed ACTUAL SOURCE derivative is injective.

This identifies the objects in the theorem with EconomicModel's
concrete source Jacobian rather than an arbitrary abstract matrix.
It does not yet identify the resulting matrix with Python's Jacobian.
-/
theorem sourceEconomicPrefixLogJacobian_fullBankShear_injective_iff
    (branch : LocalPrefixBranch) (P : Primitives S) (I : InheritedState)
    (Z0 : LocalPrefixCoordinates) (dateOne recurrent : S)
    (tail : LocalPrefixContinuationRule)
    (loan0 deposit0 loan1 deposit1
      rate0 quantity0 rate1 quantity1 : ℝ)
    (z : Fin 33 → ℝ) :
    Function.Injective
      (fun h : Fin 33 → ℝ =>
        sourceTwoDateBankFiveRowShear
          loan0 deposit0 loan1 deposit1
          rate0 quantity0 rate1 quantity1
          ((fderiv ℝ
            (localReducedPrefixLogResidualVector branch P I Z0
              dateOne recurrent tail) z) h)) ↔
    Function.Injective
      (fderiv ℝ
        (localReducedPrefixLogResidualVector branch P I Z0
          dateOne recurrent tail) z) := by
  exact sourceTwoDateBankFullRowShear_preserves_injectivity
    loan0 deposit0 loan1 deposit1
    rate0 quantity0 rate1 quantity1
    (fderiv ℝ
      (localReducedPrefixLogResidualVector branch P I Z0
        dateOne recurrent tail) z)

#print axioms sourceEconomicPrefixLogJacobian_fullBankShear_injective_iff

end Ventura26LiquidityAllocation
