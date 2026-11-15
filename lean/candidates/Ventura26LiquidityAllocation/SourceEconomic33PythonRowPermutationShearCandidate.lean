import Ventura26LiquidityAllocation.SourceEconomic33BankShearIntegrationCandidate

/-!
# Exact SOURCE-to-Python 33-equation OUTPUT ROW ORDER

The original SOURCE localPrefixEquationOfIndex and Python
finite_irf.PREFIX_ROW_NAMES differ ONLY by the firm-equation order:
source indices 1,2,3,4 map to Python 3,1,4,2; and source indices
18,19 map to Python 19,18. The other 27 row positions agree.
The frozen Python audit code/irf/audit_source_python_33_row_permutation.py
verifies these data against both original source files.

This module implements the permutation WITH ITS INVERSE in Lean and
combines it with the already checked six-bank-row SOURCE shear and
the real EconomicModel log-chart Frechet derivative.

IMPORTANT: Permuting outputs is not a certificate of economic
SOURCE/Python residual identity or numerical Jacobian invertibility.
-/

namespace Ventura26LiquidityAllocation

/-- For each original SOURCE row, its corresponding Python row. -/
def source33RowToPython : Fin 33 → Fin 33
  | 1 => 3
  | 2 => 1
  | 3 => 4
  | 4 => 2
  | 18 => 19
  | 19 => 18
  | i => i

/-- For each original Python row, its corresponding SOURCE row. -/
def python33RowToSource : Fin 33 → Fin 33
  | 1 => 2
  | 2 => 4
  | 3 => 1
  | 4 => 3
  | 18 => 19
  | 19 => 18
  | i => i

theorem source33RowToPython_left_inverse (i : Fin 33) :
    python33RowToSource (source33RowToPython i) = i := by
  fin_cases i <;> rfl

theorem source33RowToPython_right_inverse (i : Fin 33) :
    source33RowToPython (python33RowToSource i) = i := by
  fin_cases i <;> rfl

#print axioms source33RowToPython_left_inverse
#print axioms source33RowToPython_right_inverse

/-- Reorder a SOURCE residual vector to ORIGINAL Python row order. -/
def source33RowsInPythonOrder
    (v : Fin 33 → ℝ) : Fin 33 → ℝ :=
  fun i => v (python33RowToSource i)

/-- Reorder a Python residual vector to ORIGINAL SOURCE row order. -/
def python33RowsInSourceOrder
    (v : Fin 33 → ℝ) : Fin 33 → ℝ :=
  fun i => v (source33RowToPython i)

/-- Exact round-trip from SOURCE via Python ordering. -/
theorem source33RowsInPythonOrder_undo
    (v : Fin 33 → ℝ) :
    python33RowsInSourceOrder (source33RowsInPythonOrder v) = v := by
  funext i
  simp only [python33RowsInSourceOrder, source33RowsInPythonOrder,
    source33RowToPython_left_inverse]

/-- Exact round-trip from Python via SOURCE ordering. -/
theorem python33RowsInSourceOrder_undo
    (v : Fin 33 → ℝ) :
    source33RowsInPythonOrder (python33RowsInSourceOrder v) = v := by
  funext i
  simp only [source33RowsInPythonOrder, python33RowsInSourceOrder,
    source33RowToPython_right_inverse]

/-- Row reordering is injective. -/
theorem source33RowsInPythonOrder_injective :
    Function.Injective source33RowsInPythonOrder := by
  intro v w h
  have hi := congrArg python33RowsInSourceOrder h
  simpa only [source33RowsInPythonOrder_undo] using hi

/-- Row reordering preserves the zero vector. -/
theorem source33RowsInPythonOrder_zero_iff
    (v : Fin 33 → ℝ) :
    source33RowsInPythonOrder v = 0 ↔ v = 0 := by
  constructor
  · intro h
    have hi := congrArg python33RowsInSourceOrder h
    simpa only [source33RowsInPythonOrder_undo,
      python33RowsInSourceOrder, Pi.zero_apply] using hi
  · intro h
    subst v
    rfl

/-- The banking row indices are fixed by the exact SOURCE/Python
equation permutation, at both dates. -/
theorem source33BankIndices_fixed :
    source33RowToPython 12 = 12 ∧
    source33RowToPython 13 = 13 ∧
    source33RowToPython 14 = 14 ∧
    source33RowToPython 15 = 15 ∧
    source33RowToPython 16 = 16 ∧
    source33RowToPython 28 = 28 ∧
    source33RowToPython 29 = 29 ∧
    source33RowToPython 30 = 30 ∧
    source33RowToPython 31 = 31 ∧
    source33RowToPython 32 = 32 := by
  decide

/-- Actual economic SOURCE residual vector: first perform the
six-bank-row shear, then reorder equations to Python's labels. -/
noncomputable def sourceEconomic33BankShearInPythonRowOrder
    {S : Type*} [Fintype S] [DecidableEq S]
    (branch : LocalPrefixBranch) (P : Primitives S) (I : InheritedState)
    (dateOne recurrent : S) (tail : LocalPrefixContinuationRule)
    (loan0 deposit0 loan1 deposit1
      rate0 quantity0 rate1 quantity1 : ℝ)
    (z : Fin 33 → ℝ) : Fin 33 → ℝ :=
  source33RowsInPythonOrder
    (sourceEconomicPrefix33BankShearedResidual
      branch P I dateOne recurrent tail
      loan0 deposit0 loan1 deposit1
      rate0 quantity0 rate1 quantity1 z)

/-- The combined exact row permutation and invertible bank shear
preserve the genuine SOURCE 33-equation zero set. -/
theorem sourceEconomic33BankShearInPythonRowOrder_zero_iff
    {S : Type*} [Fintype S] [DecidableEq S]
    (branch : LocalPrefixBranch) (P : Primitives S) (I : InheritedState)
    (dateOne recurrent : S) (tail : LocalPrefixContinuationRule)
    (loan0 deposit0 loan1 deposit1
      rate0 quantity0 rate1 quantity1 : ℝ)
    (z : Fin 33 → ℝ) :
    sourceEconomic33BankShearInPythonRowOrder
      branch P I dateOne recurrent tail
      loan0 deposit0 loan1 deposit1
      rate0 quantity0 rate1 quantity1 z = 0 ↔
    localReducedPrefixResidualVector
      branch P I dateOne recurrent tail z = 0 := by
  unfold sourceEconomic33BankShearInPythonRowOrder
  rw [source33RowsInPythonOrder_zero_iff,
    sourceEconomicPrefix33BankShearedResidual_zero_iff]

#print axioms sourceEconomic33BankShearInPythonRowOrder_zero_iff

/-- Applying BOTH certified output transforms to the actual
SOURCE positive-log Jacobian preserves injectivity. The conclusion
does not assert injectivity of the SOURCE Jacobian itself. -/
theorem sourceEconomicLogJacobian_bankShearAndPythonRowOrder_injective_iff
    {S : Type*} [Fintype S] [DecidableEq S]
    (branch : LocalPrefixBranch) (P : Primitives S) (I : InheritedState)
    (Z0 : LocalPrefixCoordinates) (dateOne recurrent : S)
    (tail : LocalPrefixContinuationRule)
    (loan0 deposit0 loan1 deposit1
      rate0 quantity0 rate1 quantity1 : ℝ)
    (z : Fin 33 → ℝ) :
    Function.Injective
      (fun h : Fin 33 → ℝ =>
        source33RowsInPythonOrder
          (sourceTwoDateBankFiveRowShear
            loan0 deposit0 loan1 deposit1
            rate0 quantity0 rate1 quantity1
            ((fderiv ℝ
              (localReducedPrefixLogResidualVector branch P I Z0
                dateOne recurrent tail) z) h))) ↔
    Function.Injective
      (fderiv ℝ
        (localReducedPrefixLogResidualVector branch P I Z0
          dateOne recurrent tail) z) := by
  constructor
  · intro h x y hxy
    apply h
    simpa only using congrArg
      (fun v => source33RowsInPythonOrder
        (sourceTwoDateBankFiveRowShear
          loan0 deposit0 loan1 deposit1
          rate0 quantity0 rate1 quantity1 v)) hxy
  · intro h x y hxy
    apply h
    apply sourceTwoDateBankFullRowShear_injective
      loan0 deposit0 loan1 deposit1
      rate0 quantity0 rate1 quantity1
    exact source33RowsInPythonOrder_injective hxy

#print axioms sourceEconomicLogJacobian_bankShearAndPythonRowOrder_injective_iff

end Ventura26LiquidityAllocation
