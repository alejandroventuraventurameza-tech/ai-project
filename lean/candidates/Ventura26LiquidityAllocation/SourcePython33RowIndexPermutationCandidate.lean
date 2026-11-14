import Ventura26LiquidityAllocation.SourceEulerLogChartRowIndexCandidate

/-!
# Literal 33-row SOURCE label ordering versus frozen Python prefix ordering

The actual SOURCE economic residual uses the Fin 33 enumeration
localPrefixEquationOfIndex. The Python engine finite_irf.py uses an
identical set of economic rows but a different ordering in the firm
date-zero and date-one blocks.

This file records the SIX nontrivial index moves, checks the exact
left/right inverse of the proposed permutation in Lean, and proves
zero-set preservation of any row residual vector.

This is a rigorously proved ROW-INDEX contract. It is not a proof
that the values of 33 Python residual expressions coincide with the
corresponding source EconomicModel.lean expressions.
-/

namespace Ventura26LiquidityAllocation

/-- SOURCE index -> Python index, read against the audited 8+16+9
row partition in code/irf/audit_frozen_33_offroot_nonlinear_transform.py.
All other 27 indices are unchanged. -/
def sourceToPython33Index (i : Fin 33) : Fin 33 :=
  if i = 1 then 3
  else if i = 2 then 1
  else if i = 3 then 4
  else if i = 4 then 2
  else if i = 18 then 19
  else if i = 19 then 18
  else i

/-- Explicit Python index -> SOURCE index (the inverse permutation). -/
def pythonToSource33Index (j : Fin 33) : Fin 33 :=
  if j = 1 then 2
  else if j = 2 then 4
  else if j = 3 then 1
  else if j = 4 then 3
  else if j = 18 then 19
  else if j = 19 then 18
  else j

theorem pythonToSource33_sourceToPython33 (i : Fin 33) :
    pythonToSource33Index (sourceToPython33Index i) = i := by
  fin_cases i <;>
    decide

theorem sourceToPython33_pythonToSource33 (j : Fin 33) :
    sourceToPython33Index (pythonToSource33Index j) = j := by
  fin_cases j <;>
    decide

#print axioms pythonToSource33_sourceToPython33
#print axioms sourceToPython33_pythonToSource33

/-- An exact equivalence of all SOURCE and Python row INDEX SETS. -/
def sourcePython33IndexEquiv : Fin 33 ≃ Fin 33 where
  toFun := sourceToPython33Index
  invFun := pythonToSource33Index
  left_inv := pythonToSource33_sourceToPython33
  right_inv := sourceToPython33_pythonToSource33

theorem sourceToPython33Index_bijective :
    Function.Bijective sourceToPython33Index :=
  sourcePython33IndexEquiv.bijective

#print axioms sourceToPython33Index_bijective

/-- Reorder SOURCE row values into Python's equation-row order, without
modifying a single economic residual value. -/
def sourceRowsInPython33Order
    (v : Fin 33 → ℝ) : Fin 33 → ℝ :=
  fun j => v (pythonToSource33Index j)

/-- Reorder Python row values into the original SOURCE order. -/
def pythonRowsInSource33Order
    (v : Fin 33 → ℝ) : Fin 33 → ℝ :=
  fun i => v (sourceToPython33Index i)

theorem sourcePython33_rows_roundtrip
    (v : Fin 33 → ℝ) :
    pythonRowsInSource33Order (sourceRowsInPython33Order v) = v := by
  funext i
  simp [pythonRowsInSource33Order, sourceRowsInPython33Order,
    pythonToSource33_sourceToPython33]

theorem pythonSource33_rows_roundtrip
    (v : Fin 33 → ℝ) :
    sourceRowsInPython33Order (pythonRowsInSource33Order v) = v := by
  funext j
  simp [sourceRowsInPython33Order, pythonRowsInSource33Order,
    sourceToPython33_pythonToSource33]

#print axioms sourcePython33_rows_roundtrip
#print axioms pythonSource33_rows_roundtrip

/-- A reindexing alone creates and destroys NO economic roots. -/
theorem sourcePython33_rows_all_zero_iff
    (v : Fin 33 → ℝ) :
    (∀ j : Fin 33, sourceRowsInPython33Order v j = 0) ↔
      (∀ i : Fin 33, v i = 0) := by
  constructor
  · intro h i
    have hi := h (sourceToPython33Index i)
    simpa [sourceRowsInPython33Order,
      pythonToSource33_sourceToPython33] using hi
  · intro h j
    exact h (pythonToSource33Index j)

#print axioms sourcePython33_rows_all_zero_iff

end Ventura26LiquidityAllocation
