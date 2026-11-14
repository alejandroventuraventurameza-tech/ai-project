import Ventura26LiquidityAllocation.SourceAugmented34TwoRowRescaleCandidate

/-!
# SOURCE 34-output: explicit permutation plus two collateral scalings

The genuine SOURCE 33+1 output is originally in SOURCE row order.
The Python-shaped canonical representation uses a verified permutation
of the first 33 rows, and changes rows 5 and 21. This file establishes
the exact abstract rank/bijectivity invariance of the COMPOSITE map,
not just a diagonal scaling applied in an unspecified row order.

The economic Frechet equality between these output transforms and the
true source residual derivatives is a separate obligation.
-/

namespace Ventura26LiquidityAllocation
namespace ProposedLocalScalarAugmented34Source

/-- Move the genuine SOURCE 33-row vector to the audited Python ordering,
while preserving the 34th source funding-dual equation. -/
def source34RowsInPythonOrder
    (v : (Fin 33 → ℝ) × ℝ) : (Fin 33 → ℝ) × ℝ :=
  (sourceRowsInPython33Order v.1, v.2)

/-- Inverse row permutation, leaving the funding-dual row intact. -/
def source34RowsInSourceOrder
    (v : (Fin 33 → ℝ) × ℝ) : (Fin 33 → ℝ) × ℝ :=
  (pythonRowsInSource33Order v.1, v.2)

theorem source34RowsInPythonOrder_leftInverse :
    Function.LeftInverse source34RowsInSourceOrder source34RowsInPythonOrder := by
  intro v
  apply Prod.ext
  · exact sourcePython33_rows_roundtrip v.1
  · rfl

theorem source34RowsInPythonOrder_rightInverse :
    Function.RightInverse source34RowsInSourceOrder source34RowsInPythonOrder := by
  intro v
  apply Prod.ext
  · exact pythonSource33_rows_roundtrip v.1
  · rfl

theorem source34RowsInPythonOrder_bijective :
    Function.Bijective source34RowsInPythonOrder :=
  ⟨source34RowsInPythonOrder_leftInverse.injective,
   source34RowsInPythonOrder_rightInverse.surjective⟩

#print axioms source34RowsInPythonOrder_bijective

theorem source34RowsInPythonOrder_comp_bijective_iff
    {E : Type*} (J : E → (Fin 33 → ℝ) × ℝ) :
    Function.Bijective (fun d => source34RowsInPythonOrder (J d)) ↔
      Function.Bijective J := by
  have hp := source34RowsInPythonOrder_bijective
  constructor
  · intro h
    constructor
    · intro x y heq
      exact h.1 (congrArg source34RowsInPythonOrder heq)
    · intro v
      obtain ⟨x, hx⟩ := h.2 (source34RowsInPythonOrder v)
      exact ⟨x, hp.1 hx⟩
  · intro h
    constructor
    · intro x y heq
      exact h.1 (hp.1 heq)
    · intro v
      obtain ⟨w, hw⟩ := hp.2 v
      obtain ⟨x, hx⟩ := h.2 w
      exact ⟨x, by simpa only [hx] using hw⟩

#print axioms source34RowsInPythonOrder_comp_bijective_iff

/-- EXACT abstract 34-dimensional rank transport with BOTH audited
Python row ordering and two independent nonzero collateral factors.
This does NOT identify a Python numerical derivative with SOURCE. -/
theorem source34PythonPermutation_twoRowScale_bijective_iff
    {E : Type*} (J : E → (Fin 33 → ℝ) × ℝ)
    (k5 k21 : ℝ) (hk5 : k5 ≠ 0) (hk21 : k21 ≠ 0) :
    Function.Bijective
      (fun d => source34RowsInPythonOrder
        (source34TwoRowRescale k5 k21 (J d))) ↔
      Function.Bijective J := by
  calc
    Function.Bijective
      (fun d => source34RowsInPythonOrder
        (source34TwoRowRescale k5 k21 (J d))) ↔
      Function.Bijective
        (fun d => source34TwoRowRescale k5 k21 (J d)) :=
        source34RowsInPythonOrder_comp_bijective_iff
          (fun d => source34TwoRowRescale k5 k21 (J d))
    _ ↔ Function.Bijective J :=
      source34TwoRowRescale_comp_bijective_iff J k5 k21 hk5 hk21

#print axioms source34PythonPermutation_twoRowScale_bijective_iff

end ProposedLocalScalarAugmented34Source
end Ventura26LiquidityAllocation
