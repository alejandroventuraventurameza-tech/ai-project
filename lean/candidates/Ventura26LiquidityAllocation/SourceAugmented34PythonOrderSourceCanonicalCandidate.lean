import Ventura26LiquidityAllocation.SourceAugmented34CanonicalLogBoundaryCandidate
import Ventura26LiquidityAllocation.SourcePython33RowIndexPermutationCandidate

/-!
# Genuine SOURCE 33+1 boundary, reordered into Python's equation-row order

This puts the original SOURCE 34-equation operator in the SAME output
row ordering used by finite_irf.py, and uses SOURCE's exact positive
log-face collateral normalization for L at row 5. The entire first
block still evaluates real SOURCE Lean definitions. We prove that this
explicit algebraic reindexing and normalization preserve the EXACT
SOURCE 34-dimensional root set at arbitrary remuneration h.

This creates a precise target for future SOURCE/Python functional
identity. It does NOT execute the Python engine nor certify its
true derivatives or any SOURCE economic root.
-/

namespace Ventura26LiquidityAllocation
namespace ProposedLocalScalarAugmented34Source

open ProposedLocalScalarEconomicSlice

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- Exact SOURCE residual, in Python's 33-row OUTPUT ORDER and with a
logarithmic L-collateral row. The 34th row remains SOURCE's funding
dual, and the endogenous unknowns retain the ORIGINAL 33 log-chart
coordinate order plus policy innovation h. -/
noncomputable def sourceCanonicalPythonOrder34
    (P : Primitives S) (I : InheritedState) (Z0 : LocalPrefixCoordinates)
    (dateOne recurrent : S) (tail : LocalPrefixContinuationRule)
    (z : Fin 33 → ℝ) (h : ℝ) : (Fin 33 → ℝ) × ℝ :=
  (sourceRowsInPython33Order
    (sourceCanonicalLogBindingResidual P I Z0 dateOne recurrent tail z h),
   localNormalizedCollateralDualL P (localPrefixLogChart Z0 z))

/-- The reordered SOURCE map has exactly the same 34-root set as the
original SOURCE augmented boundary for every h, subject only to
the positive nominal-face/pledge chart. -/
theorem sourceCanonicalPythonOrder34_eq_zero_iff_source_boundary_zero
    (P : Primitives S) (I : InheritedState) (Z0 : LocalPrefixCoordinates)
    (dateOne recurrent : S) (tail : LocalPrefixContinuationRule)
    (z : Fin 33 → ℝ) (h : ℝ)
    (hp : 0 < (localPrefixLogChart Z0 z).stateOne.firmFaceL /
      sourceBindingLPledgeFace (sourceReserveSlicePrimitives P h)
        (localPrefixLogChart Z0 z)) :
    sourceCanonicalPythonOrder34 P I Z0 dateOne recurrent tail z h = (0, 0) ↔
      augmentedBoundaryZeroResidual P I Z0 dateOne recurrent tail z h = (0, 0) := by
  have hcanon := sourceCanonicalLogBoundary_eq_zero_iff_original_boundary_zero
    P I Z0 dateOne recurrent tail z h hp
  constructor
  · intro hz
    have hrows :
        ∀ row : Fin 33,
          sourceRowsInPython33Order
            (sourceCanonicalLogBindingResidual P I Z0 dateOne recurrent tail z h)
              row = 0 := by
      intro row
      have heq := congrArg
        (fun f : Fin 33 → ℝ => f row) (congrArg Prod.fst hz)
      simpa [sourceCanonicalPythonOrder34] using heq
    have hdual : localNormalizedCollateralDualL P
        (localPrefixLogChart Z0 z) = 0 := by
      simpa [sourceCanonicalPythonOrder34] using congrArg Prod.snd hz
    apply hcanon.mp
    apply Prod.ext
    · funext row
      exact (sourcePython33_rows_all_zero_iff _).mp hrows row
    · exact hdual
  · intro hz
    have hlog := hcanon.mpr hz
    have hrows : ∀ row : Fin 33,
        sourceCanonicalLogBindingResidual P I Z0 dateOne recurrent tail z h row = 0 := by
      intro row
      have heq := congrArg (fun f : Fin 33 → ℝ => f row)
        (congrArg Prod.fst hlog)
      simpa [sourceCanonicalLogBoundary] using heq
    have hdual : localNormalizedCollateralDualL P
        (localPrefixLogChart Z0 z) = 0 := by
      simpa [sourceCanonicalLogBoundary] using congrArg Prod.snd hlog
    apply Prod.ext
    · funext row
      exact (sourcePython33_rows_all_zero_iff _).mpr hrows row
    · exact hdual

#print axioms sourceCanonicalPythonOrder34_eq_zero_iff_source_boundary_zero

/-- In Python OUTPUT ORDER, roots of the SOURCE canonical log map are
equivalent to the ORIGINAL 33 SOURCE binding equations under the same
intervened primitives Pv(h), together with the same exact funding
dual, provided the SOURCE pledge denominator is nonzero. -/
theorem sourceCanonicalPythonOrder34_eq_zero_iff_original_economic_rows
    (P : Primitives S) (I : InheritedState) (Z0 : LocalPrefixCoordinates)
    (dateOne recurrent : S) (tail : LocalPrefixContinuationRule)
    (z : Fin 33 → ℝ) (h : ℝ)
    (hp : 0 < (localPrefixLogChart Z0 z).stateOne.firmFaceL /
      sourceBindingLPledgeFace (sourceReserveSlicePrimitives P h)
        (localPrefixLogChart Z0 z))
    (hne : sourceBindingLPledgeFace (sourceReserveSlicePrimitives P h)
      (localPrefixLogChart Z0 z) ≠ 0) :
    sourceCanonicalPythonOrder34 P I Z0 dateOne recurrent tail z h = (0, 0) ↔
    (∀ row : Fin 33,
      localReducedPrefixResidual LocalPrefixBranch.binding
        (sourceReserveSlicePrimitives P h) I
        (localPrefixLogChart Z0 z) dateOne recurrent tail
        (localPrefixEquationOfIndex row) = 0) ∧
    localNormalizedCollateralDualL
      (sourceReserveSlicePrimitives P h) (localPrefixLogChart Z0 z) = 0 := by
  rw [sourceCanonicalPythonOrder34_eq_zero_iff_source_boundary_zero
    P I Z0 dateOne recurrent tail z h hp,
    sourceAugmented34_nonzeroPolicy_root_iff_original_binding_boundary
      P I Z0 dateOne recurrent tail z h hne]

#print axioms sourceCanonicalPythonOrder34_eq_zero_iff_original_economic_rows

end ProposedLocalScalarAugmented34Source
end Ventura26LiquidityAllocation
