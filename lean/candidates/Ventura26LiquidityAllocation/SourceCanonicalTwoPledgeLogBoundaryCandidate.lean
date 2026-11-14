import Ventura26LiquidityAllocation.SourceCanonicalPythonCollateralFourCoordinatesCandidate
import Ventura26LiquidityAllocation.LocalScalarCommonPledgeLogZeroCandidate

/-!
# Genuine SOURCE 34 rows: normalize BOTH collateral relations as Python logs

The SOURCE binding-L log row at Python output index 5 is already exact.
The second collateral relation, SOURCE .commonPledgeOne at Python output
index 21, is still in LEVELS in sourceCanonicalPythonOrder34 while
finite_irf.binding_period_residual uses
log(J2 / ((1-delta) * Pi2 * q2)).

Here we normalize precisely that second row with the genuine SOURCE
date-one data record and the SAME intervened policy Primitives Pv(h).
On the economically required strictly positive collateral chart,
this log conversion preserves every original SOURCE 34-root at
arbitrary reserve-rate innovation h.

Only the root set is addressed: away from roots the row values and
their Jacobians differ by a nontrivial normalization. The new map
still has other SOURCE rows in levels, where Python may use logarithms.
-/

namespace Ventura26LiquidityAllocation
namespace ProposedLocalScalarAugmented34Source

open ProposedLocalScalarCommonPledgeLogZero

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- ORIGINAL SOURCE date-one common-pledge residual, at exactly the
same intervened primitives as the full 34-equation SOURCE boundary,
equals the existing canonical map's Python-order row 21. -/
theorem sourceCanonicalPythonOrder34_row21_eq_source_pledge_level
    (P : Primitives S) (I : InheritedState) (Z0 : LocalPrefixCoordinates)
    (dateOne recurrent : S) (tail : LocalPrefixContinuationRule)
    (z : Fin 33 → ℝ) (h : ℝ) :
    (sourceCanonicalPythonOrder34 P I Z0 dateOne recurrent tail z h).1
      (21 : Fin 33) =
    localReducedPrefixResidual LocalPrefixBranch.binding
      (sourceReserveSlicePrimitives P h) I
      (localPrefixLogChart Z0 z) dateOne recurrent tail
      LocalPrefixEquation.commonPledgeOne := by
  calc
    (sourceCanonicalPythonOrder34 P I Z0 dateOne recurrent tail z h).1
        (21 : Fin 33) =
      localBindingResidualWithSlack P I Z0 dateOne recurrent tail
        (ProposedLocalScalarEconomicSlice.reserveRemunerationSlice 0 h)
        z (21 : Fin 33) := by
          simp [sourceCanonicalPythonOrder34,
            sourceRowsInPython33Order, pythonToSource33Index,
            sourceCanonicalLogBindingResidual]
    _ = _ := by
      simpa [localPrefixEquationOfIndex] using
        (sourceBinding33_nonzeroPolicy_eachRow P I Z0
          dateOne recurrent tail z h (21 : Fin 33))

#print axioms sourceCanonicalPythonOrder34_row21_eq_source_pledge_level

/-- The genuine SOURCE 34 residual in Python row order, with TWO
collateral rows normalized like Python:
  - row 5, L nominal-face ratio;
  - row 21, date-one common-pledge valuation ratio.
All other 32 source residuals are unchanged. -/
noncomputable def sourceCanonicalTwoPledgeLog34
    (P : Primitives S) (I : InheritedState) (Z0 : LocalPrefixCoordinates)
    (dateOne recurrent : S) (tail : LocalPrefixContinuationRule)
    (z : Fin 33 → ℝ) (h : ℝ) : (Fin 33 → ℝ) × ℝ :=
  (fun row =>
    if row = (21 : Fin 33) then
      Real.log
        ((localPrefixLogChart Z0 z).stateTwo.commonPledgeValue /
          sourceDateOneCommonPledgeValuation
            (sourceReserveSlicePrimitives P h)
            (localPrefixLogChart Z0 z) dateOne recurrent tail)
    else
      (sourceCanonicalPythonOrder34 P I Z0 dateOne recurrent tail z h).1 row,
   (sourceCanonicalPythonOrder34 P I Z0 dateOne recurrent tail z h).2)

/-- Strictly positive level and next nominal valuation suffice to
transfer the exact zero-set equivalence from the genuine original
SOURCE row 21 to its Python-shaped log expression, at arbitrary h. -/
theorem sourceCanonicalTwoPledgeLog34_row_zero_iff
    (P : Primitives S) (I : InheritedState) (Z0 : LocalPrefixCoordinates)
    (dateOne recurrent : S) (tail : LocalPrefixContinuationRule)
    (z : Fin 33 → ℝ) (h : ℝ) (row : Fin 33)
    (hlevel : 0 < (localPrefixLogChart Z0 z).stateTwo.commonPledgeValue)
    (hvaluation : 0 <
      sourceDateOneCommonPledgeValuation
        (sourceReserveSlicePrimitives P h)
        (localPrefixLogChart Z0 z) dateOne recurrent tail) :
    (sourceCanonicalTwoPledgeLog34 P I Z0 dateOne recurrent tail z h).1 row = 0 ↔
    (sourceCanonicalPythonOrder34 P I Z0 dateOne recurrent tail z h).1 row = 0 := by
  by_cases hrow : row = (21 : Fin 33)
  · subst row
    change
      (Real.log
        ((localPrefixLogChart Z0 z).stateTwo.commonPledgeValue /
          sourceDateOneCommonPledgeValuation
            (sourceReserveSlicePrimitives P h)
            (localPrefixLogChart Z0 z) dateOne recurrent tail) = 0) ↔
      (sourceCanonicalPythonOrder34 P I Z0 dateOne recurrent tail z h).1
        (21 : Fin 33) = 0
    rw [sourceCanonicalPythonOrder34_row21_eq_source_pledge_level]
    exact source_common_pledge_log_zero_iff
      (sourceReserveSlicePrimitives P h) I
      (localPrefixLogChart Z0 z) dateOne recurrent tail
      hlevel hvaluation
  · simp [sourceCanonicalTwoPledgeLog34, hrow]

#print axioms sourceCanonicalTwoPledgeLog34_row_zero_iff

/-- SOURCE's original 34-root set is invariant under converting
BOTH collateral equations to the Python log-ratio form, subject to
strictly positive denominator and pledged face valuation.
No floating Python equation or finite P0 is assumed. -/
theorem sourceCanonicalTwoPledgeLog34_eq_zero_iff_original_source_boundary
    (P : Primitives S) (I : InheritedState) (Z0 : LocalPrefixCoordinates)
    (dateOne recurrent : S) (tail : LocalPrefixContinuationRule)
    (z : Fin 33 → ℝ) (h : ℝ)
    (hfaceRatio : 0 < (localPrefixLogChart Z0 z).stateOne.firmFaceL /
      sourceBindingLPledgeFace (sourceReserveSlicePrimitives P h)
        (localPrefixLogChart Z0 z))
    (hlevel : 0 < (localPrefixLogChart Z0 z).stateTwo.commonPledgeValue)
    (hvaluation : 0 <
      sourceDateOneCommonPledgeValuation
        (sourceReserveSlicePrimitives P h)
        (localPrefixLogChart Z0 z) dateOne recurrent tail) :
    sourceCanonicalTwoPledgeLog34 P I Z0 dateOne recurrent tail z h =
      (0, 0) ↔
    augmentedBoundaryZeroResidual P I Z0 dateOne recurrent tail z h =
      (0, 0) := by
  have hc := sourceCanonicalPythonOrder34_eq_zero_iff_source_boundary_zero
    P I Z0 dateOne recurrent tail z h hfaceRatio
  constructor
  · intro hz
    apply hc.mp
    apply Prod.ext
    · funext row
      have heq := congrArg (fun f : Fin 33 → ℝ => f row)
        (congrArg Prod.fst hz)
      exact (sourceCanonicalTwoPledgeLog34_row_zero_iff
        P I Z0 dateOne recurrent tail z h row hlevel hvaluation).mp heq
    · exact congrArg Prod.snd hz
  · intro hz
    have ho := hc.mpr hz
    apply Prod.ext
    · funext row
      have heq := congrArg (fun f : Fin 33 → ℝ => f row)
        (congrArg Prod.fst ho)
      exact (sourceCanonicalTwoPledgeLog34_row_zero_iff
        P I Z0 dateOne recurrent tail z h row hlevel hvaluation).mpr heq
    · exact congrArg Prod.snd ho

#print axioms sourceCanonicalTwoPledgeLog34_eq_zero_iff_original_source_boundary

end ProposedLocalScalarAugmented34Source
end Ventura26LiquidityAllocation
