import Ventura26LiquidityAllocation.SourceAugmented34ExactRowCorrespondenceCandidate
import Ventura26LiquidityAllocation.SourceRow21Joint34FrechetCandidate
import Ventura26LiquidityAllocation.SourceRow5Joint34FrechetCandidate

/-!
# Actual SOURCE 34-coordinate rowwise Frechet factorization

This is the missing economic bridge from the genuine SOURCE augmented
boundary to the two-collateral-log normalized map. The OUTPUT rows are
permuted to the verified Python order. At a genuine SOURCE augmented
root, row 5 has a -1 derivative factor relative to the SOURCE
normalized L slack, and row 21 has a +1/V2 factor relative to the
SOURCE original common-pledge level residual.

All other SOURCE row functions are IDENTICAL after the permutation,
so their derivatives agree even without separately assumed regularity.
The final funding-dual row is also identical.

This theorem states equality of Frechet derivatives for EACH scalar
economic row. Its assumptions do not assert existence of the root,
invertibility of the 34x34 Jacobian or equality with Python floats.
-/

namespace Ventura26LiquidityAllocation
namespace ProposedLocalScalarAugmented34Source

open ProposedLocalScalarEconomicSlice
open ProposedLocalScalarCommonPledgeLogZero

variable {S : Type*} [Fintype S] [DecidableEq S]

theorem source34_actual_twoPledge_fderiv_eachRow
    (P : Primitives S) (I : InheritedState) (Z0 : LocalPrefixCoordinates)
    (dateOne recurrent : S) (tail : LocalPrefixContinuationRule)
    (wstar : (Fin 33 → ℝ) × ℝ)
    (hslack : DifferentiableAt ℝ
      (fun w : (Fin 33 → ℝ) × ℝ =>
        localBindingResidualWithSlack P I Z0 dateOne recurrent tail
          (reserveRemunerationSlice 0 w.2) w.1 (5 : Fin 33)) wstar)
    (hJ : DifferentiableAt ℝ
      (fun w : (Fin 33 → ℝ) × ℝ =>
        (localPrefixLogChart Z0 w.1).stateTwo.commonPledgeValue) wstar)
    (hV : DifferentiableAt ℝ
      (fun w : (Fin 33 → ℝ) × ℝ =>
        sourceDateOneCommonPledgeValuation
          (sourceReserveSlicePrimitives P w.2)
          (localPrefixLogChart Z0 w.1) dateOne recurrent tail) wstar)
    (hpositive : 0 <
      sourceDateOneCommonPledgeValuation
        (sourceReserveSlicePrimitives P wstar.2)
        (localPrefixLogChart Z0 wstar.1) dateOne recurrent tail)
    (hroot : augmentedBoundaryZeroResidual P I Z0 dateOne recurrent tail
      wstar.1 wstar.2 = (0, 0))
    (row : Fin 33) :
    fderiv ℝ
      (fun w : (Fin 33 → ℝ) × ℝ =>
        (sourceCanonicalTwoPledgeLog34 P I Z0 dateOne recurrent tail
          w.1 w.2).1 row) wstar =
    if row = (5 : Fin 33) then
      -fderiv ℝ
        (fun w : (Fin 33 → ℝ) × ℝ =>
          (augmentedBoundaryZeroResidual P I Z0 dateOne recurrent tail
            w.1 w.2).1 (pythonToSource33Index row)) wstar
    else if row = (21 : Fin 33) then
      (sourceDateOneCommonPledgeValuation
        (sourceReserveSlicePrimitives P wstar.2)
        (localPrefixLogChart Z0 wstar.1) dateOne recurrent tail)⁻¹ •
        fderiv ℝ
          (fun w : (Fin 33 → ℝ) × ℝ =>
            (augmentedBoundaryZeroResidual P I Z0 dateOne recurrent tail
              w.1 w.2).1 (pythonToSource33Index row)) wstar
    else
      fderiv ℝ
        (fun w : (Fin 33 → ℝ) × ℝ =>
          (augmentedBoundaryZeroResidual P I Z0 dateOne recurrent tail
            w.1 w.2).1 (pythonToSource33Index row)) wstar := by
  have hroot5 :
      (augmentedBoundaryZeroResidual P I Z0 dateOne recurrent tail
        wstar.1 wstar.2).1 (5 : Fin 33) = 0 := by
    have hh := congrArg
      (fun v : (Fin 33 → ℝ) × ℝ => v.1 (5 : Fin 33)) hroot
    simpa using hh
  have hroot21 :
      (sourceCanonicalPythonOrder34 P I Z0 dateOne recurrent tail
        wstar.1 wstar.2).1 (21 : Fin 33) = 0 := by
    rw [source34_python_row21_eq_augmented_source]
    have hh := congrArg
      (fun v : (Fin 33 → ℝ) × ℝ => v.1 (21 : Fin 33)) hroot
    simpa using hh
  by_cases hrow5 : row = (5 : Fin 33)
  · subst row
    have hfun :
        (fun w : (Fin 33 → ℝ) × ℝ =>
          (sourceCanonicalTwoPledgeLog34 P I Z0 dateOne recurrent tail
            w.1 w.2).1 (5 : Fin 33)) =
        (fun w : (Fin 33 → ℝ) × ℝ =>
          (sourceCanonicalPythonOrder34 P I Z0 dateOne recurrent tail
            w.1 w.2).1 (5 : Fin 33)) := by
      funext w
      simp [sourceCanonicalTwoPledgeLog34]
    rw [hfun]
    simpa [pythonToSource33Index] using
      (source_row5_joint34_log_fderiv_eq_neg_original_source
        P I Z0 dateOne recurrent tail wstar hslack hroot5)
  · by_cases hrow21 : row = (21 : Fin 33)
    · subst row
      have hfun :
          (fun w : (Fin 33 → ℝ) × ℝ =>
            (sourceCanonicalPythonOrder34 P I Z0 dateOne recurrent tail
              w.1 w.2).1 (21 : Fin 33)) =
          (fun w : (Fin 33 → ℝ) × ℝ =>
            (augmentedBoundaryZeroResidual P I Z0 dateOne recurrent tail
              w.1 w.2).1 (21 : Fin 33)) := by
        funext w
        exact source34_python_row21_eq_augmented_source
          P I Z0 dateOne recurrent tail w.1 w.2
      have hlog := source_row21_joint34_log_fderiv_at_positive_root
        P I Z0 dateOne recurrent tail wstar hJ hV hpositive hroot21
      rw [hfun] at hlog
      simpa [sourceCanonicalTwoPledgeLog34, pythonToSource33Index] using hlog
    · have hfun :
          (fun w : (Fin 33 → ℝ) × ℝ =>
            (sourceCanonicalTwoPledgeLog34 P I Z0 dateOne recurrent tail
              w.1 w.2).1 row) =
          (fun w : (Fin 33 → ℝ) × ℝ =>
            (augmentedBoundaryZeroResidual P I Z0 dateOne recurrent tail
              w.1 w.2).1 (pythonToSource33Index row)) := by
        funext w
        exact source34_twoPledge_unmodified_row_eq_source
          P I Z0 dateOne recurrent tail w.1 w.2 row hrow5 hrow21
      simpa [hrow5, hrow21] using
        congrArg (fun f : ((Fin 33 → ℝ) × ℝ) → ℝ =>
          fderiv ℝ f wstar) hfun

#print axioms source34_actual_twoPledge_fderiv_eachRow

/-- Exact agreement of the scalar dual DERIVATIVE for the original
and log-collateral SOURCE augmented maps, including policy direction h. -/
theorem source34_actual_twoPledge_fderiv_dual
    (P : Primitives S) (I : InheritedState) (Z0 : LocalPrefixCoordinates)
    (dateOne recurrent : S) (tail : LocalPrefixContinuationRule)
    (wstar : (Fin 33 → ℝ) × ℝ) :
    fderiv ℝ
      (fun w : (Fin 33 → ℝ) × ℝ =>
        (sourceCanonicalTwoPledgeLog34 P I Z0 dateOne recurrent tail
          w.1 w.2).2) wstar =
    fderiv ℝ
      (fun w : (Fin 33 → ℝ) × ℝ =>
        (augmentedBoundaryZeroResidual P I Z0 dateOne recurrent tail
          w.1 w.2).2) wstar := by
  have hfun :
      (fun w : (Fin 33 → ℝ) × ℝ =>
        (sourceCanonicalTwoPledgeLog34 P I Z0 dateOne recurrent tail
          w.1 w.2).2) =
      (fun w : (Fin 33 → ℝ) × ℝ =>
        (augmentedBoundaryZeroResidual P I Z0 dateOne recurrent tail
          w.1 w.2).2) := by
    funext w
    exact source34_twoPledge_dual_eq_source
      P I Z0 dateOne recurrent tail w.1 w.2
  rw [hfun]

#print axioms source34_actual_twoPledge_fderiv_dual

end ProposedLocalScalarAugmented34Source
end Ventura26LiquidityAllocation
