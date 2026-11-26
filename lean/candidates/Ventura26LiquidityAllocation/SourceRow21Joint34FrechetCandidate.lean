import Ventura26LiquidityAllocation.SourceRow21LogQuotientDirectCandidate

/-!
# SOURCE common-pledge row 21: joint (33 log states, policy h) Frechet rule

Unlike the fixed-h differentiation gate, this result differentiates
with respect to the FULL 34-dimensional unknown (z,h), which is the
domain of the augmented SOURCE boundary Jacobian. The underlying
functions are the genuine SOURCE commitment level and next-date
valuation under the same policy slice.

The only analytic hypotheses are differentiability of the two actual
SOURCE functions on the joint chart, valuation positivity and the
genuine row-21 zero. No quotient derivative formula is postulated,
and no assertion of root existence or invertibility is made.
-/

namespace Ventura26LiquidityAllocation
namespace ProposedLocalScalarAugmented34Source

open ProposedLocalScalarCommonPledgeLogZero

variable {S : Type*} [Fintype S] [DecidableEq S]

theorem source_row21_joint34_log_fderiv_at_positive_root
    (P : Primitives S) (I : InheritedState) (Z0 : LocalPrefixCoordinates)
    (dateOne recurrent : S) (tail : LocalPrefixContinuationRule)
    (wstar : (Fin 33 → ℝ) × ℝ)
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
    (hroot :
      (sourceCanonicalPythonOrder34 P I Z0 dateOne recurrent tail
        wstar.1 wstar.2).1 (21 : Fin 33) = 0) :
    fderiv ℝ
      (fun w : (Fin 33 → ℝ) × ℝ =>
        Real.log
          ((localPrefixLogChart Z0 w.1).stateTwo.commonPledgeValue /
            sourceDateOneCommonPledgeValuation
              (sourceReserveSlicePrimitives P w.2)
              (localPrefixLogChart Z0 w.1) dateOne recurrent tail))
      wstar =
      (sourceDateOneCommonPledgeValuation
        (sourceReserveSlicePrimitives P wstar.2)
        (localPrefixLogChart Z0 wstar.1) dateOne recurrent tail)⁻¹ •
        fderiv ℝ
          (fun w : (Fin 33 → ℝ) × ℝ =>
            (sourceCanonicalPythonOrder34 P I Z0 dateOne recurrent tail
              w.1 w.2).1 (21 : Fin 33))
          wstar := by
  let J : ((Fin 33 → ℝ) × ℝ) → ℝ :=
    fun w => (localPrefixLogChart Z0 w.1).stateTwo.commonPledgeValue
  let V : ((Fin 33 → ℝ) × ℝ) → ℝ :=
    fun w => sourceDateOneCommonPledgeValuation
      (sourceReserveSlicePrimitives P w.2)
      (localPrefixLogChart Z0 w.1) dateOne recurrent tail
  have hrow : ∀ w : (Fin 33 → ℝ) × ℝ,
      (sourceCanonicalPythonOrder34 P I Z0 dateOne recurrent tail
        w.1 w.2).1 (21 : Fin 33) = J w - V w := by
    intro w
    rw [sourceCanonicalPythonOrder34_row21_eq_source_pledge_level]
    exact source_common_pledge_level_row
      (sourceReserveSlicePrimitives P w.2) I
      (localPrefixLogChart Z0 w.1) dateOne recurrent tail
  have hJV : J wstar = V wstar := by
    rw [hrow wstar] at hroot
    exact sub_eq_zero.mp hroot
  have hlog := source_row21_log_ratio_fderiv_at_positive_root
    J V wstar hJ hV hpositive hJV
  change fderiv ℝ (fun w => Real.log (J w / V w)) wstar =
    (V wstar)⁻¹ • fderiv ℝ
      (fun w : (Fin 33 → ℝ) × ℝ =>
        (sourceCanonicalPythonOrder34 P I Z0 dateOne recurrent tail
          w.1 w.2).1 (21 : Fin 33)) wstar
  rw [hlog]
  have hfunctions :
      (fun w : (Fin 33 → ℝ) × ℝ =>
        (sourceCanonicalPythonOrder34 P I Z0 dateOne recurrent tail
          w.1 w.2).1 (21 : Fin 33)) =
      (fun w => J w - V w) := by
    funext w
    exact hrow w
  rw [hfunctions, fderiv_fun_sub hJ hV]

#print axioms source_row21_joint34_log_fderiv_at_positive_root

end ProposedLocalScalarAugmented34Source
end Ventura26LiquidityAllocation
