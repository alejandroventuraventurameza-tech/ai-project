import Ventura26LiquidityAllocation.SourceRow21LogQuotientDirectCandidate

/-!
# Genuine SOURCE row 21: positive-root Frechet derivative without
# assuming a quotient derivative or importing a Python operator.

At a genuine SOURCE binding row-21 zero with positive date-two pledge
valuation, this module specializes the generic log quotient theorem to
the literal SOURCE date-one continuation and policy-intervened primitives.

Regularity of the SOURCE numerator and denominator remains explicit.
No economic root, matrix inverse, or all-row source/python identity is
asserted or smuggled in.
-/

namespace Ventura26LiquidityAllocation
namespace ProposedLocalScalarAugmented34Source

open ProposedLocalScalarCommonPledgeLogZero

variable {S : Type*} [Fintype S] [DecidableEq S]

theorem source_row21_actual_log_fderiv_at_positive_root
    (P : Primitives S) (I : InheritedState) (Z0 : LocalPrefixCoordinates)
    (dateOne recurrent : S) (tail : LocalPrefixContinuationRule)
    (zstar : Fin 33 → ℝ) (h : ℝ)
    (hJ : DifferentiableAt ℝ
      (fun z : Fin 33 → ℝ =>
        (localPrefixLogChart Z0 z).stateTwo.commonPledgeValue) zstar)
    (hV : DifferentiableAt ℝ
      (fun z : Fin 33 → ℝ =>
        sourceDateOneCommonPledgeValuation
          (sourceReserveSlicePrimitives P h)
          (localPrefixLogChart Z0 z) dateOne recurrent tail) zstar)
    (hpositive : 0 <
      sourceDateOneCommonPledgeValuation
        (sourceReserveSlicePrimitives P h)
        (localPrefixLogChart Z0 zstar) dateOne recurrent tail)
    (hroot : localReducedPrefixResidual LocalPrefixBranch.binding
      (sourceReserveSlicePrimitives P h) I
      (localPrefixLogChart Z0 zstar) dateOne recurrent tail
      LocalPrefixEquation.commonPledgeOne = 0) :
    fderiv ℝ
      (fun z : Fin 33 → ℝ =>
        Real.log
          ((localPrefixLogChart Z0 z).stateTwo.commonPledgeValue /
            sourceDateOneCommonPledgeValuation
              (sourceReserveSlicePrimitives P h)
              (localPrefixLogChart Z0 z) dateOne recurrent tail))
      zstar =
      (sourceDateOneCommonPledgeValuation
        (sourceReserveSlicePrimitives P h)
        (localPrefixLogChart Z0 zstar) dateOne recurrent tail)⁻¹ •
        fderiv ℝ
          (fun z : Fin 33 → ℝ =>
            localReducedPrefixResidual LocalPrefixBranch.binding
              (sourceReserveSlicePrimitives P h) I
              (localPrefixLogChart Z0 z) dateOne recurrent tail
              LocalPrefixEquation.commonPledgeOne)
          zstar := by
  let J : (Fin 33 → ℝ) → ℝ :=
    fun z => (localPrefixLogChart Z0 z).stateTwo.commonPledgeValue
  let V : (Fin 33 → ℝ) → ℝ :=
    fun z => sourceDateOneCommonPledgeValuation
      (sourceReserveSlicePrimitives P h)
      (localPrefixLogChart Z0 z) dateOne recurrent tail
  have hrow : ∀ z : Fin 33 → ℝ,
      localReducedPrefixResidual LocalPrefixBranch.binding
        (sourceReserveSlicePrimitives P h) I
        (localPrefixLogChart Z0 z) dateOne recurrent tail
        LocalPrefixEquation.commonPledgeOne = J z - V z := by
    intro z
    exact source_common_pledge_level_row
      (sourceReserveSlicePrimitives P h) I
      (localPrefixLogChart Z0 z) dateOne recurrent tail
  have hJV : J zstar = V zstar := by
    have hz := hrow zstar
    rw [hz] at hroot
    exact sub_eq_zero.mp hroot
  have hlog := source_row21_log_ratio_fderiv_at_positive_root
    J V zstar hJ hV hpositive hJV
  change fderiv ℝ (fun z => Real.log (J z / V z)) zstar =
    (V zstar)⁻¹ • fderiv ℝ
      (fun z : Fin 33 → ℝ =>
        localReducedPrefixResidual LocalPrefixBranch.binding
          (sourceReserveSlicePrimitives P h) I
          (localPrefixLogChart Z0 z) dateOne recurrent tail
          LocalPrefixEquation.commonPledgeOne) zstar
  rw [hlog]
  have hfunctions :
      (fun z : Fin 33 → ℝ =>
        localReducedPrefixResidual LocalPrefixBranch.binding
          (sourceReserveSlicePrimitives P h) I
          (localPrefixLogChart Z0 z) dateOne recurrent tail
          LocalPrefixEquation.commonPledgeOne) =
      (fun z => J z - V z) := by
    funext z
    exact hrow z
  rw [hfunctions, fderiv_fun_sub hJ hV]

#print axioms source_row21_actual_log_fderiv_at_positive_root

end ProposedLocalScalarAugmented34Source
end Ventura26LiquidityAllocation
