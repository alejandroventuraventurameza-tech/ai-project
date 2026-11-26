import Ventura26LiquidityAllocation.SourceRow21RatioDifferentiabilityCandidate

/-!
# SOURCE row 21: genuine economic log/level Frechet transport at a root

The two functions used here are the original SOURCE state-two
common-pledge value and its actual next-date valuation. In contrast
to a Python surrogate, this bridge uses the genuine SOURCE 33-coordinate
log chart and policy-intervened primitives.

The quotient derivative formula is still a PREMISE. The result is a
conditional SOURCE-type specialization, not a root or inverse certificate.
-/

namespace Ventura26LiquidityAllocation
namespace ProposedLocalScalarAugmented34Source

open ProposedLocalScalarCommonPledgeLogZero

variable {S : Type*} [Fintype S] [DecidableEq S]

theorem source_row21_actual_log_fderiv_of_quotient_formula
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
    (hroot :
      (sourceCanonicalPythonOrder34 P I Z0 dateOne recurrent tail zstar h).1
        (21 : Fin 33) = 0)
    (hratio_deriv :
      fderiv ℝ
        (fun z : Fin 33 → ℝ =>
          (localPrefixLogChart Z0 z).stateTwo.commonPledgeValue /
            sourceDateOneCommonPledgeValuation
              (sourceReserveSlicePrimitives P h)
              (localPrefixLogChart Z0 z) dateOne recurrent tail) zstar =
      (sourceDateOneCommonPledgeValuation
        (sourceReserveSlicePrimitives P h)
        (localPrefixLogChart Z0 zstar) dateOne recurrent tail)⁻¹ •
        (fderiv ℝ
          (fun z : Fin 33 → ℝ =>
            (localPrefixLogChart Z0 z).stateTwo.commonPledgeValue) zstar -
         fderiv ℝ
          (fun z : Fin 33 → ℝ =>
            sourceDateOneCommonPledgeValuation
              (sourceReserveSlicePrimitives P h)
              (localPrefixLogChart Z0 z) dateOne recurrent tail) zstar)) :
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
            (localPrefixLogChart Z0 z).stateTwo.commonPledgeValue -
              sourceDateOneCommonPledgeValuation
                (sourceReserveSlicePrimitives P h)
                (localPrefixLogChart Z0 z) dateOne recurrent tail)
          zstar := by
  have hroot_level :
      (localPrefixLogChart Z0 zstar).stateTwo.commonPledgeValue =
        sourceDateOneCommonPledgeValuation
          (sourceReserveSlicePrimitives P h)
          (localPrefixLogChart Z0 zstar) dateOne recurrent tail := by
    rw [sourceCanonicalPythonOrder34_row21_eq_source_pledge_level] at hroot
    rw [source_common_pledge_level_row] at hroot
    exact sub_eq_zero.mp hroot
  have hlog := source_row21_log_ratio_fderiv_of_constituent_regularities
    (fun z : Fin 33 → ℝ =>
      (localPrefixLogChart Z0 z).stateTwo.commonPledgeValue)
    (fun z : Fin 33 → ℝ =>
      sourceDateOneCommonPledgeValuation
        (sourceReserveSlicePrimitives P h)
        (localPrefixLogChart Z0 z) dateOne recurrent tail)
    zstar hJ hV hpositive hroot_level hratio_deriv
  rw [hlog, fderiv_fun_sub hJ hV]

#print axioms source_row21_actual_log_fderiv_of_quotient_formula

end ProposedLocalScalarAugmented34Source
end Ventura26LiquidityAllocation
