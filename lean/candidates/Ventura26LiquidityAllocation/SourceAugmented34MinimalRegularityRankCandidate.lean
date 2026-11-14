import Ventura26LiquidityAllocation.SourceAugmented34LogRegularityCandidate
import Ventura26LiquidityAllocation.SourceAugmented34ActualJacobianRankCandidate

/-!
# SOURCE 34 rank equivalence with no independent log-map/slack regularity

This strengthens the actual SOURCE 34x34 Jacobian transport: the ONLY
differentiability hypotheses are the original SOURCE 34-vector F, the
date-two common-pledge value J2, and the SOURCE continuation valuation
V2. Differentiability of the original L slack row follows from F;
that of the log-normalized map follows from the positive-root log
regularity theorem. The exact derivative factorization is then used,
rather than postulated.

An economic root, local regularity and V2 > 0 remain explicit premises.
It neither supplies a root nor establishes full Jacobian invertibility.
-/

namespace Ventura26LiquidityAllocation
namespace ProposedLocalScalarAugmented34Source

open ProposedLocalScalarEconomicSlice
open ProposedLocalScalarCommonPledgeLogZero

variable {S : Type*} [Fintype S] [DecidableEq S]

theorem source34_actual_jacobian_bijective_iff_with_primitive_regularity
    (P : Primitives S) (I : InheritedState) (Z0 : LocalPrefixCoordinates)
    (dateOne recurrent : S) (tail : LocalPrefixContinuationRule)
    (wstar : (Fin 33 → ℝ) × ℝ)
    (hF : DifferentiableAt ℝ
      (fun w : (Fin 33 → ℝ) × ℝ =>
        augmentedBoundaryZeroResidual P I Z0 dateOne recurrent tail w.1 w.2)
      wstar)
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
      wstar.1 wstar.2 = (0, 0)) :
    Function.Bijective
      (fderiv ℝ
        (fun w : (Fin 33 → ℝ) × ℝ =>
          sourceCanonicalTwoPledgeLog34 P I Z0 dateOne recurrent tail w.1 w.2)
        wstar) ↔
    Function.Bijective
      (fderiv ℝ
        (fun w : (Fin 33 → ℝ) × ℝ =>
          augmentedBoundaryZeroResidual P I Z0 dateOne recurrent tail w.1 w.2)
        wstar) := by
  have hslack : DifferentiableAt ℝ
      (fun w : (Fin 33 → ℝ) × ℝ =>
        localBindingResidualWithSlack P I Z0 dateOne recurrent tail
          (reserveRemunerationSlice 0 w.2) w.1 (5 : Fin 33)) wstar := by
    have hrow := ((differentiableAt_pi).mp hF.fst) (5 : Fin 33)
    simpa only [augmentedBoundaryZeroResidual] using hrow
  have hG : DifferentiableAt ℝ
      (fun w : (Fin 33 → ℝ) × ℝ =>
        sourceCanonicalTwoPledgeLog34 P I Z0 dateOne recurrent tail w.1 w.2)
      wstar :=
    source34_twoPledge_differentiableAt_of_original_at_positive_root
      P I Z0 dateOne recurrent tail wstar hF hJ hV hpositive hroot
  exact source34_actual_source_jacobian_bijective_iff_log_normalized
    P I Z0 dateOne recurrent tail wstar hF hG hslack hJ hV
    hpositive hroot

#print axioms source34_actual_jacobian_bijective_iff_with_primitive_regularity

end ProposedLocalScalarAugmented34Source
end Ventura26LiquidityAllocation
