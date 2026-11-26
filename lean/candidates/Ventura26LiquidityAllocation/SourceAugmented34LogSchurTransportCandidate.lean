import Ventura26LiquidityAllocation.SourceAugmented34MinimalRegularityRankCandidate
import Ventura26LiquidityAllocation.SourceAugmented34PositiveLogSchurCandidate

/-!
# Exact economic Schur gate for the SOURCE two-log-collateral 34x34 Jacobian

The true SOURCE augmented system has the block form
  [ A  b ]
  [ c  0 ]
where the funding-dual row does not depend directly on remuneration h.
The two-log-collateral normalization permutes SOURCE output rows and
rescales their derivative at a root, so its Jacobian has identical
bijectivity condition.

Assume an actual SOURCE positive binding boundary root and the original
SOURCE map plus J2/V2 regularity. The linear equivalence A and its
identification with the TRUE 33-row SOURCE derivative remain explicit
premises: they are NOT supplied by this theorem. No numeric Schur scalar
or equilibrium root is certified by this statement.
-/

namespace Ventura26LiquidityAllocation
namespace ProposedLocalScalarAugmented34Source

open ProposedLocalScalarEconomicSlice
open ProposedLocalScalarCommonPledgeLogZero

variable {S : Type*} [Fintype S] [DecidableEq S]

theorem source34_twoPledge_log_jacobian_bijective_iff_source_schur
    (P : Primitives S) (I : InheritedState) (Z0 : LocalPrefixCoordinates)
    (dateOne recurrent : S) (tail : LocalPrefixContinuationRule)
    (hZ0 : LocalPrefixCoordinatesPositive Z0)
    (wstar : (Fin 33 → ℝ) × ℝ)
    (A : (Fin 33 → ℝ) ≃ₗ[ℝ] (Fin 33 → ℝ))
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
      wstar.1 wstar.2 = (0, 0))
    (hA : ∀ u : Fin 33 → ℝ,
      (fderiv ℝ
        (sourceAugmented34Rows P I Z0 dateOne recurrent tail)
        wstar) (u, (0 : ℝ)) = A u) :
    Function.Bijective
      (fderiv ℝ
        (fun w : (Fin 33 → ℝ) × ℝ =>
          sourceCanonicalTwoPledgeLog34 P I Z0 dateOne recurrent tail w.1 w.2)
        wstar) ↔
    (fderiv ℝ (sourceAugmented34Dual P Z0) wstar.1)
      (A.symm ((fderiv ℝ
        (sourceAugmented34Rows P I Z0 dateOne recurrent tail)
        wstar) ((0 : Fin 33 → ℝ), (1 : ℝ)))) ≠ 0 := by
  have hB : DifferentiableAt ℝ
      (sourceAugmented34Rows P I Z0 dateOne recurrent tail)
      wstar := by
    simpa only [sourceAugmented34Rows, augmentedBoundaryZeroResidual] using hF.fst
  have hbridge := source34_actual_jacobian_bijective_iff_with_primitive_regularity
    P I Z0 dateOne recurrent tail wstar hF hJ hV hpositive hroot
  rw [hbridge]
  simpa only [sourceAugmented34Map] using
    (sourceAugmented34_actualJacobian_bijective_iff_of_positive_log
      P I Z0 dateOne recurrent tail hZ0 wstar.1 wstar.2
      A hB hA)

#print axioms source34_twoPledge_log_jacobian_bijective_iff_source_schur

end ProposedLocalScalarAugmented34Source
end Ventura26LiquidityAllocation
