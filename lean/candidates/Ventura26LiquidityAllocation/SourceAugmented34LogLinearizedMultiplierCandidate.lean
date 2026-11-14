import Ventura26LiquidityAllocation.SourceAugmented34MinimalRegularityRankCandidate
import Ventura26LiquidityAllocation.SourceAugmented34LinearizedMultiplierCandidate

/-!
# Genuine SOURCE two-pledge-log 34 Jacobian and the economic multiplier

Given a linearized response of the 33 economic SOURCE equations to a
reserve-remuneration innovation, the scalar change in the genuine L
funding dual is EXACTLY the Schur transversality gate. Combining the
verified SOURCE-log derivative rank transport with the original SOURCE
linearized-multiplier theorem produces a direct biconditional for the
log-normalized 34x34 Jacobian.

This remains conditional on a genuine SOURCE boundary root, local
differentiability of original SOURCE and pledge primitives, positivity,
an identified invertible 33x33 block A, and the 33-row linearized
response. No Python floating calculation, interval inverse,
economic root, or full equilibrium is constructed.
-/

namespace Ventura26LiquidityAllocation
namespace ProposedLocalScalarAugmented34Source

open ProposedLocalScalarEconomicSlice
open ProposedLocalScalarCommonPledgeLogZero

variable {S : Type*} [Fintype S] [DecidableEq S]

theorem source34_logJacobian_bijective_iff_linearized_source_dual_ne
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
    (hA : ∀ x : Fin 33 → ℝ,
      (fderiv ℝ (sourceAugmented34Rows P I Z0 dateOne recurrent tail)
        wstar) (x, (0 : ℝ)) = A x)
    (u : Fin 33 → ℝ)
    (hu : (fderiv ℝ
      (sourceAugmented34Rows P I Z0 dateOne recurrent tail)
      wstar) (u, (1 : ℝ)) = 0) :
    Function.Bijective
      (fderiv ℝ
        (fun w : (Fin 33 → ℝ) × ℝ =>
          sourceCanonicalTwoPledgeLog34 P I Z0 dateOne recurrent tail w.1 w.2)
        wstar) ↔
      (fderiv ℝ (sourceAugmented34Dual P Z0) wstar.1) u ≠ 0 := by
  have hB : DifferentiableAt ℝ
      (sourceAugmented34Rows P I Z0 dateOne recurrent tail)
      wstar := by
    simpa only [sourceAugmented34Rows, augmentedBoundaryZeroResidual] using hF.fst
  have hbridge := source34_actual_jacobian_bijective_iff_with_primitive_regularity
    P I Z0 dateOne recurrent tail wstar hF hJ hV hpositive hroot
  rw [hbridge]
  simpa only [sourceAugmented34Map] using
    (sourceAugmented34_actualJacobian_bijective_iff_linearizedDual_ne
      P I Z0 dateOne recurrent tail hZ0 wstar.1 wstar.2
      A hB hA u hu)

#print axioms source34_logJacobian_bijective_iff_linearized_source_dual_ne

end ProposedLocalScalarAugmented34Source
end Ventura26LiquidityAllocation
