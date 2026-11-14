import Ventura26LiquidityAllocation.SourceAugmented34ActualFrechetBlockCandidate
import Ventura26LiquidityAllocation.SourceFundingDualPositiveLogRegularityCandidate

/-!
# Economic SOURCE 34x34 Schur criterion with genuine L-dual smoothness

This module uses the actual SOURCE L funding-dual differentiability
theorem on the strictly positive economic log chart. Thus only
Fréchet regularity of the *33 first* modified-binding equations
is explicitly assumed, plus a supplied invertible real-linear map A
identified with the actual 33-coordinate economic Jacobian block.

The theorem does NOT assert the 33x33 block is invertible at the
economic reference, or that the Schur scalar is nonzero.
-/

namespace Ventura26LiquidityAllocation
namespace ProposedLocalScalarAugmented34Source

variable {S : Type*} [Fintype S] [DecidableEq S]

private abbrev Economic33 := Fin 33 → ℝ

/-- For the true SOURCE 34-equation remuneration experiment on a
positive log chart, the last equation's differentiability follows
from the original CRRA primitives, without an additional assumption.
Only the 33 modified-binding rows require an external regularity
hypothesis for this conditional Schur biconditional. -/
theorem sourceAugmented34_actualJacobian_bijective_iff_of_positive_log
    (P : Primitives S) (I : InheritedState) (Z0 : LocalPrefixCoordinates)
    (dateOne recurrent : S) (tail : LocalPrefixContinuationRule)
    (hZ0 : LocalPrefixCoordinatesPositive Z0)
    (zstar : Economic33) (hstar : ℝ)
    (A : Economic33 ≃ₗ[ℝ] Economic33)
    (hB : DifferentiableAt ℝ
      (sourceAugmented34Rows P I Z0 dateOne recurrent tail)
      (zstar, hstar))
    (hA : ∀ u : Economic33,
      (fderiv ℝ
        (sourceAugmented34Rows P I Z0 dateOne recurrent tail)
        (zstar, hstar)) (u, (0 : ℝ)) = A u) :
    Function.Bijective
      (fderiv ℝ (sourceAugmented34Map P I Z0 dateOne recurrent tail)
        (zstar, hstar)) ↔
    (fderiv ℝ (sourceAugmented34Dual P Z0) zstar)
      (A.symm ((fderiv ℝ
        (sourceAugmented34Rows P I Z0 dateOne recurrent tail)
        (zstar, hstar)) ((0 : Economic33), (1 : ℝ)))) ≠ 0 := by
  exact sourceAugmented34_actualJacobian_bijective_iff_schur
    P I Z0 dateOne recurrent tail zstar hstar
    (fderiv ℝ
      (sourceAugmented34Rows P I Z0 dateOne recurrent tail)
      (zstar, hstar))
    (fderiv ℝ (sourceAugmented34Dual P Z0) zstar)
    A
    hB.hasFDerivAt
    (sourceFundingDual_differentiableAt_positive_log
      P Z0 hZ0 zstar).hasFDerivAt
    hA

#print axioms sourceAugmented34_actualJacobian_bijective_iff_of_positive_log

end ProposedLocalScalarAugmented34Source
end Ventura26LiquidityAllocation
