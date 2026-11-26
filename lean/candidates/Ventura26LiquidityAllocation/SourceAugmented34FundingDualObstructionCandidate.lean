import Ventura26LiquidityAllocation.LocalScalarAugmented34SourceCandidate

/-!
# SOURCE augmented boundary: a necessary funding-dual zero

This module uses the literal SOURCE 33+1 residual, not the frozen
Python surrogate.  It gives a logically unconditional obstruction:
no choice of reserve-remuneration innovation h can make (z,h) a
34-row root when the original normalized L funding dual at z is
nonzero.  It does NOT prove that the SOURCE dual is positive at any
particular reference, or that the original 33-row system has a root.
-/

namespace Ventura26LiquidityAllocation
namespace ProposedLocalScalarAugmented34Source

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- Every zero of the 34-dimensional SOURCE residual has exactly zero
original firm-L normalized funding dual. -/
theorem augmentedBoundary_root_implies_source_funding_dual_zero
    (P : Primitives S) (I : InheritedState)
    (Z0 : LocalPrefixCoordinates)
    (dateOne recurrent : S) (tail : LocalPrefixContinuationRule)
    (z : Fin 33 → ℝ) (h : ℝ)
    (hroot : augmentedBoundaryZeroResidual P I Z0 dateOne recurrent tail
      z h = (0, 0)) :
    localNormalizedCollateralDualL P (localPrefixLogChart Z0 z) = 0 := by
  exact ((augmentedBoundaryZeroResidual_eq_zero_iff
    P I Z0 dateOne recurrent tail z h).mp hroot).2

/-- A nonzero genuine SOURCE funding dual obstructs the complete
34-dimensional boundary equation, regardless of the 33 other rows. -/
theorem augmentedBoundary_not_root_of_source_funding_dual_ne_zero
    (P : Primitives S) (I : InheritedState)
    (Z0 : LocalPrefixCoordinates)
    (dateOne recurrent : S) (tail : LocalPrefixContinuationRule)
    (z : Fin 33 → ℝ) (h : ℝ)
    (hdual : localNormalizedCollateralDualL P
      (localPrefixLogChart Z0 z) ≠ 0) :
    augmentedBoundaryZeroResidual P I Z0 dateOne recurrent tail
      z h ≠ (0, 0) := by
  intro hroot
  exact hdual (augmentedBoundary_root_implies_source_funding_dual_zero
    P I Z0 dateOne recurrent tail z h hroot)

/-- Strictly positive SOURCE firm-L funding dual is a sufficient
obstruction to the augmented zero at this same log-chart coordinate.
This does not construct such an economically admissible coordinate. -/
theorem augmentedBoundary_not_root_of_source_funding_dual_pos
    (P : Primitives S) (I : InheritedState)
    (Z0 : LocalPrefixCoordinates)
    (dateOne recurrent : S) (tail : LocalPrefixContinuationRule)
    (z : Fin 33 → ℝ) (h : ℝ)
    (hdual : 0 < localNormalizedCollateralDualL P
      (localPrefixLogChart Z0 z)) :
    augmentedBoundaryZeroResidual P I Z0 dateOne recurrent tail
      z h ≠ (0, 0) := by
  exact augmentedBoundary_not_root_of_source_funding_dual_ne_zero
    P I Z0 dateOne recurrent tail z h (ne_of_gt hdual)

#print axioms augmentedBoundary_root_implies_source_funding_dual_zero
#print axioms augmentedBoundary_not_root_of_source_funding_dual_ne_zero
#print axioms augmentedBoundary_not_root_of_source_funding_dual_pos

end ProposedLocalScalarAugmented34Source
end Ventura26LiquidityAllocation
