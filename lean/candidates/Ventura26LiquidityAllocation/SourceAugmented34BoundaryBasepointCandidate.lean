import Ventura26LiquidityAllocation.SourceAugmented34ReducedMarginalZeroSetCandidate

/-!
# SOURCE boundary-basepoint audit for the true augmented 34-row experiment

LocalScalarImplicitReduction asserts the exact 33-row modified binding
system solves at the baseline policy vector, but it does NOT assert
that the normalized L funding dual vanishes at that same point.

This theorem isolates the *additional* genuine SOURCE scalar equality
needed before the 34-dimensional implicit-function theorem could be
instantiated at the baseline.

This is a conditional equivalence and NOT an economic existence theorem.
-/

namespace Ventura26LiquidityAllocation
namespace ProposedLocalScalarAugmented34Source

open ProposedLocalScalarEconomicSlice

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- At the actual SOURCE implicit 33-row baseline, the full 34-row
boundary is zero precisely if the original normalized firm-L funding
dual is ALSO zero at the baseline log chart point.

The proof makes explicit that the 34th boundary condition is not
contained in the predicate LocalScalarImplicitReduction. -/
theorem augmentedBoundaryZeroResidual_base_iff_source_dual_zero
    (P : Primitives S) (I : InheritedState)
    (Z0 : LocalPrefixCoordinates)
    (dateOne recurrent : S) (tail : LocalPrefixContinuationRule)
    (solutionLog : (Fin 5 → ℝ) → (Fin 33 → ℝ))
    (hred : LocalScalarImplicitReduction P I Z0 dateOne recurrent tail
      solutionLog) :
    augmentedBoundaryZeroResidual P I Z0 dateOne recurrent tail
        (0 : Fin 33 → ℝ) (0 : ℝ) = (0, 0) ↔
      localNormalizedCollateralDualL P
        (localPrefixLogChart Z0 (0 : Fin 33 → ℝ)) = 0 := by
  obtain ⟨radius, hradius, hiff⟩ :=
    augmentedBoundaryZeroResidual_root_iff_source_marginal_zero
      P I Z0 dateOne recurrent tail solutionLog hred
  have hmem : reserveRemunerationSlice (0 : ℝ) (0 : ℝ) ∈
      Metric.ball (0 : Fin 5 → ℝ) radius := by
    simpa [reserveRemunerationSlice_zero] using
      (Metric.mem_ball_self hradius :
        (0 : Fin 5 → ℝ) ∈ Metric.ball 0 radius)
  have hbase : solutionLog (0 : Fin 5 → ℝ) = 0 := hred.1
  simpa only [reserveRemunerationSlice_zero, hbase,
    economicReserveRemunerationMarginal, localScalarReducedMap]
    using hiff (0 : ℝ) hmem

#print axioms augmentedBoundaryZeroResidual_base_iff_source_dual_zero

end ProposedLocalScalarAugmented34Source
end Ventura26LiquidityAllocation
