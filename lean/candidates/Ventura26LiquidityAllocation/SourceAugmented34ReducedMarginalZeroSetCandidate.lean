import Ventura26LiquidityAllocation.LocalScalarAugmented34SourceCandidate

/-!
# SOURCE 34-equation boundary zero: genuine implicit 33-row solution bridge

This module identifies the actual augmented 34-row SOURCE residual
evaluated on the SOURCE five-policy-parameter solutionLog restricted
to the reserve-remuneration intervention, with the scalar SOURCE
funding dual (not an artificial equation).

The proof is conditional on LocalScalarImplicitReduction, which
asserts existence and local uniqueness of solutionLog and derivative
signs; it does NOT establish this predicate from first principles.
-/

namespace Ventura26LiquidityAllocation
namespace ProposedLocalScalarAugmented34Source

open ProposedLocalScalarEconomicSlice

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- On the exact 33-equation SOURCE implicit solution, the 34-equation
boundary residual is literally (zero vector, reduced funding dual).
The radius and the 33-row zeros come from the explicit SOURCE
LocalScalarImplicitReduction premise. -/
theorem augmentedBoundaryZeroResidual_at_implicit_solution
    (P : Primitives S) (I : InheritedState) (Z0 : LocalPrefixCoordinates)
    (dateOne recurrent : S) (tail : LocalPrefixContinuationRule)
    (solutionLog : (Fin 5 → ℝ) → (Fin 33 → ℝ))
    (hred : LocalScalarImplicitReduction P I Z0 dateOne recurrent tail
      solutionLog) :
    ∃ radius : ℝ, 0 < radius ∧
      ∀ h : ℝ, reserveRemunerationSlice 0 h ∈
        Metric.ball (0 : Fin 5 → ℝ) radius →
      augmentedBoundaryZeroResidual P I Z0 dateOne recurrent tail
        (solutionLog (reserveRemunerationSlice 0 h)) h =
      (0, economicReserveRemunerationMarginal P Z0 solutionLog 0 h) := by
  rcases hred with ⟨_hbase, radius, hradius, _hdiffSol,
    _hdiffM, hrows, _hunique, _hslo, _hshi, _hrate⟩
  refine ⟨radius, hradius, ?_⟩
  intro h hin
  apply Prod.ext
  · funext row
    exact hrows (reserveRemunerationSlice 0 h) hin row
  · rfl

#print axioms augmentedBoundaryZeroResidual_at_implicit_solution

/-- In the genuine SOURCE 34-equation system, conditional on the
LOCAL implicit reduction, an augmented boundary root on that solution
slice is equivalent to zero of the exact reduced L funding dual.
No new equilibrium-existence claim is made. -/
theorem augmentedBoundaryZeroResidual_root_iff_source_marginal_zero
    (P : Primitives S) (I : InheritedState) (Z0 : LocalPrefixCoordinates)
    (dateOne recurrent : S) (tail : LocalPrefixContinuationRule)
    (solutionLog : (Fin 5 → ℝ) → (Fin 33 → ℝ))
    (hred : LocalScalarImplicitReduction P I Z0 dateOne recurrent tail
      solutionLog) :
    ∃ radius : ℝ, 0 < radius ∧
      ∀ h : ℝ, reserveRemunerationSlice 0 h ∈
        Metric.ball (0 : Fin 5 → ℝ) radius →
      (augmentedBoundaryZeroResidual P I Z0 dateOne recurrent tail
        (solutionLog (reserveRemunerationSlice 0 h)) h = (0, 0) ↔
       economicReserveRemunerationMarginal P Z0 solutionLog 0 h = 0) := by
  obtain ⟨radius, hradius, hpair⟩ :=
    augmentedBoundaryZeroResidual_at_implicit_solution
      P I Z0 dateOne recurrent tail solutionLog hred
  refine ⟨radius, hradius, ?_⟩
  intro h hin
  rw [hpair h hin]
  constructor
  · intro heq
    exact congrArg Prod.snd heq
  · intro hm
    simp [hm]

#print axioms augmentedBoundaryZeroResidual_root_iff_source_marginal_zero

end ProposedLocalScalarAugmented34Source
end Ventura26LiquidityAllocation
