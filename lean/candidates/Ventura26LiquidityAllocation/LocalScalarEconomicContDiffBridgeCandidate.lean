import Mathlib.Analysis.Calculus.ContDiff.Comp
import Ventura26LiquidityAllocation.LocalScalarEconomicC1MonotonicityCandidate

/-!
# Paper-level C^1 regularity implies the local economic Schur sign

The manuscript states C^1 regularity of the reduced map. The preceding
module needs only continuity at the reference point of the Frechet
derivative evaluated in the collateral-slack direction. This module
proves that the manuscript-style ContDiffAt R 1 hypothesis is sufficient
for that directional continuity, and therefore for the source
K-dependent local antitonicity conclusion.

It does not establish ContDiffAt of the source M: this must be
derived from the actual 33-equation system and an implicit-function
certificate, not inferred from differentiability alone.
-/

namespace Ventura26LiquidityAllocation
namespace ProposedLocalScalarEconomicContDiffBridge

open ProposedLocalScalarEconomicC1Monotonicity
open ProposedLocalScalarEconomicSlice

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- A genuinely C^1 source reduced map has a continuous derivative
in the economic collateral-slack direction. -/
theorem source_contDiffAt_implies_schur_directional_continuity
    (P : Primitives S) (Z0 : LocalPrefixCoordinates)
    (solutionLog : (Fin 5 → ℝ) → (Fin 33 → ℝ))
    (hC1 : ContDiffAt ℝ 1
      (localScalarReducedMap P Z0 solutionLog)
      (0 : Fin 5 → ℝ)) :
    ContinuousAt
      (fun y : Fin 5 → ℝ =>
        fderiv ℝ (localScalarReducedMap P Z0 solutionLog)
          y localScalarSlackDirection)
      (0 : Fin 5 → ℝ) := by
  have hder : ContinuousAt
      (fderiv ℝ (localScalarReducedMap P Z0 solutionLog))
      (0 : Fin 5 → ℝ) :=
    hC1.continuousAt_fderiv (by norm_num)
  exact hder.clm_apply continuousAt_const

/-- C^1 at the source reference and the source differentiable
implicit-reduction predicate imply the K-dependent local
continuity/strict decrease required by the bifurcation proof.
The implicit-reduction predicate itself remains unproved. -/
theorem source_contDiffAt_implies_K_local_cone_monotonicity
    (P : Primitives S) (I : InheritedState) (Z0 : LocalPrefixCoordinates)
    (dateOne recurrent : S) (tail : LocalPrefixContinuationRule)
    (solutionLog : (Fin 5 → ℝ) → (Fin 33 → ℝ))
    (hred : LocalScalarImplicitReduction P I Z0 dateOne recurrent tail solutionLog)
    (hC1 : ContDiffAt ℝ 1
      (localScalarReducedMap P Z0 solutionLog)
      (0 : Fin 5 → ℝ)) :
    ∀ K : ℝ, 0 < K →
      ∃ rhoK : ℝ, 0 < rhoK ∧
        (∀ h : ℝ, -rhoK < h → h < 0 →
          ContinuousOn (fun s => economicReserveRemunerationMarginal
            P Z0 solutionLog s h) (Set.Icc (0 : ℝ) (-K * h))) ∧
        (∀ h : ℝ, -rhoK < h → h < 0 →
          StrictAntiOn (fun s => economicReserveRemunerationMarginal
            P Z0 solutionLog s h) (Set.Icc (0 : ℝ) (-K * h))) := by
  exact source_C1_implies_local_scalar_cone_antitonicity
    P I Z0 dateOne recurrent tail solutionLog hred
      (source_contDiffAt_implies_schur_directional_continuity
        P Z0 solutionLog hC1)

#print axioms source_contDiffAt_implies_schur_directional_continuity
#print axioms source_contDiffAt_implies_K_local_cone_monotonicity

end ProposedLocalScalarEconomicContDiffBridge
end Ventura26LiquidityAllocation
