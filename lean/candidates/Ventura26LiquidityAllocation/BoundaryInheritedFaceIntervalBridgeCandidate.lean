import Ventura26LiquidityAllocation.BoundaryInheritedFaceGateCandidate

/-!
# Conditional rational-interval gate for the exact SOURCE root

The independent Python outward-interval audit of the SOURCE formulas
reports the two endpoint signs at 1029135/1000000 and 1029136/1000000
and a positive initial nominal-face gap throughout that small interval.

The Lean theorems below establish the *logical reduction* to precisely
those three mathematical inequalities on the original model functions.
The inequalities are explicitly hypotheses: the Python program does
not become a Lean proof, and no artificial axioms are introduced.
-/

namespace Ventura26LiquidityAllocation
namespace ProposedBoundaryInheritedFaceIntervalBridge

open ProposedBoundaryResourceRoot
open ProposedBoundaryAnalyticPackage
open ProposedBoundaryFullPrefix
open ProposedBoundaryNormalizationBridge
open ProposedBoundaryInheritedFaceGate

/-- Strict monotonicity of the original resource residual localizes the
exact SOURCE root whenever the two narrow endpoint signs are established.
Only the endpoint signs are premises; uniqueness/monotonicity and the
broad-bracket root are already certified by the original Lean chain. -/
theorem sourceBoundaryRate_in_narrow_rational_interval
    (hleft : boundaryResourceResidual (1029135 / 1000000 : ℝ) < 0)
    (hright : 0 < boundaryResourceResidual (1029136 / 1000000 : ℝ)) :
    (1029135 / 1000000 : ℝ) < boundarySourceRate ∧
      boundarySourceRate < (1029136 / 1000000 : ℝ) := by
  have hmono : StrictMonoOn boundaryResourceResidual boundaryInterval :=
    boundary_analyticPackage.strictMonoOn
  have hroot : boundaryResourceResidual boundarySourceRate = 0 :=
    boundarySourceRate_spec.2.2
  have hrootMem : boundarySourceRate ∈ boundaryInterval :=
    ⟨boundarySourceRate_spec.1, boundarySourceRate_spec.2.1⟩
  have hleftMem : (1029135 / 1000000 : ℝ) ∈ boundaryInterval := by
    change boundaryLo ≤ (1029135 / 1000000 : ℝ) ∧
      (1029135 / 1000000 : ℝ) ≤ boundaryHi
    norm_num [boundaryLo, boundaryHi]
  have hrightMem : (1029136 / 1000000 : ℝ) ∈ boundaryInterval := by
    change boundaryLo ≤ (1029136 / 1000000 : ℝ) ∧
      (1029136 / 1000000 : ℝ) ≤ boundaryHi
    norm_num [boundaryLo, boundaryHi]
  constructor
  · by_contra hn
    have hle : boundarySourceRate ≤ (1029135 / 1000000 : ℝ) :=
      le_of_not_gt hn
    rcases lt_or_eq_of_le hle with hlt | heq
    · have hltValue := hmono hrootMem hleftMem hlt
      rw [hroot] at hltValue
      linarith
    · have heqValue := congrArg boundaryResourceResidual heq
      rw [hroot] at heqValue
      linarith
  · by_contra hn
    have hle : (1029136 / 1000000 : ℝ) ≤ boundarySourceRate :=
      le_of_not_gt hn
    rcases lt_or_eq_of_le hle with hlt | heq
    · have hltValue := hmono hrightMem hrootMem hlt
      rw [hroot] at hltValue
      linarith
    · have heqValue := congrArg boundaryResourceResidual heq
      rw [hroot] at heqValue
      linarith

/-- Future kernel-checked exact signs and a *uniform* face-gap lower
bound would rule out every competitive equilibrium using the unchanged
SOURCE inherited state. This is a conditional proof, not an invocation
of the independent Python interval artifact as an axiom. -/
theorem noCompetitiveEquilibrium_of_exact_interval_inequalities
    (G : ℝ) (X : Allocation LocalBridgePhase)
    (hleft : boundaryResourceResidual (1029135 / 1000000 : ℝ) < 0)
    (hright : 0 < boundaryResourceResidual (1029136 / 1000000 : ℝ))
    (hgap : ∀ R : ℝ,
      (1029135 / 1000000 : ℝ) ≤ R →
      R ≤ (1029136 / 1000000 : ℝ) →
      (8 / 100 : ℝ) <
        inheritedNominalFaceGap
          (boundaryPrimitives G R)
          (boundaryInitialState G R)) :
    ¬ CompetitiveEquilibrium
      (boundaryPrimitives G boundarySourceRate)
      (boundaryInitialState G boundarySourceRate) X := by
  obtain ⟨hlo, hhi⟩ :=
    sourceBoundaryRate_in_narrow_rational_interval hleft hright
  have hpositive : (8 / 100 : ℝ) <
      sourceBoundaryInheritedNominalFaceGap G := by
    exact hgap boundarySourceRate hlo.le hhi.le
  apply sourceBoundary_noCompetitiveEquilibrium_of_gap_ne_zero G X
  exact ne_of_gt (lt_trans (by norm_num) hpositive)

#print axioms sourceBoundaryRate_in_narrow_rational_interval
#print axioms noCompetitiveEquilibrium_of_exact_interval_inequalities

end ProposedBoundaryInheritedFaceIntervalBridge
end Ventura26LiquidityAllocation
