import Ventura26LiquidityAllocation.BoundaryPredeterminedStateCandidate

/-!
# Reducing the exact SOURCE interval gap obligation to one fiscal reference

The source gap is exactly independent of G. Consequently the remaining
kernel obligation of a uniform gap lower bound over a rational interval
can be stated at the fiscal reference G = 0, then transported without
additional numerical work to any fiscal bond supply G.

This is a reduction of an unproved numerical inequality, NOT its proof.
No floating-point output, axiom or numerical certificate is imported.
-/

namespace Ventura26LiquidityAllocation
namespace ProposedBoundaryFaceGapFiscalReduction

open ProposedStationaryPrimitives
open ProposedStationaryInheritedState
open ProposedStationaryRealScale
open ProposedBoundaryResourceRoot
open ProposedBoundaryInheritedFaceDecomposition
open ProposedBoundaryFullPrefix
open ProposedBoundaryInheritedFaceGate
open ProposedBoundaryInheritedFaceMechanism
open ProposedBoundaryInheritedFaceIntervalBridge
open ProposedBoundaryNormalizationBridge

/-- The SOURCE nominal face gap at any G equals its value at G=0.
This is an exact source-side equation, not a numerical comparison. -/
theorem source_gap_eq_at_zero_fiscal (G R : ℝ) :
    inheritedNominalFaceGap
      (boundaryPrimitives G R) (boundaryInitialState G R) =
    inheritedNominalFaceGap
      (boundaryPrimitives 0 R) (boundaryInitialState 0 R) := by
  exact boundaryInheritedGap_independent_of_G G 0 R

/-- A uniform lower bound proved ONCE at fiscal reference G=0 suffices
for ALL fiscal-bond supplies. The reference lower bound is an explicit
hypothesis and must ultimately be established in the Lean kernel. -/
theorem uniform_gap_from_zero_fiscal_reference
    (hzero : ∀ R : ℝ,
      (1029135 / 1000000 : ℝ) ≤ R →
      R ≤ (1029136 / 1000000 : ℝ) →
      (8 / 100 : ℝ) <
        inheritedNominalFaceGap
          (boundaryPrimitives 0 R) (boundaryInitialState 0 R))
    (G R : ℝ)
    (hlo : (1029135 / 1000000 : ℝ) ≤ R)
    (hhi : R ≤ (1029136 / 1000000 : ℝ)) :
    (8 / 100 : ℝ) <
      inheritedNominalFaceGap
        (boundaryPrimitives G R) (boundaryInitialState G R) := by
  rw [source_gap_eq_at_zero_fiscal G R]
  exact hzero R hlo hhi

/-- Source-specific no-equilibrium conclusion needs only the two
literal endpoint signs and a uniform gap certificate at G=0.
The three obligations remain hypotheses here. -/
theorem noCompetitiveEquilibrium_from_zero_fiscal_reference
    (G : ℝ) (X : Allocation LocalBridgePhase)
    (hleft : ProposedBoundaryResourceRoot.boundaryResourceResidual
      (1029135 / 1000000 : ℝ) < 0)
    (hright : 0 < ProposedBoundaryResourceRoot.boundaryResourceResidual
      (1029136 / 1000000 : ℝ))
    (hzero : ∀ R : ℝ,
      (1029135 / 1000000 : ℝ) ≤ R →
      R ≤ (1029136 / 1000000 : ℝ) →
      (8 / 100 : ℝ) <
        inheritedNominalFaceGap
          (boundaryPrimitives 0 R) (boundaryInitialState 0 R)) :
    ¬ CompetitiveEquilibrium
      (boundaryPrimitives G boundarySourceRate)
      (boundaryInitialState G boundarySourceRate) X := by
  apply noCompetitiveEquilibrium_of_exact_interval_inequalities G X hleft hright
  intro R hlo hhi
  exact uniform_gap_from_zero_fiscal_reference hzero G R hlo hhi

/-- Conditional economic implication on ORIGINAL SOURCE terms.
The bank-face contribution is strictly negative throughout boundaryInterval.
If the aggregate inherited nominal gap is positive, the mass-weighted
DECLINE in firm promises must itself be strictly positive. This lemma
does not assert that the total gap is positive; that requires the still
pending exact interval-sign certificate. -/
theorem firm_face_decline_pos_of_total_gap_pos
    (G R : ℝ) (hR : R ∈ boundaryInterval)
    (hgap : 0 <
      inheritedNominalFaceGap
        (boundaryPrimitives G R) (boundaryInitialState G R)) :
    0 < ∑ i, (primitives G).mass i *
      ((inheritedState G).firmFace i -
        boundaryInheritedFace G R (boundaryZeroSeed G R) i) := by
  have hbank :
      (boundaryBankEquity R - bankEquity) /
        bankRenewalFactor (primitives G) < 0 :=
    bankFaceContribution_neg G R hR
  rw [boundaryInheritedGap_eq_face_shifts G R] at hgap
  linarith

#print axioms source_gap_eq_at_zero_fiscal
#print axioms uniform_gap_from_zero_fiscal_reference
#print axioms noCompetitiveEquilibrium_from_zero_fiscal_reference
#print axioms firm_face_decline_pos_of_total_gap_pos

end ProposedBoundaryFaceGapFiscalReduction
end Ventura26LiquidityAllocation
