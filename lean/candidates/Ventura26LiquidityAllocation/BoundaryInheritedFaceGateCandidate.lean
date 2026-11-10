import Ventura26LiquidityAllocation.BoundaryFullFirmBudgetCandidate

/-!
# Exact inherited nominal-face gap at the SOURCE boundary

The 33 reduced rows, even when realized by an all-date Allocation, do
not include InheritedNominalFaceConsistency. We isolate its exact
necessary and sufficient scalar equality under a positive renewal factor.

A reproducible *numerical*, not Lean, audit suggests the named SOURCE
root leaves a +0.08291496457 residual. This file DOES NOT prove that
number or its sign. The obstruction theorem is conditional on a
future exact nonzero certificate.
-/

namespace Ventura26LiquidityAllocation
namespace ProposedBoundaryInheritedFaceGate

open ProposedStationaryReducedSystem
open ProposedBoundaryFullPrefix
open ProposedBoundaryNormalizationBridge

noncomputable def inheritedNominalFaceGap
    (P : Primitives LocalBridgePhase) (I : InheritedState) : ℝ :=
  I.depositRateLag * I.householdDeposits -
    (∑ i, P.mass i * I.firmFace i) -
    I.reserveRateLag * I.reservesLag +
    I.facilityRateLag * I.facilityBorrowingLag +
    I.bankFace / bankRenewalFactor P

theorem inheritedNominalFaceConsistency_iff_gap_zero
    (P : Primitives LocalBridgePhase) (I : InheritedState)
    (hpositive : 0 < bankRenewalFactor P) :
    InheritedNominalFaceConsistency P I ↔
      inheritedNominalFaceGap P I = 0 := by
  constructor
  · intro h
    rcases h with ⟨_hfactor, heq⟩
    unfold inheritedNominalFaceGap
    linarith
  · intro hgap
    constructor
    · exact hpositive
    · unfold inheritedNominalFaceGap at hgap
      linarith

noncomputable def sourceBoundaryInheritedNominalFaceGap (G : ℝ) : ℝ :=
  inheritedNominalFaceGap
    (boundaryPrimitives G boundarySourceRate)
    (boundaryInitialState G boundarySourceRate)

/-- Exact bridge, not a proof of the zero on its right-hand side. -/
theorem sourceBoundaryInheritedFaceConsistency_iff_gap_zero (G : ℝ) :
    InheritedNominalFaceConsistency
      (boundaryPrimitives G boundarySourceRate)
      (boundaryInitialState G boundarySourceRate) ↔
    sourceBoundaryInheritedNominalFaceGap G = 0 := by
  have hfactor : 0 < bankRenewalFactor
      (boundaryPrimitives G boundarySourceRate) :=
    lt_trans (by norm_num)
      (bankRenewalFactor_bounds
        (boundaryPrimitives G boundarySourceRate)
        (boundary_stationary_parameters G boundarySourceRate)).1
  change InheritedNominalFaceConsistency
    (boundaryPrimitives G boundarySourceRate)
    (boundaryInitialState G boundarySourceRate) ↔
    inheritedNominalFaceGap
      (boundaryPrimitives G boundarySourceRate)
      (boundaryInitialState G boundarySourceRate) = 0
  exact inheritedNominalFaceConsistency_iff_gap_zero
    (boundaryPrimitives G boundarySourceRate)
    (boundaryInitialState G boundarySourceRate) hfactor

/-- Conditional obstruction. hgap remains a PENDING exact obligation. -/
theorem sourceBoundary_inheritedFace_invalid_of_gap_ne_zero
    (G : ℝ)
    (hgap : sourceBoundaryInheritedNominalFaceGap G ≠ 0) :
    ¬ InheritedNominalFaceConsistency
      (boundaryPrimitives G boundarySourceRate)
      (boundaryInitialState G boundarySourceRate) := by
  intro h
  exact hgap ((sourceBoundaryInheritedFaceConsistency_iff_gap_zero G).mp h)

/-- If the exact SOURCE inherited-face gap is nonzero, *no* Allocation
over the unchanged SOURCE primitives and inherited positions can satisfy
the full original competitive equilibrium definition. In particular this
does not merely rule out the explicitly constructed candidate.
The hypothesis hgap requires a separate exact proof. -/
theorem sourceBoundary_noCompetitiveEquilibrium_of_gap_ne_zero
    (G : ℝ) (X : Allocation LocalBridgePhase)
    (hgap : sourceBoundaryInheritedNominalFaceGap G ≠ 0) :
    ¬ CompetitiveEquilibrium
      (boundaryPrimitives G boundarySourceRate)
      (boundaryInitialState G boundarySourceRate) X := by
  intro hCE
  rcases hCE with ⟨_hdomain, _hpositive, _hpolicy, _hfirms,
    _hhousehold, _hpopulation, _hretail, _hcapitalOptimal,
    _hfirmBudgets, _hhouseholdBudget, hinheritedFaces, _hrest⟩
  exact hgap ((sourceBoundaryInheritedFaceConsistency_iff_gap_zero G).mp
    hinheritedFaces)

#print axioms inheritedNominalFaceConsistency_iff_gap_zero
#print axioms sourceBoundaryInheritedFaceConsistency_iff_gap_zero
#print axioms sourceBoundary_inheritedFace_invalid_of_gap_ne_zero
#print axioms sourceBoundary_noCompetitiveEquilibrium_of_gap_ne_zero

end ProposedBoundaryInheritedFaceGate
end Ventura26LiquidityAllocation
