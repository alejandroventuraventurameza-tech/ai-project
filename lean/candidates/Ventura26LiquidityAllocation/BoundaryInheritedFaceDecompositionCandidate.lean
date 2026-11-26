import Ventura26LiquidityAllocation.BoundaryFrozenInheritanceCandidate

/-!
# Algebraic decomposition of inherited nominal-face incompatibility

The former SOURCE boundary carrier changed inherited firm faces and bank
face in order to close its impact budgets. Its initial aggregate face gap
equals the sum of precisely those predated claim changes, relative to the
certified stationary inherited state.

This is an EXACT identity over original SOURCE objects, with no rounding,
and not yet a sign proof. It complements the rational-interval NUMERICO
certificate; Lean must still establish its strict bound at the named root.
-/

namespace Ventura26LiquidityAllocation
namespace ProposedBoundaryInheritedFaceDecomposition

open ProposedStationaryPrimitives
open ProposedStationaryInheritedState
open ProposedStationaryRealScale
open ProposedBoundaryResourceRoot
open ProposedBoundaryBridge
open ProposedBoundaryNormalizationBridge
open ProposedBoundaryFullPrefix
open ProposedBoundaryInheritedFaceGate

/-- Arbitrary changes in two inherited nominal face fields alter the
initial accounting gap only by the mass-weighted firm claims and the
bank's renewal-adjusted inherited face. All other positions are fixed. -/
theorem inheritedNominalFaceGap_firm_bank_update
    (P : Primitives LocalBridgePhase) (I : InheritedState)
    (newFirmFace : FirmType → ℝ) (newBankFace : ℝ) :
    inheritedNominalFaceGap P
        { I with firmFace := newFirmFace, bankFace := newBankFace } =
      inheritedNominalFaceGap P I +
      (∑ i, P.mass i * (I.firmFace i - newFirmFace i)) +
      (newBankFace - I.bankFace) / bankRenewalFactor P := by
  unfold inheritedNominalFaceGap
  simp only [sum_firmType_eq_H_add_L]
  ring

/-- Policy surprises never alter this inherited accounting gap, provided
the predecessor balance sheet is genuinely held fixed. -/
theorem inheritedNominalFaceGap_initialIntervention_invariant
    (P : Primitives LocalBridgePhase) (I : InheritedState)
    (v : InitialPolicyIntervention) :
    inheritedNominalFaceGap (initialIntervenedPrimitives P v) I =
      inheritedNominalFaceGap P I := by
  rfl

/-- The old SOURCE initial state differs from the stationary parent
only in the installed capital, two inherited firm promises, and bank face.
The previous reserve lag fields were restated, but not changed. -/
theorem boundaryInitialState_unchanged_fields (G R : ℝ) :
    boundaryInitialState G R =
      { inheritedState G with
        capital := boundaryCapital R
        firmFace := boundaryInheritedFace G R (boundaryZeroSeed G R)
        bankFace := boundaryBankEquity R } := by
  rfl

/-- For every date-zero rate R (not only the root), the original SOURCE
nominal gap is exactly the change in predated nominal claims relative to
the genuinely consistent stationary predecessor. Government bond
positions and G cancel, as do the unchanged deposit/reserve/facility
positions. This identity alone does NOT show a positive or negative gap. -/
theorem boundaryInheritedGap_eq_face_shifts (G R : ℝ) :
    inheritedNominalFaceGap
        (boundaryPrimitives G R) (boundaryInitialState G R) =
      (∑ i, (primitives G).mass i *
        ((inheritedState G).firmFace i -
          boundaryInheritedFace G R (boundaryZeroSeed G R) i)) +
        (boundaryBankEquity R - bankEquity) /
          bankRenewalFactor (primitives G) := by
  have hstationary :=
    (inheritedNominalFaceConsistency_iff_gap_zero
      (primitives G) (inheritedState G)
      (inherited_nominalFaceConsistency G).1).mp
      (inherited_nominalFaceConsistency G)
  have hsame :
      inheritedNominalFaceGap
        (boundaryPrimitives G R) (inheritedState G) =
          inheritedNominalFaceGap (primitives G) (inheritedState G) := by
    rfl
  have hstate :
      inheritedNominalFaceGap
        (boundaryPrimitives G R) (boundaryInitialState G R) =
      inheritedNominalFaceGap
        (boundaryPrimitives G R)
        { inheritedState G with
          firmFace := boundaryInheritedFace G R (boundaryZeroSeed G R)
          bankFace := boundaryBankEquity R } := by
    rfl
  rw [hstate, inheritedNominalFaceGap_firm_bank_update]
  rw [hsame, hstationary]
  change (0 : ℝ) +
      (∑ i, (primitives G).mass i *
        ((inheritedState G).firmFace i -
          boundaryInheritedFace G R (boundaryZeroSeed G R) i)) +
      (boundaryBankEquity R - bankEquity) /
        bankRenewalFactor (primitives G) =
      (∑ i, (primitives G).mass i *
        ((inheritedState G).firmFace i -
          boundaryInheritedFace G R (boundaryZeroSeed G R) i)) +
      (boundaryBankEquity R - bankEquity) /
        bankRenewalFactor (primitives G)
  ring

/-- At the named SOURCE root, the decomposition holds for each symbolic
fiscal-bond supply G. No assumption that it vanishes is smuggled in. -/
theorem sourceBoundaryInheritedGap_eq_face_shifts (G : ℝ) :
    sourceBoundaryInheritedNominalFaceGap G =
      (∑ i, (primitives G).mass i *
        ((inheritedState G).firmFace i -
          boundaryInheritedFace G boundarySourceRate
            (boundaryZeroSeed G boundarySourceRate) i)) +
      (boundaryBankEquity boundarySourceRate - bankEquity) /
        bankRenewalFactor (primitives G) := by
  exact boundaryInheritedGap_eq_face_shifts G boundarySourceRate

#print axioms inheritedNominalFaceGap_firm_bank_update
#print axioms inheritedNominalFaceGap_initialIntervention_invariant
#print axioms boundaryInitialState_unchanged_fields
#print axioms boundaryInheritedGap_eq_face_shifts
#print axioms sourceBoundaryInheritedGap_eq_face_shifts

end ProposedBoundaryInheritedFaceDecomposition
end Ventura26LiquidityAllocation
