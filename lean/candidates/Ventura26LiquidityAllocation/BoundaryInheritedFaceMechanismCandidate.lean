import Ventura26LiquidityAllocation.BoundaryInheritedFaceDecompositionCandidate

/-!
# Exact inherited-face mechanism: public debt invariance and bank contribution

The SOURCE initial-face mismatch is algebraically independent of G:
G appears only in the public-bond holdings that cancel from the source
inherited-face identity. Independently, the old SOURCE constructor
reduces the inherited bank face for every rate on its certified root
interval, since the SOURCE loan rate exceeds the parent bank loan rate.

None of these strict-sign facts by itself proves the total inherited-face
gap nonzero; the separate firm-face variation must also be bounded.
-/

namespace Ventura26LiquidityAllocation
namespace ProposedBoundaryInheritedFaceMechanism

open ProposedStationaryBank
open ProposedStationaryPrimitives
open ProposedStationaryInheritedState
open ProposedStationaryRealScale
open ProposedBoundaryResourceRoot
open ProposedBoundaryBridge
open ProposedBoundaryFullPrefix
open ProposedBoundaryNormalizationBridge
open ProposedBoundaryInheritedFaceGate
open ProposedBoundaryInheritedFaceDecomposition

/-- The initial SOURCE firm-face reconstruction ignores the fiscal bond
supply G: the firm profit inputs, wages, capital and financing choice all
belong to a common real/financial baseline. -/
theorem boundaryInheritedFace_independent_of_G
    (G H R : ℝ) (i : FirmType) :
    boundaryInheritedFace G R (boundaryZeroSeed G R) i =
      boundaryInheritedFace H R (boundaryZeroSeed H R) i := by
  rfl

/-- The original SOURCE initial-face gap does not vary with public-bond
supply G. It cannot be fixed by choosing a convenient G. -/
theorem boundaryInheritedGap_independent_of_G
    (G H R : ℝ) :
    inheritedNominalFaceGap (boundaryPrimitives G R) (boundaryInitialState G R) =
      inheritedNominalFaceGap (boundaryPrimitives H R) (boundaryInitialState H R) := by
  rw [boundaryInheritedGap_eq_face_shifts G R,
      boundaryInheritedGap_eq_face_shifts H R]
  rfl

/-- The same independence holds at the certified source scalar root. -/
theorem sourceBoundaryInheritedGap_independent_of_G
    (G H : ℝ) :
    sourceBoundaryInheritedNominalFaceGap G =
      sourceBoundaryInheritedNominalFaceGap H := by
  exact boundaryInheritedGap_independent_of_G G H boundarySourceRate

/-- Throughout the SOURCE boundary interval, the impact loan rate is
strictly higher than the parent stationary bank gross loan rate. -/
theorem stationaryLoanRate_lt_boundaryRate
    (R : ℝ) (hR : R ∈ boundaryInterval) :
    ProposedStationaryBank.loanRate < R := by
  have hparent :
      ProposedStationaryBank.loanRate <
        (101204827 / 100000000 : ℝ) :=
    boundary_source_loan_rate_micro_box.2
  have hgap :
      (101204827 / 100000000 : ℝ) < boundaryLo := by
    norm_num [boundaryLo]
  exact lt_of_lt_of_le (lt_trans hparent hgap) hR.1

/-- Hence the old SOURCE initial bank face is strictly BELOW the
stationary predecessor's bank face: it is not the same inherited stock. -/
theorem boundaryBankFace_lt_stationary
    (R : ℝ) (hR : R ∈ boundaryInterval) :
    boundaryBankEquity R < bankEquity := by
  have hRpos : 0 < R := (boundary_rate_domain hR).1
  have hloan := stationaryLoanRate_lt_boundaryRate R hR
  change bankEquity * ProposedStationaryBank.loanRate / R < bankEquity
  exact (div_lt_iff₀ hRpos).2
    (mul_lt_mul_of_pos_left hloan bank_scale_pos.1)

/-- Consequently the bank-face change contributes NEGATIVELY to the
overall inherited nominal gap, for any public-bond supply G. -/
theorem bankFaceContribution_neg
    (G R : ℝ) (hR : R ∈ boundaryInterval) :
    (boundaryBankEquity R - bankEquity) /
      bankRenewalFactor (primitives G) < 0 := by
  have hface : boundaryBankEquity R - bankEquity < 0 :=
    sub_neg.mpr (boundaryBankFace_lt_stationary R hR)
  have hrenewal : 0 < bankRenewalFactor (primitives G) :=
    (inherited_nominalFaceConsistency G).1
  exact div_neg_of_neg_of_pos hface hrenewal

/-- This sign applies to the named SOURCE rate from the original scalar
resource root and is independent of all household tax adjustments. -/
theorem sourceBankFaceContribution_neg (G : ℝ) :
    (boundaryBankEquity boundarySourceRate - bankEquity) /
      bankRenewalFactor (primitives G) < 0 := by
  exact bankFaceContribution_neg G boundarySourceRate
    ⟨boundarySourceRate_spec.1, boundarySourceRate_spec.2.1⟩

#print axioms boundaryInheritedFace_independent_of_G
#print axioms boundaryInheritedGap_independent_of_G
#print axioms sourceBoundaryInheritedGap_independent_of_G
#print axioms stationaryLoanRate_lt_boundaryRate
#print axioms boundaryBankFace_lt_stationary
#print axioms bankFaceContribution_neg
#print axioms sourceBankFaceContribution_neg

end ProposedBoundaryInheritedFaceMechanism
end Ventura26LiquidityAllocation
