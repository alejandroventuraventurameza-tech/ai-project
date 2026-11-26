import Ventura26LiquidityAllocation.LocalScalarBankRenewalCalibrationBridgeCandidate
import Ventura26LiquidityAllocation.LocalScalarAugmented34PolicyRecenterCandidate

/-!
# Original augmented bank renewal rows at dates zero and one

Python finite_bridge.py writes a log of the ratio of future nominal bank
face to an illustrative renewal flow with coefficient aB = 1/s.rate.
The original EconomicModel.lean operator writes a LEVEL residual with
coefficient bankRenewalFactor P = 1 - bankExit + bankExit*bankSeedShare.

This file connects the actual augmented source rows 6 and 22 to the
source-consistent log-ratio ZERO sets, conditional on the explicit
parameter compatibility and strict positivity at both dates.

No Jacobian equality is asserted: differentiating log ratios is not the
same as differentiating the underlying level residual. The concrete
Python rate, arrays, tail and interval boxes remain unverified against
the source primitives.
-/

namespace Ventura26LiquidityAllocation
namespace ProposedLocalScalarAugmented34BankFaceRows

open ProposedLocalScalarBankRenewalCalibrationBridge
open ProposedLocalScalarAugmented34Source
open ProposedLocalScalarAugmented34PolicyRecenter

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- A reserve-remuneration innovation cannot silently repair or
invalidate the BANK RENEWAL calibration: this parameter restriction
depends only on the bank exit fraction and its retained seed share. -/
theorem bank_renewal_compatibility_preserved
    (P : Primitives S) (referenceRate h : ℝ)
    (hcompat : P.bankExit * (1 - P.bankSeedShare) =
      1 - 1 / referenceRate) :
    (reserveRemunerationShiftedPrimitives P h).bankExit *
      (1 - (reserveRemunerationShiftedPrimitives P h).bankSeedShare) =
      1 - 1 / referenceRate := by
  simpa only [reserveRemunerationShiftedPrimitives,
    initialIntervenedPrimitives] using hcompat

/-- The literal bank-renewal rows 6 and 22 in the 34-dimensional
augmented SOURCE system have precisely the same zero sets as the
illustrative logarithmic bank-flow ratios, once the external aB
calibration has actually been identified with source primitives.
No unidentified premise is hidden behind definitional equality. -/
theorem augmented_bank_face_rows_log_zero_iff
    (P : Primitives S) (I : InheritedState)
    (Z0 : LocalPrefixCoordinates) (dateOne recurrent : S)
    (tail : LocalPrefixContinuationRule)
    (z : Fin 33 → ℝ) (h referenceRate : ℝ)
    (hcompat : P.bankExit * (1 - P.bankSeedShare) =
      1 - 1 / referenceRate)
    (hnext0 : 0 <
      (localPrefixDateZeroData (reserveRemunerationShiftedPrimitives P h)
        I (localPrefixLogChart Z0 z) dateOne).nextBankFace)
    (hflow0 : 0 < (1 / referenceRate) *
      (localPrefixDateZeroData (reserveRemunerationShiftedPrimitives P h)
        I (localPrefixLogChart Z0 z) dateOne).controls.loanRate *
      (localPrefixDateZeroData (reserveRemunerationShiftedPrimitives P h)
        I (localPrefixLogChart Z0 z) dateOne).currentBankFace /
      (localPrefixDateZeroData (reserveRemunerationShiftedPrimitives P h)
        I (localPrefixLogChart Z0 z) dateOne).controls.inflation)
    (hnext1 : 0 <
      (localPrefixDateOneData (reserveRemunerationShiftedPrimitives P h)
        (localPrefixLogChart Z0 z) dateOne recurrent tail).nextBankFace)
    (hflow1 : 0 < (1 / referenceRate) *
      (localPrefixDateOneData (reserveRemunerationShiftedPrimitives P h)
        (localPrefixLogChart Z0 z) dateOne recurrent tail).controls.loanRate *
      (localPrefixDateOneData (reserveRemunerationShiftedPrimitives P h)
        (localPrefixLogChart Z0 z) dateOne recurrent tail).currentBankFace /
      (localPrefixDateOneData (reserveRemunerationShiftedPrimitives P h)
        (localPrefixLogChart Z0 z) dateOne recurrent tail).controls.inflation) :
    let Pv := reserveRemunerationShiftedPrimitives P h
    let Z := localPrefixLogChart Z0 z
    let d0 := localPrefixDateZeroData Pv I Z dateOne
    let d1 := localPrefixDateOneData Pv Z dateOne recurrent tail
    (Real.log (d0.nextBankFace /
      ((1 / referenceRate) * d0.controls.loanRate *
        d0.currentBankFace / d0.controls.inflation)) = 0 ↔
      (augmentedBoundaryZeroResidual
        P I Z0 dateOne recurrent tail z h).1 (6 : Fin 33) = 0) ∧
    (Real.log (d1.nextBankFace /
      ((1 / referenceRate) * d1.controls.loanRate *
        d1.currentBankFace / d1.controls.inflation)) = 0 ↔
      (augmentedBoundaryZeroResidual
        P I Z0 dateOne recurrent tail z h).1 (22 : Fin 33) = 0) := by
  let Pv := reserveRemunerationShiftedPrimitives P h
  let Z := localPrefixLogChart Z0 z
  let d0 := localPrefixDateZeroData Pv I Z dateOne
  let d1 := localPrefixDateOneData Pv Z dateOne recurrent tail
  have hc : Pv.bankExit * (1 - Pv.bankSeedShare) =
      1 - 1 / referenceRate :=
    bank_renewal_compatibility_preserved P referenceRate h hcompat
  have h0 := source_bank_face_inverse_rate_log_zero_iff
    Pv d0 referenceRate hc hnext0 hflow0
  have h1 := source_bank_face_inverse_rate_log_zero_iff
    Pv d1 referenceRate hc hnext1 hflow1
  constructor
  · change Real.log (d0.nextBankFace /
      ((1 / referenceRate) * d0.controls.loanRate *
        d0.currentBankFace / d0.controls.inflation)) = 0 ↔
        localReducedRemainingResidual Pv d0 (0 : Fin 11) = 0
    exact h0
  · change Real.log (d1.nextBankFace /
      ((1 / referenceRate) * d1.controls.loanRate *
        d1.currentBankFace / d1.controls.inflation)) = 0 ↔
        localReducedRemainingResidual Pv d1 (0 : Fin 11) = 0
    exact h1

#print axioms bank_renewal_compatibility_preserved
#print axioms augmented_bank_face_rows_log_zero_iff

end ProposedLocalScalarAugmented34BankFaceRows
end Ventura26LiquidityAllocation
