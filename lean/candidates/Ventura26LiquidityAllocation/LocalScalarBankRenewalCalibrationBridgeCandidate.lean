import Ventura26LiquidityAllocation.LocalScalarBankFaceLogZeroCandidate

/-!
# Calibration compatibility for the bank renewal factor

EconomicModel.lean defines the bank renewal coefficient as
  aB_source = 1 - bankExit + bankExit * bankSeedShare.
The illustrative Python bridge defines it as
  aB_numeric = 1 / s.rate.

These coefficients are NOT definitionally equal. We prove the exact
parameter restriction required for equality and transfer the Python-
style logarithmic bank-face residual to the ORIGINAL source level row.

The restriction is an explicit premise, NOT a calibrated or verified
property of any concrete economic primitive. This theorem can be
applied to both dates zero and one because it accepts generic source
LocalPrefixDateData. The 33 other residuals and infinite competitive
equilibrium remain outside its scope.
-/

namespace Ventura26LiquidityAllocation
namespace ProposedLocalScalarBankRenewalCalibrationBridge

open ProposedLocalScalarBankFaceLogZero

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- Exact necessary AND sufficient compatibility condition for the
Illustrative inverse-loan-rate bank renewal rule. Purely algebraic:
no calibration is supplied and no positivity is silently assumed. -/
theorem bankRenewalFactor_eq_inverse_rate_iff
    (P : Primitives S) (referenceRate : ℝ) :
    bankRenewalFactor P = 1 / referenceRate ↔
      P.bankExit * (1 - P.bankSeedShare) = 1 - 1 / referenceRate := by
  constructor
  · intro h
    calc
      P.bankExit * (1 - P.bankSeedShare)
          = 1 - bankRenewalFactor P := by unfold bankRenewalFactor; ring
      _ = 1 - 1 / referenceRate := by rw [h]
  · intro h
    calc
      bankRenewalFactor P
          = 1 - P.bankExit * (1 - P.bankSeedShare) := by
            unfold bankRenewalFactor
            ring
      _ = 1 / referenceRate := by rw [h]; ring

/-- A Python-style log renewal equation using coefficient
1/referenceRate has the same zero set as the original source bank
equation if and only if the necessary coefficient identification
has been furnished, plus the positive-logarithm domain. -/
theorem source_bank_face_inverse_rate_log_zero_iff
    (P : Primitives S) (d : LocalPrefixDateData)
    (referenceRate : ℝ)
    (hcompat : P.bankExit * (1 - P.bankSeedShare) =
      1 - 1 / referenceRate)
    (hnext : 0 < d.nextBankFace)
    (hflow : 0 < (1 / referenceRate) *
      d.controls.loanRate * d.currentBankFace / d.controls.inflation) :
    Real.log
      (d.nextBankFace /
        ((1 / referenceRate) *
          d.controls.loanRate * d.currentBankFace / d.controls.inflation)) = 0 ↔
      localReducedRemainingResidual P d (0 : Fin 11) = 0 := by
  have hfactor : bankRenewalFactor P = 1 / referenceRate :=
    (bankRenewalFactor_eq_inverse_rate_iff P referenceRate).2 hcompat
  have hpositive :
      0 < bankRenewalFactor P *
        d.controls.loanRate * d.currentBankFace / d.controls.inflation := by
    simpa only [hfactor] using hflow
  simpa only [hfactor] using
    (source_bankFace_log_residual_zero_iff P d hnext hpositive)

/-- If the primitive reference rate, loan rate, bank-face level and
inflation are strictly positive, the log-flow positivity premise is
derived (not assumed separately). The compatibility of bank exit
and seed share remains explicit. -/
theorem source_bank_face_inverse_rate_log_zero_iff_of_positive
    (P : Primitives S) (d : LocalPrefixDateData)
    (referenceRate : ℝ)
    (hcompat : P.bankExit * (1 - P.bankSeedShare) =
      1 - 1 / referenceRate)
    (hreference : 0 < referenceRate)
    (hloan : 0 < d.controls.loanRate)
    (hface : 0 < d.currentBankFace)
    (hinfl : 0 < d.controls.inflation)
    (hnext : 0 < d.nextBankFace) :
    Real.log
      (d.nextBankFace /
        ((1 / referenceRate) *
          d.controls.loanRate * d.currentBankFace / d.controls.inflation)) = 0 ↔
      localReducedRemainingResidual P d (0 : Fin 11) = 0 := by
  have hflow :
      0 < (1 / referenceRate) * d.controls.loanRate *
        d.currentBankFace / d.controls.inflation := by
    exact div_pos
      (mul_pos (mul_pos (one_div_pos.mpr hreference) hloan) hface)
      hinfl
  exact source_bank_face_inverse_rate_log_zero_iff
    P d referenceRate hcompat hnext hflow

#print axioms bankRenewalFactor_eq_inverse_rate_iff
#print axioms source_bank_face_inverse_rate_log_zero_iff
#print axioms source_bank_face_inverse_rate_log_zero_iff_of_positive

end ProposedLocalScalarBankRenewalCalibrationBridge
end Ventura26LiquidityAllocation
