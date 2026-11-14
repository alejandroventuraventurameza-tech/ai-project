import Ventura26LiquidityAllocation.SourceSixLogRowJacobianRankTransportCandidate
import Ventura26LiquidityAllocation.LocalScalarBankRenewalCalibrationBridgeCandidate
import Ventura26LiquidityAllocation.SourceFullyPinnedStationaryP0OperatorCandidate

/-!
# The bank-renewal compatibility premise is PROVED for actual SOURCE primitives

A previous SOURCE/Python log-row comparison required the explicit
calibration restriction

  bankRenewalFactor P = 1 / referenceLoanRate,

because original Python defines `s.aB := 1/s.rate` while SOURCE
defines `bankRenewalFactor P := 1-bankExit+bankExit*bankSeedShare`.

Here the SOURCE stationarity parameter construction already pins
bankExit=1/10 and bankSeedShare=10/R0 - 9. Therefore the equality is
a genuine theorem for the ACTUAL SOURCE stationary Primitives, not
an assumed parameter condition.

We then specialize the already established SOURCE bank log-vs-level
zero-set bridge to this concrete coefficient, for either date's
genuine SOURCE economic row and explicit positivity hypotheses.

This does not yet execute Python's floating-point `s.rate` in Lean,
nor prove full 33-row SOURCE/Python functional equality, root
existence, a true SOURCE interval Jacobian, or dynamic equilibrium.
-/

namespace Ventura26LiquidityAllocation

/-- Actual stationary SOURCE bank exit and seed share make its
renewal factor exactly the inverse of the stationary loan rate.
This closes the earlier abstract SOURCE/Python calibration premise
on the SOURCE side; no float64 identity is assumed. -/
theorem concreteSOURCE_bankRenewalFactor_eq_inverse_loanRate
    (G : ℝ) :
    bankRenewalFactor (ProposedStationaryPrimitives.primitives G) =
      1 / ProposedStationaryBank.loanRate := by
  exact ProposedStationaryReducedSystem.bankRenewalFactor_eq
    (ProposedStationaryPrimitives.primitives G)
    (ProposedStationaryPrimitives.stationary_parameters G)

#print axioms concreteSOURCE_bankRenewalFactor_eq_inverse_loanRate

/-- A Python-shaped log rollover using 1/R0 has exactly the same
positive-domain zeros as the ORIGINAL SOURCE date-row rollover
for concrete stationary SOURCE Primitives, with no assumed
bank-entry calibration compatibility condition. -/
theorem concreteSOURCE_bankFaceLog_zero_iff_original_row
    (G : ℝ) (d : LocalPrefixDateData)
    (hnext : 0 < d.nextBankFace)
    (hloan : 0 < d.controls.loanRate)
    (hface : 0 < d.currentBankFace)
    (hinfl : 0 < d.controls.inflation) :
    Real.log (d.nextBankFace /
      ((1 / ProposedStationaryBank.loanRate) *
        d.controls.loanRate * d.currentBankFace /
        d.controls.inflation)) = 0 ↔
    localReducedRemainingResidual
      (ProposedStationaryPrimitives.primitives G) d (0 : Fin 11) = 0 := by
  have hfactor :=
    concreteSOURCE_bankRenewalFactor_eq_inverse_loanRate G
  have hcompat :
      (ProposedStationaryPrimitives.primitives G).bankExit *
        (1 - (ProposedStationaryPrimitives.primitives G).bankSeedShare) =
        1 - 1 / ProposedStationaryBank.loanRate :=
    (ProposedLocalScalarBankRenewalCalibrationBridge.bankRenewalFactor_eq_inverse_rate_iff
      (ProposedStationaryPrimitives.primitives G)
      ProposedStationaryBank.loanRate).mp hfactor
  exact
    ProposedLocalScalarBankRenewalCalibrationBridge.source_bank_face_inverse_rate_log_zero_iff_of_positive
      (ProposedStationaryPrimitives.primitives G) d
      ProposedStationaryBank.loanRate hcompat
      ProposedStationaryRealScale.loanRate_pos
      hloan hface hinfl hnext

#print axioms concreteSOURCE_bankFaceLog_zero_iff_original_row

/-- Actual SOURCE worker/labor numerical coefficients are pinned
exactly to the rational versions of Python's illustrative
`bw=.99`, `sigmaW=1`, `chiW=1`, `varphi=1`.
This is parameter correspondence, NOT equality of endogenous
worker consumption, labor aggregation or residual functions. -/
theorem concreteSOURCE_workerLabor_parameters (G : ℝ) :
    (ProposedStationaryPrimitives.primitives G).workerDiscount = 99 / 100 ∧
    (ProposedStationaryPrimitives.primitives G).workerRiskAversion = 1 ∧
    (ProposedStationaryPrimitives.primitives G).laborScale = 1 ∧
    (ProposedStationaryPrimitives.primitives G).laborCurvature = 1 := by
  exact ⟨rfl, rfl, rfl, rfl⟩

#print axioms concreteSOURCE_workerLabor_parameters

end Ventura26LiquidityAllocation
