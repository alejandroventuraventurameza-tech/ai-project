import Ventura26LiquidityAllocation.SourcePythonStationaryStrictBufferRationalGateCandidate

/-!
# Economic positivity for stationary SOURCE bank payment exposure

The exact stationary-ratio-to-buffer proof previously required positive
shock exposure as a primitive assumption. Here it is derived from two
literal economic inequalities on the ACTUAL SOURCE allocation:
  reserve requirement < deposit rate / reserve rate,
  strictly positive bank deposits.

Under these and the genuine stationary ratio, both binary payment
settlement signs are strict. The conclusion also supplies the actual
SOURCE liquidity-marginal expectations using the installed Python
binary payment law. These remain conditional properties of a SOURCE
allocation, not an existence theorem or a validated SOURCE root.
-/

namespace Ventura26LiquidityAllocation

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- Positive bank deposits and rate-over-requirement spread certify
positive exposure in the ORIGINAL source financial state. -/
theorem sourceBankExposure_pos_of_depositRateRatio_gt_requirement
    (P : Primitives S) (X : Allocation S)
    (t : ℕ) (h : History S t)
    (hSpread :
      P.reserveRequirementPath t h <
        X.depositRate t h / X.reserveRate t h)
    (hDeposits : 0 < X.bankDeposits t h) :
    0 < sourceBankShockLiquidityExposure P X t h := by
  unfold sourceBankShockLiquidityExposure
  exact mul_pos (sub_pos.mpr hSpread) hDeposits

#print axioms sourceBankExposure_pos_of_depositRateRatio_gt_requirement

/-- Exact SOURCE bank-settlement strict branch derived from three
interpretable economic conditions, no independent sign or exposure
assumptions: ratio, rate spread, and positive deposits. -/
theorem sourceInstalledPythonLaw_stationaryRatio_spread_implies_strictSigns
    (P : Primitives S) (X : Allocation S)
    (t : ℕ) (h : History S t)
    (hRatio :
      X.reservesPrePayment t h =
        ((sourceWithConcretePythonPaymentLaw P).reserveRequirementPath t h +
          (X.depositRate t h / X.reserveRate t h -
            (sourceWithConcretePythonPaymentLaw P).reserveRequirementPath t h) /
              15) * X.bankDeposits t h)
    (hSpread :
      (sourceWithConcretePythonPaymentLaw P).reserveRequirementPath t h <
        X.depositRate t h / X.reserveRate t h)
    (hDeposits : 0 < X.bankDeposits t h) :
    localBankSettlementSurplus
      (sourceWithConcretePythonPaymentLaw P) X t h 0 < 0 ∧
    0 < localBankSettlementSurplus
      (sourceWithConcretePythonPaymentLaw P) X t h 1 := by
  exact sourceInstalledPythonLaw_stationaryRatio_implies_strictSigns
    P X t h hRatio
    (sourceBankExposure_pos_of_depositRateRatio_gt_requirement
      (sourceWithConcretePythonPaymentLaw P) X t h hSpread hDeposits)

#print axioms sourceInstalledPythonLaw_stationaryRatio_spread_implies_strictSigns

/-- The SOURCE OTC-bank expectation identities follow for this
exact strict branch, with no separate binary-law or sign premise. -/
theorem sourceInstalledPythonLaw_stationaryRatio_spread_implies_expectations
    (P : Primitives S) (X : Allocation S)
    (t : ℕ) (h : History S t)
    (hRatio :
      X.reservesPrePayment t h =
        ((sourceWithConcretePythonPaymentLaw P).reserveRequirementPath t h +
          (X.depositRate t h / X.reserveRate t h -
            (sourceWithConcretePythonPaymentLaw P).reserveRequirementPath t h) /
              15) * X.bankDeposits t h)
    (hSpread :
      (sourceWithConcretePythonPaymentLaw P).reserveRequirementPath t h <
        X.depositRate t h / X.reserveRate t h)
    (hDeposits : 0 < X.bankDeposits t h) :
    finiteSupportExpectation
      (sourceWithConcretePythonPaymentLaw P).paymentSupport
      (sourceWithConcretePythonPaymentLaw P).paymentProbability
      (localBankLiquidityMarginal
        (sourceWithConcretePythonPaymentLaw P) X t h) =
        (bankOTCDeficitSlopeAt
          (sourceWithConcretePythonPaymentLaw P) X t h
          (X.bankTightness t h) +
          bankOTCSurplusSlopeAt
            (sourceWithConcretePythonPaymentLaw P) X t h
            (X.bankTightness t h)) / 2 ∧
    finiteSupportExpectation
      (sourceWithConcretePythonPaymentLaw P).paymentSupport
      (sourceWithConcretePythonPaymentLaw P).paymentProbability
      (fun ω =>
        localBankLiquidityMarginal
          (sourceWithConcretePythonPaymentLaw P) X t h ω *
        (sourceWithConcretePythonPaymentLaw P).paymentShock ω) =
        -(1 / 5 : ℝ) *
          (bankOTCDeficitSlopeAt
            (sourceWithConcretePythonPaymentLaw P) X t h
            (X.bankTightness t h) -
            bankOTCSurplusSlopeAt
              (sourceWithConcretePythonPaymentLaw P) X t h
              (X.bankTightness t h)) / 2 := by
  obtain ⟨hminus, hplus⟩ :=
    sourceInstalledPythonLaw_stationaryRatio_spread_implies_strictSigns
      P X t h hRatio hSpread hDeposits
  exact sourceInstalledPythonLaw_strictSigns_actualBankExpectations
    P X t h hminus hplus

#print axioms sourceInstalledPythonLaw_stationaryRatio_spread_implies_expectations

end Ventura26LiquidityAllocation
