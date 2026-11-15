import Ventura26LiquidityAllocation.SourceInstalledPythonBankStrictSignsExpectationsCandidate

/-!
# Original SOURCE strict bank settlement signs from a reserve-buffer bound

For the genuine installed two-atom SOURCE payment law with shock
magnitudes +/-1/5, define:
  b = reservesPre - reserveRequirement * bankDeposits
  c = (depositRate/reserveRate - reserveRequirement) * bankDeposits.

The economically transparent condition -c/5 < b < c/5
suffices for the negative-shock atom to have negative settlement
surplus and the positive-shock atom to have strictly positive
settlement surplus. It implies c>0. At this point the genuine
SOURCE bank liquidity expectations simplify to the calibrated OTC
slopes by the previous certified binary expectation lemma.

Crucially the reserve-buffer bound is a HYPOTHESIS about an economic
allocation, NOT an assertion that a computed root satisfies it.
An independently validated root/interval enclosure is required
to discharge this last sign-regime obligation in the Python economy.
-/

namespace Ventura26LiquidityAllocation

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- Original economic pre-settlement reserve buffer. -/
noncomputable def sourceBankPreSettlementBuffer
    (P : Primitives S) (X : Allocation S)
    (t : ℕ) (h : History S t) : ℝ :=
  X.reservesPrePayment t h -
    P.reserveRequirementPath t h * X.bankDeposits t h

/-- Shock-dependent liquidity exposure before OTC clearing. -/
noncomputable def sourceBankShockLiquidityExposure
    (P : Primitives S) (X : Allocation S)
    (t : ℕ) (h : History S t) : ℝ :=
  (X.depositRate t h / X.reserveRate t h -
    P.reserveRequirementPath t h) * X.bankDeposits t h

/-- The exact strict two-atom settlement regime is implied by a
reserve-buffer interval with the concrete Python zeta=1/5.
No numerical inequalities are asserted; the bounds must be proven
at the eventual economic root. -/
theorem sourceInstalledPythonLaw_buffer_implies_strictSigns
    (P : Primitives S) (X : Allocation S)
    (t : ℕ) (h : History S t)
    (hbuffer :
      -(sourceBankShockLiquidityExposure
          (sourceWithConcretePythonPaymentLaw P) X t h / 5) <
        sourceBankPreSettlementBuffer
          (sourceWithConcretePythonPaymentLaw P) X t h ∧
      sourceBankPreSettlementBuffer
        (sourceWithConcretePythonPaymentLaw P) X t h <
        sourceBankShockLiquidityExposure
          (sourceWithConcretePythonPaymentLaw P) X t h / 5) :
    localBankSettlementSurplus
      (sourceWithConcretePythonPaymentLaw P) X t h 0 < 0 ∧
    0 < localBankSettlementSurplus
      (sourceWithConcretePythonPaymentLaw P) X t h 1 := by
  have hshock0 :
      (sourceWithConcretePythonPaymentLaw P).paymentShock 0 =
        -(1 / 5 : ℝ) := by
    rfl
  have hshock1 :
      (sourceWithConcretePythonPaymentLaw P).paymentShock 1 =
        (1 / 5 : ℝ) := by
    rfl
  constructor
  · simp only [localBankSettlementSurplus, bankSettlementSurplus,
      hshock0, sourceBankShockLiquidityExposure,
      sourceBankPreSettlementBuffer] at *
    nlinarith [hbuffer.2]
  · simp only [localBankSettlementSurplus, bankSettlementSurplus,
      hshock1, sourceBankShockLiquidityExposure,
      sourceBankPreSettlementBuffer] at *
    nlinarith [hbuffer.1]

#print axioms sourceInstalledPythonLaw_buffer_implies_strictSigns

end Ventura26LiquidityAllocation
