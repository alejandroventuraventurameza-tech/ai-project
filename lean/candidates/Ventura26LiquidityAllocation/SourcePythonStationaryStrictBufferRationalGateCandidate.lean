import Ventura26LiquidityAllocation.SourceInstalledPythonBankStrictBufferCandidate

/-!
# Exact rational stationary buffer gate for the genuine SOURCE allocation

For the frozen Python values zeta=1/5 and tightness=1/2, the
payment-matching factor is zeta*(1-tight)/(1+tight)=1/15.
Consequently, if actual SOURCE pre-settlement reserves satisfy
  reservesPre = (rho + (rd/rr-rho)/15) * deposits,
the pre-settlement buffer b equals the shock exposure c divided
by 15. For strictly positive shock exposure, the branch bounds
-c/5 < b < c/5 are an EXACT rational implication, with no floating
point error.

This is conditional on the genuine SOURCE reserve/deposit ratio
identity and strictly positive exposure. It does not claim those
conditions for an instantiated SOURCE calibration. The separate
Python numerical audit has established positive margins at its
frozen stationary seed, but that is NOT a Lean interval certificate.
-/

namespace Ventura26LiquidityAllocation

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- Under the analytical stationary ratio with exact frozen
matching factor 1/15 and positive liquidity exposure, the original
SOURCE reserve buffer belongs strictly to the interval required
for the two distinct bank payment signs. -/
theorem sourcePythonStationaryRatio_implies_strictBuffer
    (P : Primitives S) (X : Allocation S)
    (t : ℕ) (h : History S t)
    (hRatio :
      X.reservesPrePayment t h =
        (P.reserveRequirementPath t h +
          (X.depositRate t h / X.reserveRate t h -
            P.reserveRequirementPath t h) / 15) *
          X.bankDeposits t h)
    (hExposure :
      0 < sourceBankShockLiquidityExposure P X t h) :
    -(sourceBankShockLiquidityExposure P X t h / 5) <
      sourceBankPreSettlementBuffer P X t h ∧
    sourceBankPreSettlementBuffer P X t h <
      sourceBankShockLiquidityExposure P X t h / 5 := by
  have hbuffer :
      sourceBankPreSettlementBuffer P X t h =
        sourceBankShockLiquidityExposure P X t h / 15 := by
    unfold sourceBankPreSettlementBuffer sourceBankShockLiquidityExposure
    rw [hRatio]
    ring
  rw [hbuffer]
  constructor <;> linarith

#print axioms sourcePythonStationaryRatio_implies_strictBuffer

/-- Specialize the analytical ratio gate to the explicitly installed
admissible Python two-point payment law on real SOURCE objects. -/
theorem sourceInstalledPythonLaw_stationaryRatio_implies_strictSigns
    (P : Primitives S) (X : Allocation S)
    (t : ℕ) (h : History S t)
    (hRatio :
      X.reservesPrePayment t h =
        ((sourceWithConcretePythonPaymentLaw P).reserveRequirementPath t h +
          (X.depositRate t h / X.reserveRate t h -
            (sourceWithConcretePythonPaymentLaw P).reserveRequirementPath t h) /
              15) * X.bankDeposits t h)
    (hExposure :
      0 < sourceBankShockLiquidityExposure
        (sourceWithConcretePythonPaymentLaw P) X t h) :
    localBankSettlementSurplus
      (sourceWithConcretePythonPaymentLaw P) X t h 0 < 0 ∧
    0 < localBankSettlementSurplus
      (sourceWithConcretePythonPaymentLaw P) X t h 1 := by
  apply sourceInstalledPythonLaw_buffer_implies_strictSigns P X t h
  exact sourcePythonStationaryRatio_implies_strictBuffer
    (sourceWithConcretePythonPaymentLaw P) X t h hRatio hExposure

#print axioms sourceInstalledPythonLaw_stationaryRatio_implies_strictSigns

end Ventura26LiquidityAllocation
