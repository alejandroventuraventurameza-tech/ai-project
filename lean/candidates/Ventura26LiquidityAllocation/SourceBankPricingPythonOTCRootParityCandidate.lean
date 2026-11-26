import Ventura26LiquidityAllocation.SourceBankPricingPythonOTCCrossRowsCandidate

/-!
# Exact monetary-rule-root parity for the three SOURCE banking rows

Conditional on the two ORIGINAL SOURCE monetary policy residuals
vanishing and a low-tightness log-two matching calibration, the
frozen-Python-style target-rate loan and deposit pricing expressions
coincide with the ORIGINAL SOURCE realized-rate residuals.
The two-target banking balance equality was already proved in
SourceEconomicBankPolicyRootParityCandidate.

This proves a CONDITIONAL economic row-value bridge only. It does
not identify the rest of frozen finite_irf.py with SOURCE: the
payment law and persistence parameters, log chart, branch, full
33-row formulas and finite-tail rule still require checks.
-/

namespace Ventura26LiquidityAllocation

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- When the SOURCE reserve-rate rule is satisfied, the Python-style
target loan-price expression is the exact SOURCE loan-price row. -/
theorem sourceLoanPricing_pythonOTC_eq_at_monetaryRoot
    (P : Primitives S) (d : LocalPrefixDateData)
    (hmatch : P.matchingIntensity = Real.log 2)
    (htight : d.controls.tightness ≤ 1)
    (hR : 0 < d.currentReserveRate)
    (hRowR : localReducedRemainingResidual P d (6 : Fin 11) = 0) :
    d.controls.loanRate - sourceRateRuleTarget P d -
      (sourceFrozenPythonDeficitSlope d +
        sourceFrozenPythonSurplusSlope d) / 2 =
      localReducedRemainingResidual P d (8 : Fin 11) := by
  have h := sourceLoanPricing_frozenPythonOTC_crossRow
    P d hmatch htight hR
  rw [hRowR] at h
  simpa using h

#print axioms sourceLoanPricing_pythonOTC_eq_at_monetaryRoot

/-- Under the same monetary root, the target-rate SOURCE deposit
row with Python OTC matching components equals the realized row. -/
theorem sourceDepositPricing_pythonOTC_eq_at_monetaryRoot
    (P : Primitives S) (d : LocalPrefixDateData)
    (hmatch : P.matchingIntensity = Real.log 2)
    (htight : d.controls.tightness ≤ 1)
    (hR : 0 < d.currentReserveRate)
    (hRowR : localReducedRemainingResidual P d (6 : Fin 11) = 0) :
    sourceRateRuleTarget P d +
      (1 - d.reserveRequirement) *
        (sourceFrozenPythonDeficitSlope d +
          sourceFrozenPythonSurplusSlope d) / 2 -
      (d.controls.depositRate / sourceRateRuleTarget P d -
        d.reserveRequirement) *
        localPrefixMeanAbsolutePaymentShock P *
          (sourceFrozenPythonDeficitSlope d -
            sourceFrozenPythonSurplusSlope d) / 2 -
      d.controls.depositRate =
      localReducedRemainingResidual P d (9 : Fin 11) := by
  have h := sourceDepositPricing_frozenPythonOTC_crossRow
    P d hmatch htight hR
  rw [hRowR] at h
  simpa using h

#print axioms sourceDepositPricing_pythonOTC_eq_at_monetaryRoot

end Ventura26LiquidityAllocation
