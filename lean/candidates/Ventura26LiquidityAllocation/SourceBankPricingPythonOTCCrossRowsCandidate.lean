import Ventura26LiquidityAllocation.SourceLocalPrefixOTCPythonMatchingCandidate

/-!
# SOURCE loan/deposit pricing rows in frozen-Python OTC coordinates

The original SOURCE reduced monetary rows 8 and 9 use the REALIZED
reserve rate; frozen finite_irf.py uses the policy TARGET through
auxiliary(). Exact cross-row corrections established in
SourceReserveRuleTargetSubstitutionCandidate remain necessary off root.

This file identifies the actual SOURCE OTC slopes with frozen-Python
chi_minus/chi_plus under P.matchingIntensity = log 2,
tightness <= 1. It does NOT assert numerical identity of the
full 33-row residual system, nor certify an equilibrium root.
-/

namespace Ventura26LiquidityAllocation

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- Frozen Python's OTC deficit slope cm, expressed in SOURCE date data. -/
noncomputable def sourceFrozenPythonDeficitSlope
    (d : LocalPrefixDateData) : ℝ :=
  d.corridorWidth *
    (1 - (1 / 2 : ℝ) +
      (1 / 2 : ℝ) / (1 + Real.sqrt (2 - d.controls.tightness)))

/-- Frozen Python's OTC surplus slope cp, expressed in SOURCE date data. -/
noncomputable def sourceFrozenPythonSurplusSlope
    (d : LocalPrefixDateData) : ℝ :=
  d.corridorWidth * d.controls.tightness * (1 / 2 : ℝ) /
    (1 + Real.sqrt (2 - d.controls.tightness))

/-- Exact loan-pricing correction in the original SOURCE bank row 8,
with BOTH source OTC slopes translated to Python's frozen formula. -/
theorem sourceLoanPricing_frozenPythonOTC_crossRow
    (P : Primitives S) (d : LocalPrefixDateData)
    (hmatch : P.matchingIntensity = Real.log 2)
    (htight : d.controls.tightness ≤ 1)
    (hR : 0 < d.currentReserveRate) :
    d.controls.loanRate - sourceRateRuleTarget P d -
      (sourceFrozenPythonDeficitSlope d +
        sourceFrozenPythonSurplusSlope d) / 2 =
      localReducedRemainingResidual P d (8 : Fin 11) +
        sourceRateRuleTarget P d *
          (Real.exp (localReducedRemainingResidual P d (6 : Fin 11)) - 1) := by
  have hm := sourceLocalPrefixOTC_deficitSlope_pythonFormula P d hmatch htight
  have hp := sourceLocalPrefixOTC_surplusSlope_pythonFormula P d hmatch htight
  have h := sourceLoanPricing_rateTarget_substitution P d hR
  simpa only [sourceFrozenPythonDeficitSlope,
    sourceFrozenPythonSurplusSlope, hm, hp] using h

#print axioms sourceLoanPricing_frozenPythonOTC_crossRow

/-- The original SOURCE deposit pricing correction, retaining the
finite-support mean absolute payment shock exactly rather than
assuming the Python binary zeta law without an explicit witness. -/
theorem sourceDepositPricing_frozenPythonOTC_crossRow
    (P : Primitives S) (d : LocalPrefixDateData)
    (hmatch : P.matchingIntensity = Real.log 2)
    (htight : d.controls.tightness ≤ 1)
    (hR : 0 < d.currentReserveRate) :
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
    localReducedRemainingResidual P d (9 : Fin 11) -
      sourceRateRuleTarget P d *
        (Real.exp (localReducedRemainingResidual P d (6 : Fin 11)) - 1) *
        (1 +
          d.controls.depositRate *
            localPrefixMeanAbsolutePaymentShock P *
              (sourceFrozenPythonDeficitSlope d -
                sourceFrozenPythonSurplusSlope d) /
                (2 * d.currentReserveRate *
                  sourceRateRuleTarget P d)) := by
  have hm := sourceLocalPrefixOTC_deficitSlope_pythonFormula P d hmatch htight
  have hp := sourceLocalPrefixOTC_surplusSlope_pythonFormula P d hmatch htight
  have h := sourceDepositPricing_rateTarget_substitution P d hR
  simpa only [sourceFrozenPythonDeficitSlope,
    sourceFrozenPythonSurplusSlope, hm, hp] using h

#print axioms sourceDepositPricing_frozenPythonOTC_crossRow

end Ventura26LiquidityAllocation
