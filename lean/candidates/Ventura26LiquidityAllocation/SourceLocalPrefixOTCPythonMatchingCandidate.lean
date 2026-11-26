import Ventura26LiquidityAllocation.SourceOTCLogTwoPythonCalibrationCandidate

/-!
# SOURCE local-prefix OTC slopes: exact frozen-Python formulas

Strengthens the algebraic log-two matching identities to the ACTUAL
localPrefixBankDeficitSlope / localPrefixBankSurplusSlope functions
of EconomicModel.lean. At each local-prefix date, the explicit
hypotheses are P.matchingIntensity = log 2 and tightness <= 1.

Frozen Python's cm/cp are algebraically identical to the RHS formulas.
The complete 33-row SOURCE/Python residual equivalence is NOT
established by these local slope lemmas: payment-distribution,
rate/quantity targets, the continuation P0, branch and remaining
row normalizations are separate obligations.
-/

namespace Ventura26LiquidityAllocation

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- Concrete SOURCE local-prefix deficit slope agrees with
the frozen Python cm formula on the low-tightness branch. -/
theorem sourceLocalPrefixOTC_deficitSlope_pythonFormula
    (P : Primitives S) (d : LocalPrefixDateData)
    (hmatch : P.matchingIntensity = Real.log 2)
    (htight : d.controls.tightness ≤ 1) :
    localPrefixBankDeficitSlope P d =
      d.corridorWidth * (1 - (1 / 2 : ℝ) +
        (1 / 2 : ℝ) /
          (1 + Real.sqrt (2 - d.controls.tightness))) := by
  unfold localPrefixBankDeficitSlope
  rw [hmatch]
  exact sourceOTC_logTwo_deficitSlope_pythonFormula
    d.currentReserveRate d.corridorWidth d.controls.tightness htight

#print axioms sourceLocalPrefixOTC_deficitSlope_pythonFormula

/-- Concrete SOURCE local-prefix surplus slope agrees with
the frozen Python cp formula under the same economic domain. -/
theorem sourceLocalPrefixOTC_surplusSlope_pythonFormula
    (P : Primitives S) (d : LocalPrefixDateData)
    (hmatch : P.matchingIntensity = Real.log 2)
    (htight : d.controls.tightness ≤ 1) :
    localPrefixBankSurplusSlope P d =
      d.corridorWidth * d.controls.tightness * (1 / 2 : ℝ) /
        (1 + Real.sqrt (2 - d.controls.tightness)) := by
  unfold localPrefixBankSurplusSlope
  rw [hmatch]
  exact sourceOTC_logTwo_surplusSlope_pythonFormula
    d.currentReserveRate d.corridorWidth d.controls.tightness htight

#print axioms sourceLocalPrefixOTC_surplusSlope_pythonFormula

end Ventura26LiquidityAllocation
