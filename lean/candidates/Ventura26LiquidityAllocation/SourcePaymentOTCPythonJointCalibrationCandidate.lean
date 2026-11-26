import Ventura26LiquidityAllocation.SourceLocalPrefixOTCPythonMatchingCandidate

/-!
# Joint calibration gate: ORIGINAL SOURCE payment law + OTC to Python

At one date and under an explicit genuine SOURCE
BinarySymmetricPaymentLaw witness, the model's finite-support
absolute payment-shock expectation equals a positive magnitude zeta.
Additionally, under matchingIntensity = log 2 and tightness <= 1,
SOURCE's actual OTC deficit and surplus slopes reduce to the
frozen Python chi_minus/chi_plus analytic expressions.

The proof explicitly combines the independent hypotheses that were
previously scattered across the bank pricing and ratio lemmas.
It makes no claim that the full economic parameters/coordinates or
Python's 33-dimensional residual functions are already identified.
-/

namespace Ventura26LiquidityAllocation

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- Exact SOURCE payment-size, two OTC slopes, and reserve/deposit
ratio identification at one date. No approximation or frozen OTC
slope assumption is used: each SOURCE quantity is literal. -/
theorem sourcePaymentOTC_pythonJointConditionalCalibration
    (P : Primitives S) (d : LocalPrefixDateData)
    (paymentMinus paymentPlus : BankPayment)
    (zeta : ℝ)
    (H : BinarySymmetricPaymentLaw P paymentMinus paymentPlus zeta)
    (hmatch : P.matchingIntensity = Real.log 2)
    (htight : d.controls.tightness ≤ 1) :
    localPrefixMeanAbsolutePaymentShock P = zeta ∧
    localPrefixBankDeficitSlope P d =
      d.corridorWidth * (1 - (1 / 2 : ℝ) +
        (1 / 2 : ℝ) /
          (1 + Real.sqrt (2 - d.controls.tightness))) ∧
    localPrefixBankSurplusSlope P d =
      d.corridorWidth * d.controls.tightness * (1 / 2 : ℝ) /
        (1 + Real.sqrt (2 - d.controls.tightness)) ∧
    localPrefixReserveDepositRatio P d =
      d.reserveRequirement +
        (d.controls.depositRate / d.currentReserveRate -
          d.reserveRequirement) * zeta *
          (1 - d.controls.tightness) /
            (1 + d.controls.tightness) := by
  have hMoment := localPrefixMeanAbsolutePaymentShock_eq_of_binarySymmetric
    P paymentMinus paymentPlus zeta H
  have hDeficit := sourceLocalPrefixOTC_deficitSlope_pythonFormula
    P d hmatch htight
  have hSurplus := sourceLocalPrefixOTC_surplusSlope_pythonFormula
    P d hmatch htight
  refine ⟨hMoment, hDeficit, hSurplus, ?_⟩
  unfold localPrefixReserveDepositRatio
  rw [hMoment]

#print axioms sourcePaymentOTC_pythonJointConditionalCalibration

end Ventura26LiquidityAllocation
