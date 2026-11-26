import Ventura26LiquidityAllocation.SourcePaymentOTCPythonJointCalibrationCandidate
import Ventura26LiquidityAllocation.SourceEconomicBankPolicyRootParityCandidate
import Ventura26LiquidityAllocation.Source33BankEconomicRowDispatchCandidate

/-!
# SOURCE two-date actual-data monetary calibration

This transports the certified one-date SOURCE payment law and OTC
identification to EconomicModel's ACTUAL zero/one prefix date data.

Under an explicit BinarySymmetricPaymentLaw witness, original
matchingIntensity log 2, both date tightness <= 1, and the four
original SOURCE monetary rules vanishing at both dates, the
actual reserve rates and quantities equal their policy targets.

This makes the restrictions needed to connect the target-substituted
bank rows to the true 33-dimensional SOURCE prefix transparent.
No assumption that frozen Python has a genuine SOURCE equilibrium,
nor any Python derivative identity, is imported.
-/

namespace Ventura26LiquidityAllocation

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- The actual original SOURCE prefix DATE ZERO and DATE ONE data
jointly obey frozen Python's binary-payment/OTC/reserve ratio
formula, given an explicit original SOURCE payment-law witness. -/
theorem sourcePrefixTwoDate_paymentOTC_calibration
    (P : Primitives S) (I : InheritedState)
    (Z : LocalPrefixCoordinates) (dateOne recurrent : S)
    (tail : LocalPrefixContinuationRule)
    (paymentMinus paymentPlus : BankPayment) (zeta : ℝ)
    (H : BinarySymmetricPaymentLaw P paymentMinus paymentPlus zeta)
    (hmatch : P.matchingIntensity = Real.log 2)
    (htight0 : (localPrefixDateZeroData P I Z dateOne).controls.tightness ≤ 1)
    (htight1 :
      (localPrefixDateOneData P Z dateOne recurrent tail).controls.tightness ≤ 1) :
    localPrefixMeanAbsolutePaymentShock P = zeta ∧
    (localPrefixReserveDepositRatio P (localPrefixDateZeroData P I Z dateOne) =
      (localPrefixDateZeroData P I Z dateOne).reserveRequirement +
      ((localPrefixDateZeroData P I Z dateOne).controls.depositRate /
        (localPrefixDateZeroData P I Z dateOne).currentReserveRate -
        (localPrefixDateZeroData P I Z dateOne).reserveRequirement) *
        zeta * (1 -
          (localPrefixDateZeroData P I Z dateOne).controls.tightness) /
          (1 + (localPrefixDateZeroData P I Z dateOne).controls.tightness)) ∧
    (localPrefixReserveDepositRatio P
      (localPrefixDateOneData P Z dateOne recurrent tail) =
      (localPrefixDateOneData P Z dateOne recurrent tail).reserveRequirement +
      ((localPrefixDateOneData P Z dateOne recurrent tail).controls.depositRate /
        (localPrefixDateOneData P Z dateOne recurrent tail).currentReserveRate -
        (localPrefixDateOneData P Z dateOne recurrent tail).reserveRequirement) *
        zeta * (1 -
          (localPrefixDateOneData P Z dateOne recurrent tail).controls.tightness) /
          (1 + (localPrefixDateOneData P Z dateOne recurrent tail).controls.tightness)) := by
  have h0 := sourcePaymentOTC_pythonJointConditionalCalibration
    P (localPrefixDateZeroData P I Z dateOne)
    paymentMinus paymentPlus zeta H hmatch htight0
  have h1 := sourcePaymentOTC_pythonJointConditionalCalibration
    P (localPrefixDateOneData P Z dateOne recurrent tail)
    paymentMinus paymentPlus zeta H hmatch htight1
  exact ⟨h0.1, h0.2.2.2, h1.2.2.2⟩

#print axioms sourcePrefixTwoDate_paymentOTC_calibration

/-- Once both original SOURCE monetary rows vanish at both dates,
realized reserve rates/quantities agree with target policy instruments
for the original two-date economic prefix (four target equalities). -/
theorem sourcePrefixTwoDate_policyTargets_of_fourOriginalRowsZero
    (P : Primitives S) (I : InheritedState)
    (Z : LocalPrefixCoordinates) (dateOne recurrent : S)
    (tail : LocalPrefixContinuationRule)
    (hR0 : 0 < (localPrefixDateZeroData P I Z dateOne).currentReserveRate)
    (hM0 : 0 < (localPrefixDateZeroData P I Z dateOne).currentReservesPre)
    (hR1 : 0 < (localPrefixDateOneData P Z dateOne recurrent tail).currentReserveRate)
    (hM1 : 0 < (localPrefixDateOneData P Z dateOne recurrent tail).currentReservesPre)
    (hr0 : localReducedRemainingResidual P
      (localPrefixDateZeroData P I Z dateOne) (6 : Fin 11) = 0)
    (hm0 : localReducedRemainingResidual P
      (localPrefixDateZeroData P I Z dateOne) (7 : Fin 11) = 0)
    (hr1 : localReducedRemainingResidual P
      (localPrefixDateOneData P Z dateOne recurrent tail) (6 : Fin 11) = 0)
    (hm1 : localReducedRemainingResidual P
      (localPrefixDateOneData P Z dateOne recurrent tail) (7 : Fin 11) = 0) :
    ((localPrefixDateZeroData P I Z dateOne).currentReserveRate =
        sourceRateRuleTarget P (localPrefixDateZeroData P I Z dateOne)) ∧
    ((localPrefixDateZeroData P I Z dateOne).currentReservesPre =
        sourceQuantityRuleTarget P (localPrefixDateZeroData P I Z dateOne)) ∧
    ((localPrefixDateOneData P Z dateOne recurrent tail).currentReserveRate =
        sourceRateRuleTarget P
          (localPrefixDateOneData P Z dateOne recurrent tail)) ∧
    ((localPrefixDateOneData P Z dateOne recurrent tail).currentReservesPre =
        sourceQuantityRuleTarget P
          (localPrefixDateOneData P Z dateOne recurrent tail)) := by
  exact ⟨
    sourceReserveRate_target_eq_of_policyRow_zero
      P (localPrefixDateZeroData P I Z dateOne) hR0 hr0,
    sourceReserveQuantity_target_eq_of_policyRow_zero
      P (localPrefixDateZeroData P I Z dateOne) hM0 hm0,
    sourceReserveRate_target_eq_of_policyRow_zero
      P (localPrefixDateOneData P Z dateOne recurrent tail) hR1 hr1,
    sourceReserveQuantity_target_eq_of_policyRow_zero
      P (localPrefixDateOneData P Z dateOne recurrent tail) hM1 hm1⟩

#print axioms sourcePrefixTwoDate_policyTargets_of_fourOriginalRowsZero

end Ventura26LiquidityAllocation
