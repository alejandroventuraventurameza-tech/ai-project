import Ventura26LiquidityAllocation.SourcePythonPaymentConcreteBinaryWitnessCandidate

/-!
# A fully admissible concrete Python binary bank payment law in SOURCE

Unlike the previous conditional calibration theorem, the object
pythonConcreteBankPaymentLaw is a literal EconomicModel.BankPaymentLaw
including all probability, mass, and shock admissibility proofs.
Using Primitives.withBankPaymentLaw installs the law in an arbitrary
otherwise-unchanged SOURCE Primitives economy. The already checked
two-date matching theorem can then be applied without separate
payment-support/probability/shock field hypotheses.

This does NOT construct the full economic Primitives values matching
the frozen Python calibration, prove strict bank settlement signs,
or certify an economic solution/root.
-/

namespace Ventura26LiquidityAllocation

/-- Nonnegative probabilities on the entire countable label space. -/
theorem pythonPaymentProbability_nonneg (ω : BankPayment) :
    0 ≤ pythonPaymentProbability ω := by
  unfold pythonPaymentProbability
  split_ifs <;> norm_num

/-- Positive probability at every support atom. -/
theorem pythonPaymentProbability_pos_on_support (ω : BankPayment)
    (hω : ω ∈ pythonPaymentSupport) :
    0 < pythonPaymentProbability ω := by
  have h := (pythonPaymentSupport_mem ω).mp hω
  rcases h with h | h
  · subst ω
    norm_num [pythonPaymentProbability]
  · subst ω
    norm_num [pythonPaymentProbability]

/-- Bank payment shocks never violate the -1 lower domain. -/
theorem pythonPaymentShock_gt_neg_one_on_support (ω : BankPayment)
    (hω : ω ∈ pythonPaymentSupport) :
    -1 < pythonPaymentShock ω := by
  have h := (pythonPaymentSupport_mem ω).mp hω
  rcases h with h | h
  · subst ω
    norm_num [pythonPaymentShock]
  · subst ω
    norm_num [pythonPaymentShock]

/-- Labels outside the two-point support have zero probability. -/
theorem pythonPaymentProbability_zero_outside (ω : BankPayment)
    (hω : ω ∉ pythonPaymentSupport) :
    pythonPaymentProbability ω = 0 := by
  have h0 : ω ≠ 0 := by
    intro hz
    apply hω
    simp [pythonPaymentSupport, hz]
  have h1 : ω ≠ 1 := by
    intro hz
    apply hω
    simp [pythonPaymentSupport, hz]
  simp [pythonPaymentProbability, h0, h1]

/-- Exact normalization of the two-atom probability distribution. -/
theorem pythonPaymentProbability_sum_one :
    (∑ ω ∈ pythonPaymentSupport, pythonPaymentProbability ω) = 1 := by
  norm_num [pythonPaymentSupport, pythonPaymentProbability]

/-- The calibrated signed payment shock has exactly zero mean. -/
theorem pythonPaymentShock_mean_zero :
    (∑ ω ∈ pythonPaymentSupport,
      pythonPaymentProbability ω * pythonPaymentShock ω) = 0 := by
  norm_num [pythonPaymentSupport,
    pythonPaymentProbability, pythonPaymentShock]

/-- An admissible SOURCE BankPaymentLaw with exact ±0.2 Python shocks.
Existing SOURCE bank capacity parameters are inherited without change. -/
noncomputable def pythonConcreteBankPaymentLaw
    {S : Type*} [Fintype S] [DecidableEq S]
    (P : Primitives S) : BankPaymentLaw where
  support := pythonPaymentSupport
  probability := pythonPaymentProbability
  shock := pythonPaymentShock
  depositCap := P.bankDepositCap
  loanCap := P.bankLoanCap
  probability_nonneg := pythonPaymentProbability_nonneg
  probability_pos_on_support := pythonPaymentProbability_pos_on_support
  shock_gt_neg_one_on_support := pythonPaymentShock_gt_neg_one_on_support
  probability_zero_outside := pythonPaymentProbability_zero_outside
  probability_sum_one := pythonPaymentProbability_sum_one
  shock_mean_zero := pythonPaymentShock_mean_zero
  caps_nonneg := P.bank_caps_nonneg

/-- A full SOURCE economy carrying the concrete calibrated payment law
instead of an assumed binary-law hypothesis. All non-payment primitives
are inherited from P, including cap values and the policy paths. -/
noncomputable def sourceWithConcretePythonPaymentLaw
    {S : Type*} [Fintype S] [DecidableEq S]
    (P : Primitives S) : Primitives S :=
  P.withBankPaymentLaw (pythonConcreteBankPaymentLaw P)

/-- The installed original SOURCE economic primitives satisfy the
genuine BinarySymmetricPaymentLaw at zeta = 1/5 without extra
assumptions on the previous arbitrary payment law of P. -/
theorem sourceWithConcretePythonPaymentLaw_binaryWitness
    {S : Type*} [Fintype S] [DecidableEq S]
    (P : Primitives S) :
    BinarySymmetricPaymentLaw
      (sourceWithConcretePythonPaymentLaw P) 0 1 (1 / 5 : ℝ) := by
  apply sourcePaymentLaw_binaryWitness_fromActualFields
  · rfl
  · rfl
  · rfl

#print axioms sourceWithConcretePythonPaymentLaw_binaryWitness

/-- Under the remaining explicit matching and tightness hypotheses,
the installed calibrated payment law yields SOURCE's actual two-date
Python reserve-ratio formulas with NO payment-law hypotheses left. -/
theorem sourceWithConcretePythonPaymentLaw_twoDateRatios
    {S : Type*} [Fintype S] [DecidableEq S]
    (P : Primitives S) (I : InheritedState)
    (Z : LocalPrefixCoordinates) (dateOne recurrent : S)
    (tail : LocalPrefixContinuationRule)
    (hmatch :
      (sourceWithConcretePythonPaymentLaw P).matchingIntensity = Real.log 2)
    (htight0 :
      (localPrefixDateZeroData
        (sourceWithConcretePythonPaymentLaw P) I Z dateOne).controls.tightness ≤ 1)
    (htight1 :
      (localPrefixDateOneData
        (sourceWithConcretePythonPaymentLaw P) Z dateOne recurrent tail).controls.tightness ≤ 1) :
    localPrefixMeanAbsolutePaymentShock
      (sourceWithConcretePythonPaymentLaw P) = (1 / 5 : ℝ) ∧
    (localPrefixReserveDepositRatio
      (sourceWithConcretePythonPaymentLaw P)
      (localPrefixDateZeroData
        (sourceWithConcretePythonPaymentLaw P) I Z dateOne) =
      (localPrefixDateZeroData
        (sourceWithConcretePythonPaymentLaw P) I Z dateOne).reserveRequirement +
      ((localPrefixDateZeroData
        (sourceWithConcretePythonPaymentLaw P) I Z dateOne).controls.depositRate /
        (localPrefixDateZeroData
          (sourceWithConcretePythonPaymentLaw P) I Z dateOne).currentReserveRate -
        (localPrefixDateZeroData
          (sourceWithConcretePythonPaymentLaw P) I Z dateOne).reserveRequirement) *
        (1 / 5 : ℝ) *
        (1 - (localPrefixDateZeroData
          (sourceWithConcretePythonPaymentLaw P) I Z dateOne).controls.tightness) /
        (1 + (localPrefixDateZeroData
          (sourceWithConcretePythonPaymentLaw P) I Z dateOne).controls.tightness)) ∧
    (localPrefixReserveDepositRatio
      (sourceWithConcretePythonPaymentLaw P)
      (localPrefixDateOneData
        (sourceWithConcretePythonPaymentLaw P) Z dateOne recurrent tail) =
      (localPrefixDateOneData
        (sourceWithConcretePythonPaymentLaw P) Z dateOne recurrent tail).reserveRequirement +
      ((localPrefixDateOneData
        (sourceWithConcretePythonPaymentLaw P) Z dateOne recurrent tail).controls.depositRate /
        (localPrefixDateOneData
          (sourceWithConcretePythonPaymentLaw P) Z dateOne recurrent tail).currentReserveRate -
        (localPrefixDateOneData
          (sourceWithConcretePythonPaymentLaw P) Z dateOne recurrent tail).reserveRequirement) *
        (1 / 5 : ℝ) *
        (1 - (localPrefixDateOneData
          (sourceWithConcretePythonPaymentLaw P) Z dateOne recurrent tail).controls.tightness) /
        (1 + (localPrefixDateOneData
          (sourceWithConcretePythonPaymentLaw P) Z dateOne recurrent tail).controls.tightness)) := by
  exact sourcePrefixTwoDate_paymentOTC_calibration
    (sourceWithConcretePythonPaymentLaw P) I Z dateOne recurrent tail
    0 1 (1 / 5 : ℝ)
    (sourceWithConcretePythonPaymentLaw_binaryWitness P)
    hmatch htight0 htight1

#print axioms sourceWithConcretePythonPaymentLaw_twoDateRatios

end Ventura26LiquidityAllocation
