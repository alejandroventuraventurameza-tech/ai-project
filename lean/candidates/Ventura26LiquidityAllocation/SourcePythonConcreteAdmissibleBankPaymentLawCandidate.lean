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

end Ventura26LiquidityAllocation
