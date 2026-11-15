import Ventura26LiquidityAllocation.SourcePrefixTwoDatePaymentOTCIdentificationCandidate

/-!
# Concrete Python payment-law calibration witness, not a SOURCE equilibrium

The illustrative Python model uses zeta=0.2 for its bank payment
shock magnitude. We construct a literal two-point measure with
probabilities 1/2 and signed shocks -1/5, +1/5.

Only if the actual SOURCE Primitives P payment fields are identified
with THESE explicit objects does this establish the genuine
BinarySymmetricPaymentLaw P 0 1 (1/5) required in the
two-date calibration theorem. This file does not construct a full
Primitives instance or claim the whole numerical economy is calibrated.
-/

namespace Ventura26LiquidityAllocation

/-- The explicit two-point support for the Python illustrative law. -/
def pythonPaymentSupport : Finset BankPayment := {0, 1}

/-- Both selected atoms have probability 1/2; all others have zero mass. -/
noncomputable def pythonPaymentProbability (ω : BankPayment) : ℝ :=
  if ω = 0 then 1 / 2 else if ω = 1 then 1 / 2 else 0

/-- Signed ±0.2 payment shocks, with zero outside the support. -/
noncomputable def pythonPaymentShock (ω : BankPayment) : ℝ :=
  if ω = 0 then -(1 / 5 : ℝ) else if ω = 1 then 1 / 5 else 0

theorem pythonPaymentSupport_mem (ω : BankPayment) :
    ω ∈ pythonPaymentSupport ↔ ω = 0 ∨ ω = 1 := by
  simp [pythonPaymentSupport]

theorem pythonPaymentLaw_atomValues :
    pythonPaymentProbability 0 = (1 / 2 : ℝ) ∧
    pythonPaymentProbability 1 = (1 / 2 : ℝ) ∧
    pythonPaymentShock 0 = -(1 / 5 : ℝ) ∧
    pythonPaymentShock 1 = (1 / 5 : ℝ) := by
  norm_num [pythonPaymentProbability, pythonPaymentShock]

/-- An explicit original SOURCE P whose payment support, probability
and shocks are identified with the Python law necessarily satisfies
the original genuine symmetric-binary-payment predicate.

The three field equalities are the remaining *calibration instantiation*
obligation. Crucially we do NOT silently assume BinarySymmetricPaymentLaw. -/
theorem sourcePaymentLaw_binaryWitness_fromActualFields
    {S : Type*} [Fintype S] [DecidableEq S]
    (P : Primitives S)
    (hSupport : P.paymentSupport = pythonPaymentSupport)
    (hProbability : P.paymentProbability = pythonPaymentProbability)
    (hShock : P.paymentShock = pythonPaymentShock) :
    BinarySymmetricPaymentLaw P 0 1 (1 / 5 : ℝ) := by
  unfold BinarySymmetricPaymentLaw
  refine ⟨by decide, by norm_num, ?_, ?_, ?_, ?_, ?_⟩
  · intro ω
    rw [hSupport]
    exact pythonPaymentSupport_mem ω
  · rw [hProbability]
    norm_num [pythonPaymentProbability]
  · rw [hProbability]
    norm_num [pythonPaymentProbability]
  · rw [hShock]
    norm_num [pythonPaymentShock]
  · rw [hShock]
    norm_num [pythonPaymentShock]

#print axioms sourcePaymentLaw_binaryWitness_fromActualFields

/-- With concrete matching payment fields, the original SOURCE
expectation moment is identically Python's illustrative zeta=1/5. -/
theorem sourcePaymentLaw_pythonMagnitude_fromActualFields
    {S : Type*} [Fintype S] [DecidableEq S]
    (P : Primitives S)
    (hSupport : P.paymentSupport = pythonPaymentSupport)
    (hProbability : P.paymentProbability = pythonPaymentProbability)
    (hShock : P.paymentShock = pythonPaymentShock) :
    localPrefixMeanAbsolutePaymentShock P = (1 / 5 : ℝ) := by
  exact localPrefixMeanAbsolutePaymentShock_eq_of_binarySymmetric
    P 0 1 (1 / 5 : ℝ)
    (sourcePaymentLaw_binaryWitness_fromActualFields
      P hSupport hProbability hShock)

#print axioms sourcePaymentLaw_pythonMagnitude_fromActualFields

end Ventura26LiquidityAllocation
