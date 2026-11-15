import Ventura26LiquidityAllocation.SourcePythonConcreteAdmissibleBankPaymentLawCandidate

/-!
# Strict payment-sign branch: original SOURCE banking expectations

The exact Python two-point law is installed into the genuine SOURCE
Primitives structure, rather than only assumed as a predicate. On
any actual source Allocation X, calendar t and history h satisfying
the two literal bank-settlement strict-sign inequalities, the
original SOURCE expectations in the bank's loan/deposit FOCs reduce
to the corresponding average and signed difference of the genuine
OTC slopes.

This does not derive the strict inequalities from numerical
coordinates. That requires a separate interval or analytic sign
certificate for the calibrated state. The finite first-order
pricing equations are not asserted to be sufficient for bank
optimization or equilibrium.
-/

namespace Ventura26LiquidityAllocation

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- With the concrete installed payment law, SOURCE's actual bank
expectations equal the binary frozen-Python slope combinations on
the strict deficit/surplus branch. The payment-law witness has
been constructed; ONLY the two true bank settlement sign
conditions remain hypotheses. -/
theorem sourceInstalledPythonLaw_strictSigns_actualBankExpectations
    (P : Primitives S) (X : Allocation S)
    (t : ℕ) (h : History S t)
    (hminus :
      localBankSettlementSurplus
        (sourceWithConcretePythonPaymentLaw P) X t h 0 < 0)
    (hplus :
      0 < localBankSettlementSurplus
        (sourceWithConcretePythonPaymentLaw P) X t h 1) :
    finiteSupportExpectation
      (sourceWithConcretePythonPaymentLaw P).paymentSupport
      (sourceWithConcretePythonPaymentLaw P).paymentProbability
      (localBankLiquidityMarginal
        (sourceWithConcretePythonPaymentLaw P) X t h) =
        (bankOTCDeficitSlopeAt
          (sourceWithConcretePythonPaymentLaw P) X t h
          (X.bankTightness t h) +
          bankOTCSurplusSlopeAt
            (sourceWithConcretePythonPaymentLaw P) X t h
            (X.bankTightness t h)) / 2 ∧
    finiteSupportExpectation
      (sourceWithConcretePythonPaymentLaw P).paymentSupport
      (sourceWithConcretePythonPaymentLaw P).paymentProbability
      (fun ω =>
        localBankLiquidityMarginal
          (sourceWithConcretePythonPaymentLaw P) X t h ω *
        (sourceWithConcretePythonPaymentLaw P).paymentShock ω) =
        -(1 / 5 : ℝ) *
          (bankOTCDeficitSlopeAt
            (sourceWithConcretePythonPaymentLaw P) X t h
            (X.bankTightness t h) -
            bankOTCSurplusSlopeAt
              (sourceWithConcretePythonPaymentLaw P) X t h
              (X.bankTightness t h)) / 2 := by
  exact binaryStrictSigns_expectations
    (sourceWithConcretePythonPaymentLaw P) X t h
    0 1 (1 / 5 : ℝ)
    (sourceWithConcretePythonPaymentLaw_binaryWitness P)
    hminus hplus

#print axioms sourceInstalledPythonLaw_strictSigns_actualBankExpectations

end Ventura26LiquidityAllocation
