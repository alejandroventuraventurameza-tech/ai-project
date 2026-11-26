import Ventura26LiquidityAllocation.SourceThreeBankRowsOffRootExponentialCrossCandidate

/-!
# Original SOURCE five monetary/bank rows: exact nonlinear targetization

At a *single actual SOURCE economic date*, the five monetary-bank
rows are reserve rate, reserve quantity, loan pricing, deposit pricing,
and bank balance (remaining-row indices 6..10).

This module relates the SOURCE realized-variable equations to targetized
SOURCE formulas through the EXACT exponential secant
  E(u) = (exp u - 1)/u  if u != 0, and E(0)=1.
The targetization is an invertible triangular row operation at EVERY
admissible economic point, not merely at a policy root.

This is NOT identification of original finite_irf.py with EconomicModel:
low-tightness/log-two OTC matching and the SOURCE payment law appear
as explicit hypotheses. The other 23 SOURCE prefix equations, Python
chart/calibration/parameters, original 33x33 Jacobian, root existence
and economic equilibrium remain separate obligations.
-/

namespace Ventura26LiquidityAllocation
namespace CurrentSourceFiveBankBridge

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- The exponential divided-difference is well-defined at zero. -/
noncomputable def expSecant (u : ℝ) : ℝ :=
  if u = 0 then 1 else (Real.exp u - 1) / u

theorem expSecant_mul (u : ℝ) :
    expSecant u * u = Real.exp u - 1 := by
  by_cases hu : u = 0
  · simp [expSecant, hu]
  · simp only [expSecant, if_neg hu]
    field_simp [hu]

#print axioms expSecant_mul

/-- SOURCE five-row realized monetary/banking subvector. -/
noncomputable def sourceFiveRows
    (P : Primitives S) (d : LocalPrefixDateData) : Fin 5 → ℝ :=
  ![
    localReducedRemainingResidual P d 6,
    localReducedRemainingResidual P d 7,
    localReducedRemainingResidual P d 8,
    localReducedRemainingResidual P d 9,
    localReducedRemainingResidual P d 10
  ]

/-- Reserve-rate-target loan pricing with the exact SOURCE OTC
log-two slopes translated to the frozen Python slope *formulas*. -/
noncomputable def sourceTargetLoanRow
    (P : Primitives S) (d : LocalPrefixDateData) : ℝ :=
  d.controls.loanRate - sourceRateRuleTarget P d -
    (sourceFrozenPythonDeficitSlope d +
      sourceFrozenPythonSurplusSlope d) / 2

/-- Reserve-rate-target deposit pricing. The SOURCE payment shock
expectation is retained, not replaced by an unproved Python law. -/
noncomputable def sourceTargetDepositRow
    (P : Primitives S) (d : LocalPrefixDateData) : ℝ :=
  sourceRateRuleTarget P d +
    (1 - d.reserveRequirement) *
      (sourceFrozenPythonDeficitSlope d +
        sourceFrozenPythonSurplusSlope d) / 2 -
    (d.controls.depositRate / sourceRateRuleTarget P d -
      d.reserveRequirement) *
      localPrefixMeanAbsolutePaymentShock P *
        (sourceFrozenPythonDeficitSlope d -
          sourceFrozenPythonSurplusSlope d) / 2 -
    d.controls.depositRate

/-- Both policy targets are substituted in the SOURCE bank balance,
keeping the genuine SOURCE loans, face value, and payment shock. -/
noncomputable def sourceTargetBalanceRow
    (P : Primitives S) (d : LocalPrefixDateData) : ℝ :=
  localPrefixReducedBankLoans P d -
    d.currentBankFace / d.controls.inflation -
    sourceBankMultiplierAtRate d.reserveRequirement
      d.controls.depositRate
      (localPrefixMeanAbsolutePaymentShock P *
        (1 - d.controls.tightness) /
          (1 + d.controls.tightness))
      (sourceRateRuleTarget P d) *
      sourceQuantityRuleTarget P d

/-- Same monetary policy rows, but targetized banking prices/balance. -/
noncomputable def sourceTargetFiveRows
    (P : Primitives S) (d : LocalPrefixDateData) : Fin 5 → ℝ :=
  ![
    localReducedRemainingResidual P d 6,
    localReducedRemainingResidual P d 7,
    sourceTargetLoanRow P d,
    sourceTargetDepositRow P d,
    sourceTargetBalanceRow P d
  ]

/-- Rate-residual coefficient in the loan-price substitution. -/
noncomputable def sourceLoanCross
    (P : Primitives S) (d : LocalPrefixDateData) : ℝ :=
  sourceRateRuleTarget P d *
    expSecant (localReducedRemainingResidual P d 6)

/-- Rate-residual coefficient in the deposit-price substitution. -/
noncomputable def sourceDepositCross
    (P : Primitives S) (d : LocalPrefixDateData) : ℝ :=
  -(sourceRateRuleTarget P d *
      (1 +
        d.controls.depositRate *
          localPrefixMeanAbsolutePaymentShock P *
          (sourceFrozenPythonDeficitSlope d -
            sourceFrozenPythonSurplusSlope d) /
          (2 * d.currentReserveRate * sourceRateRuleTarget P d))) *
    expSecant (localReducedRemainingResidual P d 6)

/-- Rate-policy contribution to the transformed balance equation. -/
noncomputable def sourceBalanceRateCross
    (P : Primitives S) (d : LocalPrefixDateData) : ℝ :=
  sourceBankRateCrossCoefficient P d *
    expSecant (localReducedRemainingResidual P d 6)

/-- Quantity-policy contribution to the transformed balance equation. -/
noncomputable def sourceBalanceQuantityCross
    (P : Primitives S) (d : LocalPrefixDateData) : ℝ :=
  sourceBankQuantityCrossCoefficient P d *
    expSecant (localReducedRemainingResidual P d 7)

/-- A triangular shear of the five rows: first two policy rows fixed. -/
def fiveBankShear (loan deposit balanceRate balanceQuantity : ℝ)
    (v : Fin 5 → ℝ) : Fin 5 → ℝ :=
  fun i =>
    if i = 2 then v i + loan * v 0
    else if i = 3 then v i + deposit * v 0
    else if i = 4 then
      v i + balanceRate * v 0 + balanceQuantity * v 1
    else v i

/-- Explicit inverse for any real coefficients, without a zero-root premise. -/
theorem fiveBankShear_inverse
    (a b c d : ℝ) (v : Fin 5 → ℝ) :
    fiveBankShear (-a) (-b) (-c) (-d)
      (fiveBankShear a b c d v) = v := by
  funext i
  fin_cases i <;> simp [fiveBankShear] <;> ring

/-- Targetization cannot create or eliminate an all-five-rows root. -/
theorem fiveBankShear_zero_iff
    (a b c d : ℝ) (v : Fin 5 → ℝ) :
    fiveBankShear a b c d v = 0 ↔ v = 0 := by
  constructor
  · intro h
    have hi := fiveBankShear_inverse a b c d v
    rw [h] at hi
    have hz : fiveBankShear (-a) (-b) (-c) (-d)
        (0 : Fin 5 → ℝ) = 0 := by
      funext i
      fin_cases i <;> simp [fiveBankShear]
    rw [hz] at hi
    exact hi.symm
  · intro h
    subst v
    funext i
    fin_cases i <;> simp [fiveBankShear]

#print axioms fiveBankShear_inverse
#print axioms fiveBankShear_zero_iff

/-- The ACTUAL SOURCE targetized five-vector is exactly a triangular
row shear with economic state-dependent coefficients. The 3 economic
banking identities come from the real SOURCE 11-row/date formulas. -/
theorem sourceTargetFiveRows_eq_nonlinearShear
    (P : Primitives S) (d : LocalPrefixDateData)
    (hmatch : P.matchingIntensity = Real.log 2)
    (htight : d.controls.tightness ≤ 1)
    (hR : 0 < d.currentReserveRate)
    (hM : 0 < d.currentReservesPre)
    (hRatio : localPrefixReserveDepositRatio P d ≠ 0)
    (hTargetRatio :
      sourceBankRatioAtRate d.reserveRequirement
        d.controls.depositRate
        (localPrefixMeanAbsolutePaymentShock P *
          (1 - d.controls.tightness) /
            (1 + d.controls.tightness))
        (sourceRateRuleTarget P d) ≠ 0) :
    sourceTargetFiveRows P d =
      fiveBankShear
        (sourceLoanCross P d) (sourceDepositCross P d)
        (sourceBalanceRateCross P d) (sourceBalanceQuantityCross P d)
        (sourceFiveRows P d) := by
  obtain ⟨hLoan, hDeposit, hBalance⟩ :=
    sourceThreeBankRows_offRoot_exponentialCrossRows
      P d hmatch htight hR hM hRatio hTargetRatio
  have hLoan' : sourceTargetLoanRow P d -
      localReducedRemainingResidual P d 8 =
      sourceLoanCross P d *
        localReducedRemainingResidual P d 6 := by
    calc
      _ = sourceRateRuleTarget P d *
          (Real.exp (localReducedRemainingResidual P d 6) - 1) := by
            simpa only [sourceTargetLoanRow] using hLoan
      _ = _ := by
        unfold sourceLoanCross
        rw [← expSecant_mul (localReducedRemainingResidual P d 6)]
        ring
  have hDeposit' : sourceTargetDepositRow P d -
      localReducedRemainingResidual P d 9 =
      sourceDepositCross P d *
        localReducedRemainingResidual P d 6 := by
    calc
      _ = -sourceRateRuleTarget P d *
          (Real.exp (localReducedRemainingResidual P d 6) - 1) *
          (1 +
            d.controls.depositRate *
              localPrefixMeanAbsolutePaymentShock P *
              (sourceFrozenPythonDeficitSlope d -
                sourceFrozenPythonSurplusSlope d) /
                (2 * d.currentReserveRate * sourceRateRuleTarget P d)) := by
            simpa only [sourceTargetDepositRow] using hDeposit
      _ = _ := by
        unfold sourceDepositCross
        rw [← expSecant_mul (localReducedRemainingResidual P d 6)]
        ring
  have hBankOriginal :
      localReducedRemainingResidual P d 10 =
      localPrefixReducedBankLoans P d -
        d.currentBankFace / d.controls.inflation -
        (1 / localPrefixReserveDepositRatio P d - 1) *
          d.currentReservesPre := by
    change localPrefixReducedBankLoans P d -
      (d.currentBankFace / d.controls.inflation +
        (1 / localPrefixReserveDepositRatio P d - 1) *
          d.currentReservesPre) =
      localPrefixReducedBankLoans P d -
        d.currentBankFace / d.controls.inflation -
        (1 / localPrefixReserveDepositRatio P d - 1) *
          d.currentReservesPre
    ring
  have hBalance' : sourceTargetBalanceRow P d -
      localReducedRemainingResidual P d 10 =
      sourceBalanceRateCross P d *
        localReducedRemainingResidual P d 6 +
      sourceBalanceQuantityCross P d *
        localReducedRemainingResidual P d 7 := by
    calc
      _ = sourceBankQuantityCrossCoefficient P d *
            (Real.exp (localReducedRemainingResidual P d 7) - 1) +
          sourceBankRateCrossCoefficient P d *
            (Real.exp (localReducedRemainingResidual P d 6) - 1) := by
              rw [hBankOriginal]
              simpa only [sourceTargetBalanceRow] using hBalance
      _ = _ := by
        unfold sourceBalanceRateCross sourceBalanceQuantityCross
        rw [← expSecant_mul (localReducedRemainingResidual P d 6)]
        rw [← expSecant_mul (localReducedRemainingResidual P d 7)]
        ring
  funext i
  fin_cases i
  · rfl
  · rfl
  · change sourceTargetLoanRow P d =
      localReducedRemainingResidual P d 8 +
        sourceLoanCross P d * localReducedRemainingResidual P d 6
    linear_combination hLoan'
  · change sourceTargetDepositRow P d =
      localReducedRemainingResidual P d 9 +
        sourceDepositCross P d * localReducedRemainingResidual P d 6
    linear_combination hDeposit'
  · change sourceTargetBalanceRow P d =
      localReducedRemainingResidual P d 10 +
        sourceBalanceRateCross P d * localReducedRemainingResidual P d 6 +
        sourceBalanceQuantityCross P d * localReducedRemainingResidual P d 7
    linear_combination hBalance'

#print axioms sourceTargetFiveRows_eq_nonlinearShear

/-- Exact zero-set equivalence for genuine SOURCE five-row/date monetary
banking subsystem and its SOURCE-formula targetization, OFF ROOT. -/
theorem sourceTargetFiveRows_zero_iff_sourceFiveRows_zero
    (P : Primitives S) (d : LocalPrefixDateData)
    (hmatch : P.matchingIntensity = Real.log 2)
    (htight : d.controls.tightness ≤ 1)
    (hR : 0 < d.currentReserveRate)
    (hM : 0 < d.currentReservesPre)
    (hRatio : localPrefixReserveDepositRatio P d ≠ 0)
    (hTargetRatio :
      sourceBankRatioAtRate d.reserveRequirement
        d.controls.depositRate
        (localPrefixMeanAbsolutePaymentShock P *
          (1 - d.controls.tightness) /
            (1 + d.controls.tightness))
        (sourceRateRuleTarget P d) ≠ 0) :
    sourceTargetFiveRows P d = 0 ↔ sourceFiveRows P d = 0 := by
  rw [sourceTargetFiveRows_eq_nonlinearShear
    P d hmatch htight hR hM hRatio hTargetRatio]
  exact fiveBankShear_zero_iff _ _ _ _ _

#print axioms sourceTargetFiveRows_zero_iff_sourceFiveRows_zero

end CurrentSourceFiveBankBridge
end Ventura26LiquidityAllocation
