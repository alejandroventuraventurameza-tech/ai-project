import Ventura26LiquidityAllocation.CurrentSourceFiveBankTargetization
import Ventura26LiquidityAllocation.SourceTwoDateBankFiveRowShearCandidate

/-!
# Two-date actual SOURCE 33-row banking targetization

This lifts the previously kernel-verified exact one-date SOURCE
monetary/banking identity to the concrete 33-row finite economic prefix.
The targetized residual is defined independently by replacing the
six actual banking rows in the SOURCE date-zero/date-one vector. Other
27 rows, including all four monetary policy rules, are unchanged.

The economic state-dependent coefficients are exactly those from
CurrentSourceFiveBankTargetization; no frozen coefficient or first
order approximation is assumed. Validity is conditional on the
specified SOURCE OTC matching calibration and banking domain for
both original date data.

This is SOURCE-to-targetized-SOURCE, NOT SOURCE-to-finite_irf.py.
It proves no full equilibrium, root existence or source Jacobian
inverse bound.
-/

namespace Ventura26LiquidityAllocation
namespace CurrentSourceTwoDateBank

open CurrentSourceFiveBankBridge

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- Explicit banking domain needed for both dates separately. -/
def TargetBankAdmissible (P : Primitives S)
    (d : LocalPrefixDateData) : Prop :=
  d.controls.tightness ≤ 1 ∧
    0 < d.currentReserveRate ∧ 0 < d.currentReservesPre ∧
    localPrefixReserveDepositRatio P d ≠ 0 ∧
    sourceBankRatioAtRate d.reserveRequirement
      d.controls.depositRate
      (localPrefixMeanAbsolutePaymentShock P *
        (1 - d.controls.tightness) /
        (1 + d.controls.tightness))
      (sourceRateRuleTarget P d) ≠ 0

/-- Actual economic SOURCE date-zero data at the same inherited state. -/
noncomputable def dateZero (P : Primitives S)
    (I : InheritedState) (Z : LocalPrefixCoordinates)
    (dateOneState : S) : LocalPrefixDateData :=
  localPrefixDateZeroData P I Z dateOneState

/-- Actual economic SOURCE date-one data, same Z and continuation. -/
noncomputable def dateOne (P : Primitives S)
    (Z : LocalPrefixCoordinates) (dateOneState recurrent : S)
    (tail : LocalPrefixContinuationRule) : LocalPrefixDateData :=
  localPrefixDateOneData P Z dateOneState recurrent tail

/-- ORIGINAL, not Python-translated, SOURCE 33 residual at one economic
coordinate Z, indexed in the exact paper/Lean source ordering. -/
noncomputable def originalPrefix33
    (branch : LocalPrefixBranch) (P : Primitives S)
    (I : InheritedState) (Z : LocalPrefixCoordinates)
    (dateOneState recurrent : S)
    (tail : LocalPrefixContinuationRule) : Fin 33 → ℝ :=
  fun i => localReducedPrefixResidual branch P I Z
    dateOneState recurrent tail (localPrefixEquationOfIndex i)

/-- Independently targetize the six actual bank rows in the 33-vector.
Both monetary-rate and monetary-quantity rule rows are preserved. -/
noncomputable def targetizedPrefix33
    (branch : LocalPrefixBranch) (P : Primitives S)
    (I : InheritedState) (Z : LocalPrefixCoordinates)
    (dateOneState recurrent : S)
    (tail : LocalPrefixContinuationRule) : Fin 33 → ℝ :=
  let d0 := dateZero P I Z dateOneState
  let d1 := dateOne P Z dateOneState recurrent tail
  let F := originalPrefix33 branch P I Z dateOneState recurrent tail
  fun i =>
    if i = 14 then sourceTargetLoanRow P d0
    else if i = 15 then sourceTargetDepositRow P d0
    else if i = 16 then sourceTargetBalanceRow P d0
    else if i = 30 then sourceTargetLoanRow P d1
    else if i = 31 then sourceTargetDepositRow P d1
    else if i = 32 then sourceTargetBalanceRow P d1
    else F i

/-- Extract the exact three economic cross-row identities from the
five-row SOURCE theorem: not assumptions of the 33-row statement. -/
private theorem threeTargetRows_eq_crossRows
    (P : Primitives S) (d : LocalPrefixDateData)
    (hmatch : P.matchingIntensity = Real.log 2)
    (hadm : TargetBankAdmissible P d) :
    (sourceTargetLoanRow P d =
      localReducedRemainingResidual P d 8 +
        sourceLoanCross P d * localReducedRemainingResidual P d 6) ∧
    (sourceTargetDepositRow P d =
      localReducedRemainingResidual P d 9 +
        sourceDepositCross P d * localReducedRemainingResidual P d 6) ∧
    (sourceTargetBalanceRow P d =
      localReducedRemainingResidual P d 10 +
        sourceBalanceRateCross P d * localReducedRemainingResidual P d 6 +
        sourceBalanceQuantityCross P d *
          localReducedRemainingResidual P d 7) := by
  rcases hadm with ⟨htight, hR, hM, hRatio, hTargetRatio⟩
  have h := sourceTargetFiveRows_eq_nonlinearShear
    P d hmatch htight hR hM hRatio hTargetRatio
  constructor
  · have hp := congrArg (fun v : Fin 5 → ℝ => v (2 : Fin 5)) h
    simpa [sourceTargetFiveRows, sourceFiveRows, fiveBankShear] using hp
  constructor
  · have hp := congrArg (fun v : Fin 5 → ℝ => v (3 : Fin 5)) h
    simpa [sourceTargetFiveRows, sourceFiveRows, fiveBankShear] using hp
  · have hp := congrArg (fun v : Fin 5 → ℝ => v (4 : Fin 5)) h
    simpa [sourceTargetFiveRows, sourceFiveRows, fiveBankShear] using hp

/-- Actual two-date banking targetization is an EXACT nonlinear
state-dependent 33-row shear. The underlying SOURCE residual is used
on both sides and all other rows are unchanged. -/
theorem targetizedPrefix33_eq_fullEconomicBankShear
    (branch : LocalPrefixBranch) (P : Primitives S)
    (I : InheritedState) (Z : LocalPrefixCoordinates)
    (dateOneState recurrent : S)
    (tail : LocalPrefixContinuationRule)
    (hmatch : P.matchingIntensity = Real.log 2)
    (h0 : TargetBankAdmissible P (dateZero P I Z dateOneState))
    (h1 : TargetBankAdmissible P
      (dateOne P Z dateOneState recurrent tail)) :
    targetizedPrefix33 branch P I Z dateOneState recurrent tail =
      sourceTwoDateBankFiveRowShear
        (sourceLoanCross P (dateZero P I Z dateOneState))
        (sourceDepositCross P (dateZero P I Z dateOneState))
        (sourceLoanCross P (dateOne P Z dateOneState recurrent tail))
        (sourceDepositCross P (dateOne P Z dateOneState recurrent tail))
        (sourceBalanceRateCross P (dateZero P I Z dateOneState))
        (sourceBalanceQuantityCross P (dateZero P I Z dateOneState))
        (sourceBalanceRateCross P (dateOne P Z dateOneState recurrent tail))
        (sourceBalanceQuantityCross P
          (dateOne P Z dateOneState recurrent tail))
        (originalPrefix33 branch P I Z dateOneState recurrent tail) := by
  obtain ⟨hLoan0, hDeposit0, hBalance0⟩ :=
    threeTargetRows_eq_crossRows
      P (dateZero P I Z dateOneState) hmatch h0
  obtain ⟨hLoan1, hDeposit1, hBalance1⟩ :=
    threeTargetRows_eq_crossRows
      P (dateOne P Z dateOneState recurrent tail) hmatch h1
  have hF12 : originalPrefix33 branch P I Z dateOneState recurrent tail 12 =
      localReducedRemainingResidual P (dateZero P I Z dateOneState) 6 := by rfl
  have hF13 : originalPrefix33 branch P I Z dateOneState recurrent tail 13 =
      localReducedRemainingResidual P (dateZero P I Z dateOneState) 7 := by rfl
  have hF14 : originalPrefix33 branch P I Z dateOneState recurrent tail 14 =
      localReducedRemainingResidual P (dateZero P I Z dateOneState) 8 := by rfl
  have hF15 : originalPrefix33 branch P I Z dateOneState recurrent tail 15 =
      localReducedRemainingResidual P (dateZero P I Z dateOneState) 9 := by rfl
  have hF16 : originalPrefix33 branch P I Z dateOneState recurrent tail 16 =
      localReducedRemainingResidual P (dateZero P I Z dateOneState) 10 := by rfl
  have hF28 : originalPrefix33 branch P I Z dateOneState recurrent tail 28 =
      localReducedRemainingResidual P
        (dateOne P Z dateOneState recurrent tail) 6 := by rfl
  have hF29 : originalPrefix33 branch P I Z dateOneState recurrent tail 29 =
      localReducedRemainingResidual P
        (dateOne P Z dateOneState recurrent tail) 7 := by rfl
  have hF30 : originalPrefix33 branch P I Z dateOneState recurrent tail 30 =
      localReducedRemainingResidual P
        (dateOne P Z dateOneState recurrent tail) 8 := by rfl
  have hF31 : originalPrefix33 branch P I Z dateOneState recurrent tail 31 =
      localReducedRemainingResidual P
        (dateOne P Z dateOneState recurrent tail) 9 := by rfl
  have hF32 : originalPrefix33 branch P I Z dateOneState recurrent tail 32 =
      localReducedRemainingResidual P
        (dateOne P Z dateOneState recurrent tail) 10 := by rfl
  funext i
  fin_cases i <;>
    simp [targetizedPrefix33,
      sourceTwoDateBankFiveRowShear,
      sourceTwoDateBankPricingRowShear,
      sourceTwoDateMonetaryBankRowShear,
      sourceDateOneMonetaryBankRowShear,
      sourceMonetaryBankRowShear,
      hF12, hF13, hF14, hF15, hF16,
      hF28, hF29, hF30, hF31, hF32,
      hLoan0, hDeposit0, hBalance0,
      hLoan1, hDeposit1, hBalance1]

#print axioms targetizedPrefix33_eq_fullEconomicBankShear

/-- Targetized ACTUAL two-date SOURCE 33 residual has the exact
same zeros as the unmodified actual SOURCE 33 residual. -/
theorem targetizedPrefix33_zero_iff_originalPrefix33_zero
    (branch : LocalPrefixBranch) (P : Primitives S)
    (I : InheritedState) (Z : LocalPrefixCoordinates)
    (dateOneState recurrent : S)
    (tail : LocalPrefixContinuationRule)
    (hmatch : P.matchingIntensity = Real.log 2)
    (h0 : TargetBankAdmissible P (dateZero P I Z dateOneState))
    (h1 : TargetBankAdmissible P
      (dateOne P Z dateOneState recurrent tail)) :
    targetizedPrefix33 branch P I Z dateOneState recurrent tail = 0 ↔
      originalPrefix33 branch P I Z dateOneState recurrent tail = 0 := by
  rw [targetizedPrefix33_eq_fullEconomicBankShear
    branch P I Z dateOneState recurrent tail hmatch h0 h1]
  exact sourceTwoDateBankFiveRowShear_zero_iff
    _ _ _ _ _ _ _ _ _

#print axioms targetizedPrefix33_zero_iff_originalPrefix33_zero

/-- Pull the two-date economic targetization back to the true SOURCE
logarithmic coordinate chart, rather than an unrelated Python chart. -/
noncomputable def targetizedLogPrefix33
    (branch : LocalPrefixBranch) (P : Primitives S)
    (I : InheritedState) (Z0 : LocalPrefixCoordinates)
    (dateOneState recurrent : S)
    (tail : LocalPrefixContinuationRule)
    (z : Fin 33 → ℝ) : Fin 33 → ℝ :=
  targetizedPrefix33 branch P I (localPrefixLogChart Z0 z)
    dateOneState recurrent tail

/-- The explicit two-date targetization preserves the true SOURCE
positive-log chart root set. This DOES NOT assert a root exists. -/
theorem targetizedLogPrefix33_zero_iff_sourceLogPrefix33_zero
    (branch : LocalPrefixBranch) (P : Primitives S)
    (I : InheritedState) (Z0 : LocalPrefixCoordinates)
    (dateOneState recurrent : S)
    (tail : LocalPrefixContinuationRule)
    (z : Fin 33 → ℝ)
    (hmatch : P.matchingIntensity = Real.log 2)
    (h0 : TargetBankAdmissible P
      (dateZero P I (localPrefixLogChart Z0 z) dateOneState))
    (h1 : TargetBankAdmissible P
      (dateOne P (localPrefixLogChart Z0 z)
        dateOneState recurrent tail)) :
    targetizedLogPrefix33 branch P I Z0 dateOneState recurrent tail z = 0 ↔
      localReducedPrefixLogResidualVector branch P I Z0
        dateOneState recurrent tail z = 0 := by
  exact targetizedPrefix33_zero_iff_originalPrefix33_zero
    branch P I (localPrefixLogChart Z0 z) dateOneState recurrent tail
    hmatch h0 h1

#print axioms targetizedLogPrefix33_zero_iff_sourceLogPrefix33_zero

end CurrentSourceTwoDateBank
end Ventura26LiquidityAllocation
