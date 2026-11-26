import Ventura26LiquidityAllocation.CurrentSourceTwoDateBankTargetization
import Mathlib.Analysis.Calculus.FDeriv.CompCLM

/-!
# Fréchet transport for the actual SOURCE two-date 33-row targetization

The operator below is the continuous linear realization of the exact
33-row economic shear established in CurrentSourceTwoDateBankTargetization.
We prove an exact derivative-transport statement *conditional* on
differentiability, a common root, and eventual SOURCE banking admissibility.

Nothing here asserts an economic root exists or proves that the numerical
Python auxiliary equals the SOURCE residual.
-/

namespace Ventura26LiquidityAllocation
namespace CurrentSourceFullFDeriv

open CurrentSourceTwoDateBank
open CurrentSourceFiveBankBridge
open Filter
open scoped Topology

abbrev Row33 := Fin 33 → ℝ

/-- General multivariate operator-valued product rule at a root.
The derivative of the state-dependent operator cancels when the
residual vector itself vanishes. -/
theorem clm_apply_hasFDerivAt_at_zero
    {X Y : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (A : X → Y →L[ℝ] Y) (F : X → Y)
    (x : X) (A' : X →L[ℝ] (Y →L[ℝ] Y))
    (F' : X →L[ℝ] Y)
    (hA : HasFDerivAt A A' x)
    (hF : HasFDerivAt F F' x)
    (hzero : F x = 0) :
    HasFDerivAt (fun z => A z (F z)) ((A x).comp F') x := by
  have h := hA.clm_apply hF
  simpa [hzero] using h

#print axioms clm_apply_hasFDerivAt_at_zero

/-- Coordinate projection as a continuous linear functional. -/
noncomputable def rowCoord (i : Fin 33) : Row33 →L[ℝ] ℝ :=
  ContinuousLinearMap.proj i

/-- The genuinely linear map underlying the six SOURCE bank-row
changes, with eight state-dependent coefficients (four per date).
The other 27 rows and both dates' monetary policy rows are fixed. -/
noncomputable def sourceShearCLM
    (loan0 deposit0 loan1 deposit1
      rate0 quantity0 rate1 quantity1 : ℝ) :
    Row33 →L[ℝ] Row33 :=
  ContinuousLinearMap.pi (fun i =>
    if i = 14 then rowCoord 14 + loan0 • rowCoord 12
    else if i = 15 then rowCoord 15 + deposit0 • rowCoord 12
    else if i = 16 then
      rowCoord 16 + rate0 • rowCoord 12 + quantity0 • rowCoord 13
    else if i = 30 then rowCoord 30 + loan1 • rowCoord 28
    else if i = 31 then rowCoord 31 + deposit1 • rowCoord 28
    else if i = 32 then
      rowCoord 32 + rate1 • rowCoord 28 + quantity1 • rowCoord 29
    else rowCoord i)

/-- The linear operator is definitionally tied to the actual SOURCE
33-row shear; no alternative row order or Python normalization. -/
theorem sourceShearCLM_apply
    (loan0 deposit0 loan1 deposit1
      rate0 quantity0 rate1 quantity1 : ℝ)
    (v : Row33) :
    sourceShearCLM loan0 deposit0 loan1 deposit1
      rate0 quantity0 rate1 quantity1 v =
    sourceTwoDateBankFiveRowShear loan0 deposit0 loan1 deposit1
      rate0 quantity0 rate1 quantity1 v := by
  funext i
  fin_cases i <;>
    simp [sourceShearCLM, rowCoord, sourceTwoDateBankFiveRowShear,
      sourceTwoDateBankPricingRowShear,
      sourceTwoDateMonetaryBankRowShear,
      sourceDateOneMonetaryBankRowShear,
      sourceMonetaryBankRowShear] <;> ring

#print axioms sourceShearCLM_apply

/-- The concrete row-shear linear operator never creates a zero.
This is a property of the row operation, not of any Jacobian. -/
theorem sourceShearCLM_zero_iff
    (loan0 deposit0 loan1 deposit1
      rate0 quantity0 rate1 quantity1 : ℝ) (v : Row33) :
    sourceShearCLM loan0 deposit0 loan1 deposit1
      rate0 quantity0 rate1 quantity1 v = 0 ↔ v = 0 := by
  rw [sourceShearCLM_apply]
  exact sourceTwoDateBankFiveRowShear_zero_iff
    loan0 deposit0 loan1 deposit1 rate0 quantity0 rate1 quantity1 v

#print axioms sourceShearCLM_zero_iff

/-- True SOURCE log-chart operator with eight economic coefficients,
not a frozen illustrative Jacobian. -/
noncomputable def economicLogShearCLM
    {S : Type*} [Fintype S] [DecidableEq S]
    (P : Primitives S) (I : InheritedState)
    (Z0 : LocalPrefixCoordinates) (dateOneState recurrent : S)
    (tail : LocalPrefixContinuationRule) (z : Row33) :
    Row33 →L[ℝ] Row33 :=
  let Z := localPrefixLogChart Z0 z
  let d0 := dateZero P I Z dateOneState
  let d1 := dateOne P Z dateOneState recurrent tail
  sourceShearCLM
    (sourceLoanCross P d0) (sourceDepositCross P d0)
    (sourceLoanCross P d1) (sourceDepositCross P d1)
    (sourceBalanceRateCross P d0) (sourceBalanceQuantityCross P d0)
    (sourceBalanceRateCross P d1) (sourceBalanceQuantityCross P d1)

/-- Exact equality with the 33-row SOURCE targetization, conditional
on the original two-date matching/domain assumptions. -/
theorem targetizedLogPrefix33_eq_economicLogShear
    {S : Type*} [Fintype S] [DecidableEq S]
    (branch : LocalPrefixBranch) (P : Primitives S)
    (I : InheritedState) (Z0 : LocalPrefixCoordinates)
    (dateOneState recurrent : S)
    (tail : LocalPrefixContinuationRule) (z : Row33)
    (hmatch : P.matchingIntensity = Real.log 2)
    (h0 : TargetBankAdmissible P
      (dateZero P I (localPrefixLogChart Z0 z) dateOneState))
    (h1 : TargetBankAdmissible P
      (dateOne P (localPrefixLogChart Z0 z) dateOneState recurrent tail)) :
    targetizedLogPrefix33 branch P I Z0 dateOneState recurrent tail z =
      economicLogShearCLM P I Z0 dateOneState recurrent tail z
        (localReducedPrefixLogResidualVector branch P I Z0
          dateOneState recurrent tail z) := by
  change
    targetizedPrefix33 branch P I (localPrefixLogChart Z0 z)
      dateOneState recurrent tail =
    economicLogShearCLM P I Z0 dateOneState recurrent tail z
      (originalPrefix33 branch P I (localPrefixLogChart Z0 z)
        dateOneState recurrent tail)
  rw [targetizedPrefix33_eq_fullEconomicBankShear
    branch P I (localPrefixLogChart Z0 z)
    dateOneState recurrent tail hmatch h0 h1]
  exact (sourceShearCLM_apply _ _ _ _ _ _ _ _ _).symm

#print axioms targetizedLogPrefix33_eq_economicLogShear

/-- CONDITIONAL differentiation of the genuine SOURCE 33-row vector.
The coefficient-map and the SOURCE residual must have Fréchet
derivatives at the same root. Crucially, two-date banking admissibility
must hold on a neighborhood, not only at the point. -/
theorem targetizedLogPrefix33_hasFDerivAt_at_source_root
    {S : Type*} [Fintype S] [DecidableEq S]
    (branch : LocalPrefixBranch) (P : Primitives S)
    (I : InheritedState) (Z0 : LocalPrefixCoordinates)
    (dateOneState recurrent : S)
    (tail : LocalPrefixContinuationRule) (z0 : Row33)
    (J : Row33 →L[ℝ] Row33)
    (dA : Row33 →L[ℝ] (Row33 →L[ℝ] Row33))
    (hmatch : P.matchingIntensity = Real.log 2)
    (hadm : ∀ᶠ z in 𝓝 z0,
      TargetBankAdmissible P
        (dateZero P I (localPrefixLogChart Z0 z) dateOneState) ∧
      TargetBankAdmissible P
        (dateOne P (localPrefixLogChart Z0 z)
          dateOneState recurrent tail))
    (hA : HasFDerivAt
      (economicLogShearCLM P I Z0 dateOneState recurrent tail) dA z0)
    (hF : HasFDerivAt
      (localReducedPrefixLogResidualVector branch P I Z0
        dateOneState recurrent tail) J z0)
    (hroot :
      localReducedPrefixLogResidualVector branch P I Z0
        dateOneState recurrent tail z0 = 0) :
    HasFDerivAt
      (targetizedLogPrefix33 branch P I Z0 dateOneState recurrent tail)
      ((economicLogShearCLM P I Z0 dateOneState recurrent tail z0).comp J)
      z0 := by
  have hprod := clm_apply_hasFDerivAt_at_zero
    (economicLogShearCLM P I Z0 dateOneState recurrent tail)
    (localReducedPrefixLogResidualVector branch P I Z0
      dateOneState recurrent tail)
    z0 dA J hA hF hroot
  apply hprod.congr_of_eventuallyEq
  filter_upwards [hadm] with z hz
  exact (targetizedLogPrefix33_eq_economicLogShear
    branch P I Z0 dateOneState recurrent tail z
    hmatch hz.1 hz.2

#print axioms targetizedLogPrefix33_hasFDerivAt_at_source_root

end CurrentSourceFullFDeriv
end Ventura26LiquidityAllocation
