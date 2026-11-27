import Ventura26LiquidityAllocation.CurrentSourceContinuous33Shear

/-!
# Actual SOURCE 33-row Fréchet targetization under CONTINUITY hypotheses

Earlier full two-date SOURCE transport in CurrentSourceTwoDateFDerivTransport
assumed a derivative of the state-dependent banking coefficient operator.
The generic SOURCE-index-exact theorem in CurrentSourceContinuous33Shear
now permits merely CONTINUITY of its eight scalar cross-coefficients.

This module specializes that theorem to the ACTUAL SOURCE original
33-log-row residual and independently targetized SOURCE economic rows:
  - the same economic primitives, inherited state, two dates, and tail;
  - the true log chart, not the legacy numerical surrogate;
  - the exact off-root SOURCE banking equality on an admissible neighborhood;
  - a common root, HasFDerivAt F J z0, and eight ContinuousAt hypotheses.

It does NOT prove economic continuity of the eight functions for the
stationary witness, HasFDerivAt of the original 33 economic equations,
source Jacobian invertibility, Python equality, or a full equilibrium.
-/

namespace Ventura26LiquidityAllocation
namespace CurrentSourceEconomicContinuousTransport

open Filter
open CurrentSourceFullFDeriv
open CurrentSourceTwoDateBank
open CurrentSourceContinuous33Shear
open CurrentSourceFiveBankBridge
open scoped Topology

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- Exact SOURCE economic 33-row derivative transport with E merely
continuous at a common root, expressed as eight economic cross
coefficient continuity hypotheses rather than HasFDerivAt E. -/
theorem targetizedLogPrefix33_hasFDerivAt_at_root_of_eight_continuous
    (branch : LocalPrefixBranch)
    (P : Primitives S) (I : InheritedState)
    (Z0 : LocalPrefixCoordinates)
    (dateOneState recurrent : S)
    (tail : LocalPrefixContinuationRule)
    (z0 : Row33) (J : Row33 →L[ℝ] Row33)
    (hmatch : P.matchingIntensity = Real.log 2)
    (hadm : ∀ᶠ z in 𝓝 z0,
      TargetBankAdmissible P
        (dateZero P I (localPrefixLogChart Z0 z) dateOneState) ∧
      TargetBankAdmissible P
        (dateOne P (localPrefixLogChart Z0 z)
          dateOneState recurrent tail))
    (hLoan0 : ContinuousAt
      (fun z => sourceLoanCross P
        (dateZero P I (localPrefixLogChart Z0 z) dateOneState)) z0)
    (hDeposit0 : ContinuousAt
      (fun z => sourceDepositCross P
        (dateZero P I (localPrefixLogChart Z0 z) dateOneState)) z0)
    (hLoan1 : ContinuousAt
      (fun z => sourceLoanCross P
        (dateOne P (localPrefixLogChart Z0 z) dateOneState recurrent tail)) z0)
    (hDeposit1 : ContinuousAt
      (fun z => sourceDepositCross P
        (dateOne P (localPrefixLogChart Z0 z) dateOneState recurrent tail)) z0)
    (hRate0 : ContinuousAt
      (fun z => sourceBalanceRateCross P
        (dateZero P I (localPrefixLogChart Z0 z) dateOneState)) z0)
    (hQuantity0 : ContinuousAt
      (fun z => sourceBalanceQuantityCross P
        (dateZero P I (localPrefixLogChart Z0 z) dateOneState)) z0)
    (hRate1 : ContinuousAt
      (fun z => sourceBalanceRateCross P
        (dateOne P (localPrefixLogChart Z0 z) dateOneState recurrent tail)) z0)
    (hQuantity1 : ContinuousAt
      (fun z => sourceBalanceQuantityCross P
        (dateOne P (localPrefixLogChart Z0 z) dateOneState recurrent tail)) z0)
    (hF : HasFDerivAt
      (localReducedPrefixLogResidualVector branch P I Z0
        dateOneState recurrent tail) J z0)
    (hroot :
      localReducedPrefixLogResidualVector branch P I Z0
        dateOneState recurrent tail z0 = 0) :
    HasFDerivAt
      (targetizedLogPrefix33 branch P I Z0
        dateOneState recurrent tail)
      ((economicLogShearCLM P I Z0
        dateOneState recurrent tail z0).comp J) z0 := by
  have hd :=
    dynamicBankShear33_hasFDerivAt_at_commonRoot
      (fun z => sourceLoanCross P
        (dateZero P I (localPrefixLogChart Z0 z) dateOneState))
      (fun z => sourceDepositCross P
        (dateZero P I (localPrefixLogChart Z0 z) dateOneState))
      (fun z => sourceLoanCross P
        (dateOne P (localPrefixLogChart Z0 z) dateOneState recurrent tail))
      (fun z => sourceDepositCross P
        (dateOne P (localPrefixLogChart Z0 z) dateOneState recurrent tail))
      (fun z => sourceBalanceRateCross P
        (dateZero P I (localPrefixLogChart Z0 z) dateOneState))
      (fun z => sourceBalanceQuantityCross P
        (dateZero P I (localPrefixLogChart Z0 z) dateOneState))
      (fun z => sourceBalanceRateCross P
        (dateOne P (localPrefixLogChart Z0 z) dateOneState recurrent tail))
      (fun z => sourceBalanceQuantityCross P
        (dateOne P (localPrefixLogChart Z0 z) dateOneState recurrent tail))
      (localReducedPrefixLogResidualVector branch P I Z0
        dateOneState recurrent tail)
      z0 J hLoan0 hDeposit0 hLoan1 hDeposit1
      hRate0 hQuantity0 hRate1 hQuantity1 hF hroot
  change HasFDerivAt
    (targetizedLogPrefix33 branch P I Z0
      dateOneState recurrent tail)
    ((sourceShearCLM
      (sourceLoanCross P
        (dateZero P I (localPrefixLogChart Z0 z0) dateOneState))
      (sourceDepositCross P
        (dateZero P I (localPrefixLogChart Z0 z0) dateOneState))
      (sourceLoanCross P
        (dateOne P (localPrefixLogChart Z0 z0)
          dateOneState recurrent tail))
      (sourceDepositCross P
        (dateOne P (localPrefixLogChart Z0 z0)
          dateOneState recurrent tail))
      (sourceBalanceRateCross P
        (dateZero P I (localPrefixLogChart Z0 z0) dateOneState))
      (sourceBalanceQuantityCross P
        (dateZero P I (localPrefixLogChart Z0 z0) dateOneState))
      (sourceBalanceRateCross P
        (dateOne P (localPrefixLogChart Z0 z0)
          dateOneState recurrent tail))
      (sourceBalanceQuantityCross P
        (dateOne P (localPrefixLogChart Z0 z0)
          dateOneState recurrent tail))).comp J) z0
  apply hd.congr_of_eventuallyEq
  filter_upwards [hadm] with z hz
  exact targetizedPrefix33_eq_fullEconomicBankShear
    branch P I (localPrefixLogChart Z0 z)
    dateOneState recurrent tail hmatch hz.1 hz.2

#print axioms targetizedLogPrefix33_hasFDerivAt_at_root_of_eight_continuous

end CurrentSourceEconomicContinuousTransport
end Ventura26LiquidityAllocation
