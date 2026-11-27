import Ventura26LiquidityAllocation.CurrentPinnedEightEconomicPrefactorContinuity
import Ventura26LiquidityAllocation.CurrentPinnedMonetaryDonorContinuity
import Ventura26LiquidityAllocation.CurrentSourceEconomicContinuousTransport
import Ventura26LiquidityAllocation.CurrentPinnedLocalNeighborhood

/-!
# SOURCE: eight actual bank shear coefficients continuous without F derivative

The SOURCE original 33-log-residual is exactly zero at the
two-date stationary binding root; its rate and quantity monetary donor
residuals also vanish exactly (PR #52).

The four donor monetary functions are themselves continuous directly
from the original log(realized/target) policy equations; no assumption
of HasFDerivAt F is needed for this. The eight economic pre-secant
bank coefficients are continuous directly from actual SOURCE payment
and bank ratio formulas; the continuous expSecant then yields
all EIGHT actual state-dependent bank shear cross coefficients.

Consequently the derivative transport for the exact SOURCE 33×33
targetization at the stationary root requires only ONE substantive
regularity premise: HasFDerivAt of the original economic F. All
root, matching, local bank domain and cross-coefficient premises are
discharged by independent kernel-proven theorems.

This module does NOT prove that remaining F premise, an inverse
Jacobian, the 34-row dual-zero branch or any infinite equilibrium.
-/

namespace Ventura26LiquidityAllocation
namespace CurrentPinnedCrossAndFrechetOnlyF

open CurrentSourceFullFDeriv
open CurrentSourceTwoDateBank
open CurrentSourceFiveBankBridge
open CurrentPinnedBankDomain
open CurrentPinnedEightCrossContinuity
open CurrentSourceCrossContinuity
open scoped Topology

/-- Continuity of ALL EIGHT genuine bank cross coefficients at the
binding stationary SOURCE log origin, with NO differentiability
assumption on the original 33-row economic residual F. -/
theorem pinned_eight_economic_bank_crosses_continuousAt (G : ℝ) :
    FourCrossContinuousAt G (pinnedDateZero G) ∧
      FourCrossContinuousAt G (pinnedDateOne G) := by
  let P := ProposedStationaryPrimitives.primitives G
  obtain ⟨hp0, hp1⟩ :=
    CurrentPinnedEightEconomicPrefactorContinuity.
      pinned_eight_preSecants_continuousAt G
  obtain ⟨⟨hPolicyRate0, hPolicyQuantity0⟩,
      ⟨hPolicyRate1, hPolicyQuantity1⟩⟩ :=
    CurrentPinnedMonetaryDonorContinuity.
      pinned_four_actual_monetary_donors_continuousAt G
  obtain ⟨hZeroRate0, hZeroQuantity0, hZeroRate1, hZeroQuantity1⟩ :=
    CurrentPinnedMonetaryRoots.pinned_four_monetary_donor_rows_zero G
  rcases hp0 with ⟨hLoan0, hDeposit0, hBalanceRate0, hBalanceQuantity0⟩
  rcases hp1 with ⟨hLoan1, hDeposit1, hBalanceRate1, hBalanceQuantity1⟩
  exact ⟨
    sourceFourCross_continuousAt_of_prefactors
      P (pinnedDateZero G) (0 : Row33)
      hLoan0 hDeposit0 hBalanceRate0 hBalanceQuantity0
      hPolicyRate0 hPolicyQuantity0 hZeroRate0 hZeroQuantity0,
    sourceFourCross_continuousAt_of_prefactors
      P (pinnedDateOne G) (0 : Row33)
      hLoan1 hDeposit1 hBalanceRate1 hBalanceQuantity1
      hPolicyRate1 hPolicyQuantity1 hZeroRate1 hZeroQuantity1⟩

#print axioms pinned_eight_economic_bank_crosses_continuousAt

/-- Actual SOURCE 33-row Fréchet transport at the pinned binding root:
ALL scalar-shear continuity, the 33-row ROOT, matching, and the bank
admissible neighborhood are now discharged. The only additional
hypothesis is genuine HasFDerivAt of ORIGINAL SOURCE F.

The derivative is the original J LEFT-MULTIPLIED by the exact
invertible economic triangular bank shear E at the same root.
No claim that this Jacobian J is nonsingular or numerically enclosed. -/
theorem pinned_targetized_hasFDerivAt_of_original_F
    (G : ℝ) (J : Row33 →L[ℝ] Row33)
    (hF : HasFDerivAt
      (CurrentPinnedEightCrossContinuity.pinnedOriginalF G)
      J (0 : Row33)) :
    HasFDerivAt
      (targetizedLogPrefix33 .binding
        (ProposedStationaryPrimitives.primitives G)
        (ProposedStationaryInheritedState.inheritedState G)
        fullyPinnedStationarySOURCEZ0 .dateOne .recurrent
        (sourceLogLinearContinuation
          ProposedStationaryRealScale.stateSix
          ProposedStationaryRealScale.controls
          sourceFrozenP0TenControls))
      ((economicLogShearCLM
        (ProposedStationaryPrimitives.primitives G)
        (ProposedStationaryInheritedState.inheritedState G)
        fullyPinnedStationarySOURCEZ0 .dateOne .recurrent
        (sourceLogLinearContinuation
          ProposedStationaryRealScale.stateSix
          ProposedStationaryRealScale.controls
          sourceFrozenP0TenControls)
        (0 : Row33)).comp J) (0 : Row33) := by
  obtain ⟨hc0, hc1⟩ :=
    pinned_eight_economic_bank_crosses_continuousAt G
  rcases hc0 with ⟨hLoan0, hDeposit0, hRate0, hQuantity0⟩
  rcases hc1 with ⟨hLoan1, hDeposit1, hRate1, hQuantity1⟩
  apply CurrentSourceEconomicContinuousTransport.
    targetizedLogPrefix33_hasFDerivAt_at_root_of_eight_continuous
      .binding
      (ProposedStationaryPrimitives.primitives G)
      (ProposedStationaryInheritedState.inheritedState G)
      fullyPinnedStationarySOURCEZ0 .dateOne .recurrent
      (sourceLogLinearContinuation
        ProposedStationaryRealScale.stateSix
        ProposedStationaryRealScale.controls
        sourceFrozenP0TenControls)
      (0 : Row33) J
  · rfl
  · simpa only [pinnedDateZero, pinnedDateOne] using
      CurrentPinnedLocalNeighborhood.pinned_banking_admissible_eventually G
  · exact hLoan0
  · exact hDeposit0
  · exact hLoan1
  · exact hDeposit1
  · exact hRate0
  · exact hQuantity0
  · exact hRate1
  · exact hQuantity1
  · simpa only [CurrentPinnedEightCrossContinuity.pinnedOriginalF] using hF
  · exact CurrentPinnedStationaryRoot.pinned_stationary_binding_prefix33_root G

#print axioms pinned_targetized_hasFDerivAt_of_original_F

end CurrentPinnedCrossAndFrechetOnlyF
end Ventura26LiquidityAllocation
