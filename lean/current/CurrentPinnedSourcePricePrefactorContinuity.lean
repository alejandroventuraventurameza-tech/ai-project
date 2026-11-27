import Ventura26LiquidityAllocation.CurrentSourcePinnedAggregateOutputContinuity
import Ventura26LiquidityAllocation.CurrentSourcePinnedOutputDomain
import Ventura26LiquidityAllocation.CurrentSourcePinnedRateTargetContinuity
import Ventura26LiquidityAllocation.CurrentSourcePinnedOTCSlopes
import Ventura26LiquidityAllocation.CurrentSourceDepositPreSecantRegularity

/-!
# Actual pinned SOURCE bank-price prefactors: no continuity premises

The original two-date SOURCE aggregate output is continuous in its
33-dimensional stationary log chart, kernel-proven from the structural
firm labor/production formulas. Its stationary level and reference
are strictly positive. Those facts imply continuity of both log-output
terms and hence both TRUE monetary reserve-rate policy targets.

Combining the latter with kernel-proven continuity of all four OTC
slopes and the exact target-rate cancellation in deposit pricing
yields all FOUR economic pre-secant bank price coefficients continuous:
loan and deposit on each of the two actual SOURCE dates.

No HasFDerivAt F, no guessed Jacobian, and no source/Python identity.
The bank-BALANCE coefficients remain a separate regularity block.
-/

namespace Ventura26LiquidityAllocation
namespace CurrentPinnedSourcePricePrefactorContinuity

open CurrentSourceFullFDeriv
open CurrentPinnedBankDomain
open CurrentSourceCrossContinuity
open scoped Topology

/-- Both ORIGINAL SOURCE monetary rate targets are continuous at the
stationary log origin, for any fiscal fiber G. The previous two
log-output premises are discharged by original Cobb-Douglas continuity
and positive stationary output, not reintroduced as assumptions. -/
theorem pinned_two_genuine_rate_targets_continuousAt (G : ℝ) :
    ContinuousAt (fun z : Row33 =>
      sourceRateRuleTarget (ProposedStationaryPrimitives.primitives G)
        (pinnedDateZero G z)) (0 : Row33) ∧
    ContinuousAt (fun z : Row33 =>
      sourceRateRuleTarget (ProposedStationaryPrimitives.primitives G)
        (pinnedDateOne G z)) (0 : Row33) := by
  obtain ⟨hOutput0, hOutput1⟩ :=
    CurrentSourcePinnedAggregateOutputContinuity.
      pinned_two_actual_aggregate_outputs_continuousAt G
  obtain ⟨hLog0, hLog1⟩ :=
    CurrentSourcePinnedOutputDomain.
      pinned_two_output_logs_continuousAt_of_aggregate_outputs
        G hOutput0 hOutput1
  exact CurrentSourcePinnedRateTargetContinuity.
    pinned_two_rate_targets_continuousAt_of_log_output
      G hLog0 hLog1

#print axioms pinned_two_genuine_rate_targets_continuousAt

/-- Four economic banking PRICE prefactors, loan and deposit on both
genuine SOURCE dates, are continuous with NO extra regularity premise.
The underlying deposit denominator is positive on the source chart;
the OTC slope continuity comes from the two matching functions. -/
theorem pinned_four_bank_price_prefactors_continuousAt (G : ℝ) :
    (ContinuousAt (fun z : Row33 =>
      sourceLoanPreSecant (ProposedStationaryPrimitives.primitives G)
        (pinnedDateZero G z)) (0 : Row33) ∧
     ContinuousAt (fun z : Row33 =>
      sourceDepositPreSecant (ProposedStationaryPrimitives.primitives G)
        (pinnedDateZero G z)) (0 : Row33)) ∧
    (ContinuousAt (fun z : Row33 =>
      sourceLoanPreSecant (ProposedStationaryPrimitives.primitives G)
        (pinnedDateOne G z)) (0 : Row33) ∧
     ContinuousAt (fun z : Row33 =>
      sourceDepositPreSecant (ProposedStationaryPrimitives.primitives G)
        (pinnedDateOne G z)) (0 : Row33)) := by
  obtain ⟨hTarget0, hTarget1⟩ :=
    pinned_two_genuine_rate_targets_continuousAt G
  obtain ⟨hMinus0, hPlus0, hMinus1, hPlus1⟩ :=
    CurrentSourcePinnedOTCSlopes.pinned_four_frozen_OTC_slopes_continuousAt G
  obtain ⟨hDeposit0, hDeposit1⟩ :=
    CurrentSourceDepositPreSecantRegularity.
      pinned_two_deposit_preSecants_continuousAt
        G hTarget0 hMinus0 hPlus0 hTarget1 hMinus1 hPlus1
  have hLoan0 : ContinuousAt (fun z : Row33 =>
      sourceLoanPreSecant (ProposedStationaryPrimitives.primitives G)
        (pinnedDateZero G z)) (0 : Row33) := by
    simpa only [sourceLoanPreSecant] using hTarget0
  have hLoan1 : ContinuousAt (fun z : Row33 =>
      sourceLoanPreSecant (ProposedStationaryPrimitives.primitives G)
        (pinnedDateOne G z)) (0 : Row33) := by
    simpa only [sourceLoanPreSecant] using hTarget1
  exact ⟨⟨hLoan0, hDeposit0⟩, ⟨hLoan1, hDeposit1⟩⟩

#print axioms pinned_four_bank_price_prefactors_continuousAt

end CurrentPinnedSourcePricePrefactorContinuity
end Ventura26LiquidityAllocation
