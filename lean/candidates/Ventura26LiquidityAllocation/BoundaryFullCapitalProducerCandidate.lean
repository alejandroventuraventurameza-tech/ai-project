import Ventura26LiquidityAllocation.BoundaryFullSettlementCandidate

/-!
# SOURCE all-date productive capital accounts

This module isolates the remaining strict physical-capital and investment
signs needed for the original source CapitalProducerAccounts predicate.
Unlike a mere algebraic aggregate-production equality, the original
predicate requires installed aggregate capital > 0 and investment >= 0.

The transient capital is scaled by the unique certified SOURCE rate, while
dates one and later use the stationary installed capital. The exact
capital-law bridge is imported from BoundaryFullResourceClearingCandidate.
No private optimality, equilibrium existence or dynamic growth is asserted.
-/

namespace Ventura26LiquidityAllocation
namespace ProposedBoundaryCapitalProducer

open ProposedStationaryRealScale
open ProposedBoundaryResourceRoot
open ProposedBoundaryFullPrefix
open ProposedBoundaryNormalizationBridge
open ProposedBoundaryFullAllocationCarrier
open ProposedBoundaryFullBankBalance
open ProposedBoundaryFullResourceClearing

/-- Positive installed capital for each firm at every SOURCE date. -/
theorem sourceBoundaryDateData_currentCapital_pos (G : ℝ) :
    ∀ t (i : FirmType), 0 < (sourceBoundaryDateData G t).currentCapital i := by
  intro t i
  cases t with
  | zero =>
      rw [sourceBoundaryDateData_zero]
      change 0 < boundaryCapital boundarySourceRate i
      rcases boundarySourceRate_positiveRealDomain with
        ⟨_hLoan, _hReserve, _hDeposit, hScale, _hScaleUpper, _hInvestment⟩
      unfold boundaryCapital
      exact mul_pos hScale (capital_pos i)
  | succ t =>
      cases t with
      | zero =>
          rw [sourceBoundaryDateData_one, boundary_oneData_fields]
          change 0 < capital i
          exact capital_pos i
      | succ n =>
          change 0 < (sourceBoundaryDateData G (n + 2)).currentCapital i
          rw [sourceBoundaryDateData_tail G n]
          exact capital_pos i

/-- Date-data mass-weighted installed capital is positive at every date. -/
theorem sourceBoundaryDateData_aggregateCapital_pos (G : ℝ) :
    ∀ t, 0 < localPrefixAggregateCapital
      (boundaryPrimitives G boundarySourceRate)
      (sourceBoundaryDateData G t).currentCapital := by
  intro t
  have hH := sourceBoundaryDateData_currentCapital_pos G t .H
  have hL := sourceBoundaryDateData_currentCapital_pos G t .L
  unfold localPrefixAggregateCapital
  rw [sum_firmType_eq_H_add_L]
  change 0 < (1 / 2 : ℝ) * (sourceBoundaryDateData G t).currentCapital .H +
    (1 / 2 : ℝ) * (sourceBoundaryDateData G t).currentCapital .L
  exact add_pos (mul_pos (by norm_num) hH)
    (mul_pos (by norm_num) hL)

/-- Exact boundary date-zero aggregate investment equals the SOURCE
scalar construction. Hence its sign is obtained from the certified
positive investment bracket, not a rounded simulation. -/
theorem sourceBoundaryDateData_zero_investment_eq (G : ℝ) :
    localPrefixInvestment
      (boundaryPrimitives G boundarySourceRate)
      (sourceBoundaryDateData G 0) =
    boundaryInvestment boundarySourceRate := by
  rw [sourceBoundaryDateData_zero]
  have hcurrent :
      localPrefixAggregateCapital
        (boundaryPrimitives G boundarySourceRate)
        (boundaryZeroData G boundarySourceRate).currentCapital =
      boundaryAggregateCapital boundarySourceRate := by
    unfold localPrefixAggregateCapital
    rw [sum_firmType_eq_H_add_L]
    change (1 / 2 : ℝ) * boundaryCapital boundarySourceRate .H +
      (1 / 2 : ℝ) * boundaryCapital boundarySourceRate .L =
      boundaryAggregateCapital boundarySourceRate
    unfold boundaryAggregateCapital boundaryCapital aggregateCapital average
    ring
  have hnext :
      localPrefixAggregateCapital
        (boundaryPrimitives G boundarySourceRate)
        (boundaryZeroData G boundarySourceRate).nextCapital =
      aggregateCapital := by
    unfold localPrefixAggregateCapital
    rw [sum_firmType_eq_H_add_L]
    change (1 / 2 : ℝ) * capital .H + (1 / 2 : ℝ) * capital .L =
      aggregateCapital
    unfold aggregateCapital average
    ring
  unfold localPrefixInvestment
  rw [hnext, hcurrent]
  change aggregateCapital - (1 - (1 / 40 : ℝ)) *
    boundaryAggregateCapital boundarySourceRate =
      boundaryInvestment boundarySourceRate
  unfold boundaryInvestment
  ring

/-- The stationary block has strictly positive investment because the
identical next-period capital stock replaces depreciated current capital. -/
theorem sourceBoundaryDateData_stationary_investment_pos (G : ℝ) :
    0 < localPrefixInvestment
      (boundaryPrimitives G boundarySourceRate) dateData := by
  have hK := aggregates_pos.1
  have hsum :
      localPrefixAggregateCapital
        (boundaryPrimitives G boundarySourceRate) capital =
        aggregateCapital := by
    unfold localPrefixAggregateCapital
    rw [sum_firmType_eq_H_add_L]
    change (1 / 2 : ℝ) * capital .H + (1 / 2 : ℝ) * capital .L =
      aggregateCapital
    unfold aggregateCapital average
    ring
  change localPrefixAggregateCapital
      (boundaryPrimitives G boundarySourceRate) capital -
    (1 - (1 / 40 : ℝ)) * localPrefixAggregateCapital
      (boundaryPrimitives G boundarySourceRate) capital > 0
  rw [hsum]
  nlinarith

/-- Investment remains strictly positive on the one-date perturbation
and the stationary tail; this does not imply private optimality. -/
theorem sourceBoundaryDateData_investment_pos (G : ℝ) :
    ∀ t, 0 < localPrefixInvestment
      (boundaryPrimitives G boundarySourceRate)
      (sourceBoundaryDateData G t) := by
  have hzero := sourceBoundaryDateData_zero_investment_eq G
  have hstationary := sourceBoundaryDateData_stationary_investment_pos G
  intro t
  cases t with
  | zero =>
      rw [hzero]
      rcases boundarySourceRate_positiveRealDomain with
        ⟨_hLoan, _hReserve, _hDeposit, _hScale, _hScaleUpper, hInvestment⟩
      exact hInvestment
  | succ t =>
      cases t with
      | zero =>
          simpa [sourceBoundaryDateData_one, boundary_oneData_fields]
            using hstationary
      | succ n =>
          change 0 < localPrefixInvestment
            (boundaryPrimitives G boundarySourceRate)
            (sourceBoundaryDateData G (n + 2))
          rw [sourceBoundaryDateData_tail G n]
          exact hstationary

/-- The source's literal inherited/installed capital in every history
coincides with the mass-weighted current date-data capital. -/
theorem sourceBoundary_sourceAggregateCapital_eq (G : ℝ) :
    ∀ t (h : History LocalBridgePhase t),
      sourceAggregateCapital
        (boundaryPrimitives G boundarySourceRate)
        (boundaryInitialState G boundarySourceRate)
        (localSlackSettlementAllocation
          (boundaryPrimitives G boundarySourceRate)
          (sourceBoundaryDateData G)) t h =
      localPrefixAggregateCapital
        (boundaryPrimitives G boundarySourceRate)
        (sourceBoundaryDateData G t).currentCapital := by
  intro t h
  cases t with
  | zero =>
      change (∑ i, (boundaryPrimitives G boundarySourceRate).mass i *
        (boundaryInitialState G boundarySourceRate).capital i) =
        ∑ i, (boundaryPrimitives G boundarySourceRate).mass i *
          (sourceBoundaryDateData G 0).currentCapital i
      apply Finset.sum_congr rfl
      intro i _hi
      rw [sourceBoundaryDateData_initial_capital G i]
  | succ t =>
      change (∑ i, (boundaryPrimitives G boundarySourceRate).mass i *
        (sourceBoundaryDateData G t).nextCapital i) =
        ∑ i, (boundaryPrimitives G boundarySourceRate).mass i *
          (sourceBoundaryDateData G (t + 1)).currentCapital i
      apply Finset.sum_congr rfl
      intro i _hi
      rw [sourceBoundaryDateData_capital_step G t i]

/-- Source investment computed from the literal Allocation's installed
capital satisfies the date-data investment identity. -/
theorem sourceBoundary_sourceInvestment_eq (G : ℝ) :
    ∀ t (h : History LocalBridgePhase t),
      sourceInvestment
        (boundaryPrimitives G boundarySourceRate)
        (boundaryInitialState G boundarySourceRate)
        (localSlackSettlementAllocation
          (boundaryPrimitives G boundarySourceRate)
          (sourceBoundaryDateData G)) t h =
      localPrefixInvestment
        (boundaryPrimitives G boundarySourceRate)
        (sourceBoundaryDateData G t) := by
  intro t h
  change (∑ i, (boundaryPrimitives G boundarySourceRate).mass i *
      (sourceBoundaryDateData G t).nextCapital i) -
    (1 - (boundaryPrimitives G boundarySourceRate).depreciation) *
      sourceAggregateCapital
        (boundaryPrimitives G boundarySourceRate)
        (boundaryInitialState G boundarySourceRate)
        (localSlackSettlementAllocation
          (boundaryPrimitives G boundarySourceRate)
          (sourceBoundaryDateData G)) t h =
    localPrefixInvestment
      (boundaryPrimitives G boundarySourceRate)
      (sourceBoundaryDateData G t)
  rw [sourceBoundary_sourceAggregateCapital_eq G t h]
  rfl

/-- Literal capital-producer technology, positive installed capital and
nonnegative investment hold at all admitted histories. This supplements
AggregateProduction, CapitalClears, AccountingIdentities, and ResourceClears;
none implies CapitalProducerOptimal. -/
theorem sourceBoundaryLiteralAllocation_capitalProducerAccounts (G : ℝ) :
    CapitalProducerAccounts
      (boundaryPrimitives G boundarySourceRate)
      (sourceBoundaryLiteralAllocation G) := by
  let P := boundaryPrimitives G boundarySourceRate
  let I := boundaryInitialState G boundarySourceRate
  let B := localSlackSettlementAllocation P (sourceBoundaryDateData G)
  have hK : ∀ t (h : History LocalBridgePhase t),
      FirmHistoryAdmissible P t h →
      0 < sourceAggregateCapital P I B t h := by
    intro t h _hs
    rw [sourceBoundary_sourceAggregateCapital_eq G t h]
    exact sourceBoundaryDateData_aggregateCapital_pos G t
  have hI : ∀ t (h : History LocalBridgePhase t),
      FirmHistoryAdmissible P t h →
      0 ≤ sourceInvestment P I B t h := by
    intro t h _hs
    rw [sourceBoundary_sourceInvestment_eq G t h]
    exact le_of_lt (sourceBoundaryDateData_investment_pos G t)
  change CapitalProducerAccounts P
    (withSourceFiscalAccounts P I (withSourceRealAccounts P I B))
  exact (withSourceFiscalAccounts_preserves_capitalProducerAccounts
    P I (withSourceRealAccounts P I B)).2
    (withSourceRealAccounts_capitalProducerAccounts P I B hK hI)

#print axioms sourceBoundaryDateData_currentCapital_pos
#print axioms sourceBoundaryDateData_aggregateCapital_pos
#print axioms sourceBoundaryDateData_zero_investment_eq
#print axioms sourceBoundaryDateData_stationary_investment_pos
#print axioms sourceBoundaryDateData_investment_pos
#print axioms sourceBoundary_sourceAggregateCapital_eq
#print axioms sourceBoundary_sourceInvestment_eq
#print axioms sourceBoundaryLiteralAllocation_capitalProducerAccounts

end ProposedBoundaryCapitalProducer
end Ventura26LiquidityAllocation
