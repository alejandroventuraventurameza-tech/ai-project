import Ventura26LiquidityAllocation.BoundaryFullRealAccountingCandidate

/-!
# Full literal resource clearing at the SOURCE frontier

The SOURCE scalar root and two-date reduced prefix are kernel-verified.
This module connects the reduced resource row to literal history-indexed
production and investment by explicitly proving installed-capital continuity
and aggregate-productivity alignment. An all-date resource identity is stronger
than an F_r(Z,v) row, but is still not household, firm or bank optimality,
a fiscal budget, or a complete competitive equilibrium.

No sorry, admit or new axiom is permitted.
-/

namespace Ventura26LiquidityAllocation
namespace ProposedBoundaryFullResourceClearing

open ProposedStationaryRealScale
open ProposedStationaryReducedSystem
open ProposedBoundaryFullPrefix
open ProposedBoundaryNormalizationBridge
open ProposedBoundaryFullAllocationCarrier
open ProposedBoundaryFullBankBalance
open ProposedBoundaryRealAccounting

/-- Each date in the literal SOURCE carrier obeys the exact reduced
resource equation, first at the frontier, then in the announced date-one
block, and thereafter in the stationary reduced system. -/
theorem sourceBoundaryDateData_resource_row (G : ℝ) :
    ∀ t, localReducedRemainingResidual
      (boundaryPrimitives G boundarySourceRate)
      (sourceBoundaryDateData G t) 2 = 0 := by
  intro t
  cases t with
  | zero =>
      rw [sourceBoundaryDateData_zero]
      have h := (boundarySourceRate_reduced_prefix
        G LocalPrefixBranch.slack) LocalPrefixEquation.resourcesZero
      change localReducedRemainingResidual
        (boundaryPrimitives G boundarySourceRate)
        (localPrefixDateZeroData
          (boundaryPrimitives G boundarySourceRate)
          (boundaryInitialState G boundarySourceRate)
          (boundaryCoordinates boundarySourceRate) .dateOne) 2 = 0 at h
      simpa only [boundary_dateZeroData_eq] using h
  | succ t =>
      cases t with
      | zero =>
          rw [sourceBoundaryDateData_one]
          have h := (boundarySourceRate_reduced_prefix
            G LocalPrefixBranch.slack) LocalPrefixEquation.resourcesOne
          change localReducedRemainingResidual
            (boundaryPrimitives G boundarySourceRate)
            (boundaryOneData G boundarySourceRate) 2 = 0 at h
          exact h
      | succ n =>
          change localReducedRemainingResidual
            (boundaryPrimitives G boundarySourceRate)
            (sourceBoundaryDateData G (n + 2)) 2 = 0
          rw [sourceBoundaryDateData_tail G n]
          exact (stationary_reduced_system
            (boundaryPrimitives G boundarySourceRate)
            (boundary_stationary_parameters G boundarySourceRate)
            0 1 (boundary_binary_payment_law G boundarySourceRate)).1
              (2 : Fin 11)

/-- The first installed capital equals the SOURCE inherited capital. -/
theorem sourceBoundaryDateData_initial_capital (G : ℝ) (i : FirmType) :
    (boundaryInitialState G boundarySourceRate).capital i =
      (sourceBoundaryDateData G 0).currentCapital i := by
  rw [sourceBoundaryDateData_zero]
  rfl

/-- Each next-period capital plan is precisely the next date's installed
capital, including the zero-one boundary and the stationary transition. -/
theorem sourceBoundaryDateData_capital_step (G : ℝ) (t : ℕ)
    (i : FirmType) :
    (sourceBoundaryDateData G t).nextCapital i =
      (sourceBoundaryDateData G (t + 1)).currentCapital i := by
  cases t with
  | zero =>
      rw [sourceBoundaryDateData_zero, sourceBoundaryDateData_one]
      rfl
  | succ t =>
      cases t with
      | zero =>
          change (sourceBoundaryDateData G 1).nextCapital i =
            (sourceBoundaryDateData G 2).currentCapital i
          rw [sourceBoundaryDateData_one, sourceBoundaryDateData_tail G 0]
          rfl
      | succ n =>
          change (sourceBoundaryDateData G (n + 2)).nextCapital i =
            (sourceBoundaryDateData G ((n + 1) + 2)).currentCapital i
          rw [sourceBoundaryDateData_tail G n,
            sourceBoundaryDateData_tail G (n + 1)]
          rfl

/-- The literal date data use unit aggregate productivity at all dates. -/
theorem sourceBoundaryDateData_unit_productivity (G : ℝ) (t : ℕ) :
    (sourceBoundaryDateData G t).currentAggregateProductivity = 1 := by
  cases t with
  | zero =>
      rw [sourceBoundaryDateData_zero]
      rfl
  | succ t =>
      cases t with
      | zero =>
          rw [sourceBoundaryDateData_one]
          rfl
      | succ n =>
          change (sourceBoundaryDateData G (n + 2)).currentAggregateProductivity = 1
          rw [sourceBoundaryDateData_tail G n]
          rfl

/-- Abstract bridge from reduced row two to all-date SOURCE resources.
The two capital-continuity premises are essential: a vector residual
without matching installed stocks does not imply literal market clearing. -/
theorem literal_resourceClears_of_aligned_reduced_rows
    (P : Primitives LocalBridgePhase) (I : InheritedState)
    (d : ℕ → LocalPrefixDateData)
    (hinit : ∀ i, I.capital i = (d 0).currentCapital i)
    (hstep : ∀ t i, (d t).nextCapital i = (d (t + 1)).currentCapital i)
    (hprod : ∀ s, P.aggregateProductivity s = 1)
    (hdateProd : ∀ t, (d t).currentAggregateProductivity = 1)
    (hrows : ∀ t, localReducedRemainingResidual P (d t) 2 = 0) :
    ResourceClears P (localSlackLiteralAllocation P I d) := by
  let B := localSlackSettlementAllocation P d
  have hcapital : ∀ t (h : History LocalBridgePhase t),
      sourceAggregateCapital P I B t h =
        localPrefixAggregateCapital P (d t).currentCapital := by
    intro t h
    cases t with
    | zero =>
        change (∑ i, P.mass i * I.capital i) =
          ∑ i, P.mass i * (d 0).currentCapital i
        apply Finset.sum_congr rfl
        intro i _hi
        rw [hinit i]
    | succ t =>
        change (∑ i, P.mass i * (d t).nextCapital i) =
          ∑ i, P.mass i * (d (t + 1)).currentCapital i
        apply Finset.sum_congr rfl
        intro i _hi
        rw [hstep t i]
  have houtput : ∀ t (h : History LocalBridgePhase t),
      sourceAggregateOutput P I B t h =
        localPrefixAggregateOutput P (d t) := by
    intro t h
    cases t with
    | zero =>
        change (∑ i, P.mass i *
          operatingOutput
            (P.aggregateProductivity (currentState h) * P.productivity i)
            (I.capital i) (localPrefixLabor P (d 0) i)
            P.alpha P.beta) =
          ∑ i, P.mass i * localPrefixOutput P (d 0) i
        apply Finset.sum_congr rfl
        intro i _hi
        unfold localPrefixOutput
        rw [hprod (currentState h), hdateProd 0, hinit i]
    | succ t =>
        change (∑ i, P.mass i *
          operatingOutput
            (P.aggregateProductivity (currentState h) * P.productivity i)
            ((d t).nextCapital i)
            (localPrefixLabor P (d (t + 1)) i) P.alpha P.beta) =
          ∑ i, P.mass i * localPrefixOutput P (d (t + 1)) i
        apply Finset.sum_congr rfl
        intro i _hi
        unfold localPrefixOutput
        rw [hprod (currentState h), hdateProd (t + 1), hstep t i]
  change ResourceClears P (withSourceAccountingCompletion P I B)
  apply (resourceClears_withSourceAccountingCompletion_iff P I B).2
  intro t h _hs
  have hK := hcapital t h
  have hY := houtput t h
  have hI : sourceInvestment P I B t h =
      localPrefixInvestment P (d t) := by
    change (∑ i, P.mass i * (d t).nextCapital i) -
      (1 - P.depreciation) * sourceAggregateCapital P I B t h =
      localPrefixInvestment P (d t)
    rw [hK]
    rfl
  have hC : sourceCapitalCreationCost P I B t h =
      localPrefixCapitalCost P (d t) := by
    change capitalCreationTechnology P (sourceInvestment P I B t h)
      (sourceAggregateCapital P I B t h) =
      localPrefixCapitalCost P (d t)
    rw [hI, hK]
    rfl
  have hP : sourcePriceAdjustmentResourceCost P I B t h =
      localPrefixRotembergCost P (d t) := by
    change P.priceAdjustmentCost / 2 *
      ((d t).controls.inflation - 1) ^ 2 *
      sourceAggregateOutput P I B t h =
      localPrefixRotembergCost P (d t)
    rw [hY]
    rfl
  change (d t).controls.workerConsumption +
    (∑ i, P.mass i * localPrefixFirmConsumption (d t).controls i) +
    sourceCapitalCreationCost P I B t h +
    sourcePriceAdjustmentResourceCost P I B t h =
    sourceAggregateOutput P I B t h
  rw [hC, hP, hY]
  have hr := hrows t
  change (d t).controls.workerConsumption +
    (∑ i, P.mass i * localPrefixFirmConsumption (d t).controls i) +
    localPrefixCapitalCost P (d t) +
    localPrefixRotembergCost P (d t) -
    localPrefixAggregateOutput P (d t) = 0 at hr
  linarith

/-- The actual SOURCE history-indexed allocation clears its literal
resource market at all supported dates. This is not a full equilibrium
claim: bank population, household/firm optimality, fiscal settlement
and terminal conditions remain separate. -/
theorem sourceBoundaryLiteralAllocation_resourceClears (G : ℝ) :
    ResourceClears
      (boundaryPrimitives G boundarySourceRate)
      (sourceBoundaryLiteralAllocation G) := by
  exact literal_resourceClears_of_aligned_reduced_rows
    (boundaryPrimitives G boundarySourceRate)
    (boundaryInitialState G boundarySourceRate)
    (sourceBoundaryDateData G)
    (sourceBoundaryDateData_initial_capital G)
    (sourceBoundaryDateData_capital_step G)
    (by intro s; rfl)
    (sourceBoundaryDateData_unit_productivity G)
    (sourceBoundaryDateData_resource_row G)

#print axioms sourceBoundaryDateData_resource_row
#print axioms sourceBoundaryDateData_initial_capital
#print axioms sourceBoundaryDateData_capital_step
#print axioms sourceBoundaryDateData_unit_productivity
#print axioms literal_resourceClears_of_aligned_reduced_rows
#print axioms sourceBoundaryLiteralAllocation_resourceClears

end ProposedBoundaryFullResourceClearing
end Ventura26LiquidityAllocation
