import Ventura26LiquidityAllocation.BoundaryFullResourceClearingCandidate

/-!
# Certified SOURCE frontier: candidate all-history OTC and fiscal clearing

The scalar SOURCE root, the 33-row reduced prefix, and the literal
history-indexed resource accounts are imported as *proved* results.

This candidate attempts to establish the independent OTC condition
for every supported history. The source common-bank plan has a binary
symmetric payment distribution. At all three calendar phases the
reserve/deposit ratio follows its exact settlement-preserving reduced
formula. Date zero and the stationary continuation are checked separately.

The fiscal closure is derived from OTC settlement through the original
source fiscal-accounting constructor. The latter does not prove
HouseholdBudgetFlows, FirmOptimal, BankOptimal or CompetitiveEquilibrium.
-/

namespace Ventura26LiquidityAllocation
namespace ProposedBoundaryFullSettlement

open ProposedStationaryBank
open ProposedStationaryRealScale
open ProposedBoundaryResourceRoot
open ProposedBoundaryFullPrefix
open ProposedBoundaryNormalizationBridge
open ProposedBoundaryFullAllocationCarrier
open ProposedBoundaryFullBankBalance
open ProposedBoundaryRealAccounting
open ProposedBoundaryFullResourceClearing

/-- The SOURCE date-zero deposit rate exceeds the reserve rate.
In particular, the deposit/reserve price ratio strictly exceeds the
reserve requirement. The proof uses the original OTC pricing equation,
not a guessed decimal price. -/
theorem source_boundary_deposit_gt_reserve :
    boundaryReserveRate boundarySourceRate <
      boundaryDepositRate boundarySourceRate := by
  have hrr : 0 < boundaryReserveRate boundarySourceRate :=
    boundarySourceRate_positiveRealDomain.2.1
  have hb : 0 < boundaryPaymentTerm := by
    unfold boundaryPaymentTerm
    exact div_pos slope_bounds.2.2.1 (by norm_num)
  have hgap : 0 < meanSlope - boundaryPaymentTerm := by
    simpa only [boundaryPaymentTerm] using slope_bounds.2.2.2.2
  have hc : 0 < (9 / 10 : ℝ) * (meanSlope - boundaryPaymentTerm) :=
    mul_pos (by norm_num) hgap
  have hden : 0 <
      boundaryReserveRate boundarySourceRate + boundaryPaymentTerm :=
    add_pos hrr hb
  rw [boundaryDepositRate_rewrite boundarySourceRate
    (ne_of_gt hrr) (ne_of_gt hden)]
  have hpositive :
      0 < ((9 / 10 : ℝ) * (meanSlope - boundaryPaymentTerm)) *
          boundaryReserveRate boundarySourceRate /
            (boundaryReserveRate boundarySourceRate + boundaryPaymentTerm) :=
    div_pos (mul_pos hc hrr) hden
  linarith

/-- Both the transient SOURCE portfolio and the stationary rows satisfy
the five strict OTC-domain conditions required by the source cancellation
lemma. This verifies the domain for *every date*, not just two rows. -/
theorem sourceBoundaryDateData_otc_domain (G : ℝ) :
    ∀ t,
      0 < (sourceBoundaryDateData G t).controls.tightness ∧
      0 < (sourceBoundaryDateData G t).currentReservesPre ∧
      0 < localPrefixReserveDepositRatio
        (boundaryPrimitives G boundarySourceRate) (sourceBoundaryDateData G t) ∧
      0 < (sourceBoundaryDateData G t).currentReserveRate ∧
      (sourceBoundaryDateData G t).reserveRequirement <
        (sourceBoundaryDateData G t).controls.depositRate /
          (sourceBoundaryDateData G t).currentReserveRate := by
  let P := boundaryPrimitives G boundarySourceRate
  have hstationary :
      0 < dateData.controls.tightness ∧
      0 < dateData.currentReservesPre ∧
      0 < localPrefixReserveDepositRatio P dateData ∧
      0 < dateData.currentReserveRate ∧
      dateData.reserveRequirement <
        dateData.controls.depositRate / dateData.currentReserveRate := by
    rcases ProposedStationaryBank.localPrefix_bank_domain
      P dateData 0 1 (boundary_binary_payment_law G boundarySourceRate)
      rfl rfl rfl rfl with ⟨htau, hrr, hxi, hratio, _hratiohi⟩
    exact ⟨htau, bank_scale_pos.2.2,
      lt_trans (by norm_num) hratio, hrr, hxi⟩
  have hzero :
      0 < (boundaryZeroData G boundarySourceRate).controls.tightness ∧
      0 < (boundaryZeroData G boundarySourceRate).currentReservesPre ∧
      0 < localPrefixReserveDepositRatio P
        (boundaryZeroData G boundarySourceRate) ∧
      0 < (boundaryZeroData G boundarySourceRate).currentReserveRate ∧
      (boundaryZeroData G boundarySourceRate).reserveRequirement <
        (boundaryZeroData G boundarySourceRate).controls.depositRate /
          (boundaryZeroData G boundarySourceRate).currentReserveRate := by
    rcases boundarySourceRate_bankDomain with
      ⟨_hEquity, _hDeposits, hReserves, hRatio, _hRatioUpper, _hLoans⟩
    have hRR := boundarySourceRate_positiveRealDomain.2.1
    have hRD :
        1 < boundaryDepositRate boundarySourceRate /
            boundaryReserveRate boundarySourceRate :=
      (one_lt_div hRR).mpr source_boundary_deposit_gt_reserve
    change (0 : ℝ) < 1 / 2 ∧
      0 < boundaryReservesPre boundarySourceRate ∧
      0 < localPrefixReserveDepositRatio P
        (boundaryZeroData G boundarySourceRate) ∧
      0 < boundaryReserveRate boundarySourceRate ∧
      (1 / 10 : ℝ) <
        boundaryDepositRate boundarySourceRate /
          boundaryReserveRate boundarySourceRate
    refine ⟨by norm_num, hReserves, ?_, hRR, by linarith⟩
    rw [show P = boundaryPrimitives G boundarySourceRate from rfl,
      boundary_zero_reserveDepositRatio]
    exact hRatio
  intro t
  cases t with
  | zero =>
      simpa only [sourceBoundaryDateData_zero] using hzero
  | succ t =>
      cases t with
      | zero =>
          simpa [sourceBoundaryDateData_one, boundary_oneData_fields]
            using hstationary
      | succ n =>
          simpa only [sourceBoundaryDateData_tail G n] using hstationary

/-- On an admissible (positive-weight) Markov history the reserve
requirement in the source primitive is exactly the date-data requirement.
The calendar is deterministic and is not replaced by a simulated history. -/
theorem sourceBoundaryDateData_reserveRequirement (G : ℝ) :
    ∀ t (h : History LocalBridgePhase t),
      FirmHistoryAdmissible (boundaryPrimitives G boundarySourceRate) t h →
      (boundaryPrimitives G boundarySourceRate).reserveRequirementPath t h =
        (sourceBoundaryDateData G t).reserveRequirement := by
  intro t h hs
  simpa only [sourceBoundaryDateData] using
    (proposed_localSlackExactDateData_reserveRequirement_eq
      (boundaryPrimitives G boundarySourceRate)
      (boundaryInitialState G boundarySourceRate)
      (boundaryCoordinates boundarySourceRate)
      boundaryTail
      (fun _ ↦ (boundaryCoordinates boundarySourceRate).stateTwo)
      (fun _ ↦ boundaryTail (boundaryCoordinates boundarySourceRate).stateTwo)
      (by rfl) t h hs)

/-- Exact OTC net interbank position, expected over both payment shocks,
vanishes at every supported SOURCE history and every date. This is not
a claim about off-path histories or a bank population optimum. -/
theorem sourceBoundaryLiteralAllocation_settlementClears (G : ℝ) :
    SettlementClears
      (boundaryPrimitives G boundarySourceRate)
      (sourceBoundaryLiteralAllocation G) := by
  let P := boundaryPrimitives G boundarySourceRate
  let I := boundaryInitialState G boundarySourceRate
  let d := sourceBoundaryDateData G
  have hd := sourceBoundaryDateData_otc_domain G
  change SettlementClears P (localSlackLiteralAllocation P I d)
  exact proposed_localSlackLiteralAllocation_settlementClears_of_binarySymmetric
    P I d 0 1 (1 / 5) (boundary_binary_payment_law G boundarySourceRate)
    (fun t ↦ (hd t).1)
    (fun t ↦ (hd t).2.1)
    (fun t ↦ (hd t).2.2.1)
    (fun t ↦ (hd t).2.2.2.1)
    (fun t ↦ (hd t).2.2.2.2)
    (sourceBoundaryDateData_reserveRequirement G)

/-- The SOURCE fiscal constructor's tax and bond positions satisfy
the literal consolidated fiscal closure once OTC has been proved.
The household budget remains an independent condition. -/
theorem sourceBoundaryLiteralAllocation_fiscalClosure (G : ℝ) :
    FiscalClosure
      (boundaryPrimitives G boundarySourceRate)
      (boundaryInitialState G boundarySourceRate)
      (sourceBoundaryLiteralAllocation G) := by
  have hsettlement := sourceBoundaryLiteralAllocation_settlementClears G
  change SettlementClears
    (boundaryPrimitives G boundarySourceRate)
    (localSlackSettlementAllocation
      (boundaryPrimitives G boundarySourceRate)
      (sourceBoundaryDateData G)) at hsettlement
  exact sourceBoundary_fiscalClosure_of_settlement G hsettlement

#print axioms source_boundary_deposit_gt_reserve
#print axioms sourceBoundaryDateData_otc_domain
#print axioms sourceBoundaryDateData_reserveRequirement
#print axioms sourceBoundaryLiteralAllocation_settlementClears
#print axioms sourceBoundaryLiteralAllocation_fiscalClosure

end ProposedBoundaryFullSettlement
end Ventura26LiquidityAllocation
