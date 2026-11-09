import Ventura26LiquidityAllocation.BoundaryFullAllocationCarrierCandidate

/-!
# All-date bank balance of the constructed SOURCE boundary carrier

Proves exact source BankBalance at all supported histories for an explicit
full Allocation. Each date uses the source reduced bank-balance row with
the reserve/deposit denominator shown strictly nonzero. The first date is
the certified frontier; the second is the stationary real block with
announced monetary lags; all later dates have the stationary reduced data.

BankBalance is a literal accounting identity, not BankFeasible,
BankPopulationEquilibrium, BankOptimal, or CompetitiveEquilibrium.
-/

namespace Ventura26LiquidityAllocation
namespace ProposedBoundaryFullBankBalance

open ProposedStationaryBank
open ProposedStationaryRealScale
open ProposedStationaryReducedSystem
open ProposedBoundaryFullPrefix
open ProposedBoundaryNormalizationBridge
open ProposedBoundaryFullAllocationCarrier

/-- Initial reduced records exactly match the SOURCE frontier date. -/
theorem sourceBoundaryDateData_zero (G : ℝ) :
    sourceBoundaryDateData G 0 =
      boundaryZeroData G boundarySourceRate := by
  change localPrefixDateZeroData
    (boundaryPrimitives G boundarySourceRate)
    (boundaryInitialState G boundarySourceRate)
    (boundaryCoordinates boundarySourceRate) .dateOne =
      boundaryZeroData G boundarySourceRate
  exact boundary_dateZeroData_eq G boundarySourceRate

/-- The announced date-one financial rates and innovations are retained. -/
theorem sourceBoundaryDateData_one (G : ℝ) :
    sourceBoundaryDateData G 1 =
      boundaryOneData G boundarySourceRate := by
  rfl

/-- Recurrent dates use the literal stationary date-data record, with
all monetary innovations set to zero and the source payment law unchanged. -/
theorem sourceBoundaryDateData_tail (G : ℝ) (n : ℕ) :
    sourceBoundaryDateData G (n + 2) = dateData := by
  change localRecurrentDateData
    (boundaryPrimitives G boundarySourceRate)
    (fun _ ↦ stateSix) (fun _ ↦ controls) n = dateData
  apply recurrent_dateData_eq
  · intro i
    rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

/-- Every date's reduced bank-balance row is exactly zero. This property
was not imposed as a new premise on the constructed allocation. -/
theorem sourceBoundaryDateData_bankRow (G : ℝ) :
    ∀ t, localReducedRemainingResidual
      (boundaryPrimitives G boundarySourceRate)
      (sourceBoundaryDateData G t) 10 = 0 := by
  intro t
  cases t with
  | zero =>
      rw [sourceBoundaryDateData_zero]
      exact boundary_zero_bankBalance G boundarySourceRate
        ⟨boundarySourceRate_spec.1, boundarySourceRate_spec.2.1⟩
  | succ t =>
      cases t with
      | zero =>
          rw [sourceBoundaryDateData_one]
          exact boundary_one_nonpolicy_rows
            G boundarySourceRate (10 : Fin 11) (by decide) (by decide)
      | succ n =>
          change localReducedRemainingResidual
            (boundaryPrimitives G boundarySourceRate)
            (sourceBoundaryDateData G (n + 2)) 10 = 0
          rw [sourceBoundaryDateData_tail G n]
          exact (stationary_reduced_system
            (boundaryPrimitives G boundarySourceRate)
            (boundary_stationary_parameters G boundarySourceRate)
            0 1 (boundary_binary_payment_law G boundarySourceRate)).1
              (10 : Fin 11)

/-- No division by zero in the source reserve/deposit reconstruction at
any date; includes the DATE ZERO frontier, DATE ONE, and the recurrent tail. -/
theorem sourceBoundaryDateData_ratio_nonzero (G : ℝ) :
    ∀ t, localPrefixReserveDepositRatio
      (boundaryPrimitives G boundarySourceRate)
      (sourceBoundaryDateData G t) ≠ 0 := by
  have hstationary :
      localPrefixReserveDepositRatio
        (boundaryPrimitives G boundarySourceRate) dateData ≠ 0 := by
    rw [reducedReserveDepositRatio_eq
      (boundaryPrimitives G boundarySourceRate) 0 1
      (boundary_binary_payment_law G boundarySourceRate)]
    exact ne_of_gt bank_margins_and_pricing.1
  intro t
  cases t with
  | zero =>
      rw [sourceBoundaryDateData_zero,
        boundary_zero_reserveDepositRatio]
      rcases boundarySourceRate_bankDomain with
        ⟨_he, _hd, _hm, hratio, _hratioLt, _hloans⟩
      exact ne_of_gt hratio
  | succ t =>
      cases t with
      | zero =>
          rw [sourceBoundaryDateData_one]
          have hratioOne :
              localPrefixReserveDepositRatio
                (boundaryPrimitives G boundarySourceRate)
                (boundaryOneData G boundarySourceRate) =
              localPrefixReserveDepositRatio
                (boundaryPrimitives G boundarySourceRate)
                dateData := by
            rw [boundary_oneData_fields] <;> rfl
          rw [hratioOne]
          exact hstationary
      | succ n =>
          change localPrefixReserveDepositRatio
            (boundaryPrimitives G boundarySourceRate)
            (sourceBoundaryDateData G (n + 2)) ≠ 0
          rw [sourceBoundaryDateData_tail G n]
          exact hstationary

/-- Full literal bank balance over every supported Markov history of the
constructed Allocation. The remaining household, firm, bank-optimality,
settlement and equilibrium obligations stay open. -/
theorem sourceBoundaryLiteralAllocation_bankBalance (G : ℝ) :
    BankBalance
      (boundaryPrimitives G boundarySourceRate)
      (sourceBoundaryLiteralAllocation G) := by
  exact localSlackLiteralAllocation_bankBalance
    (boundaryPrimitives G boundarySourceRate)
    (boundaryInitialState G boundarySourceRate)
    (sourceBoundaryDateData G)
    (sourceBoundaryDateData_ratio_nonzero G)
    (sourceBoundaryDateData_bankRow G)

#print axioms sourceBoundaryDateData_zero
#print axioms sourceBoundaryDateData_one
#print axioms sourceBoundaryDateData_tail
#print axioms sourceBoundaryDateData_bankRow
#print axioms sourceBoundaryDateData_ratio_nonzero
#print axioms sourceBoundaryLiteralAllocation_bankBalance

end ProposedBoundaryFullBankBalance
end Ventura26LiquidityAllocation
