import Ventura26LiquidityAllocation.BoundaryFullCapitalProducerCandidate

/-!
# Literal all-history firm budget flows at the certified SOURCE frontier

A solution of the 33 reduced rows proves only the date-zero and date-one
budget equations. This module extends them to every date, and connects
the original firm's *wealth-flow* identities to the predecessor's
installed capital and inherited nominal loan face.

The extension uses the constructed date sequence, certified recurrent
stationary rows, and exact capital- and face-continuity theorems.
No global firm optimality, collateral sufficiency, TVCs, nor full
competitive equilibrium is inferred from these budget identities.
-/

namespace Ventura26LiquidityAllocation
namespace ProposedBoundaryFullFirmBudget

open ProposedStationaryRealScale
open ProposedStationaryReducedSystem
open ProposedBoundaryResourceRoot
open ProposedBoundaryFullPrefix
open ProposedBoundaryNormalizationBridge
open ProposedBoundaryFullAllocationCarrier
open ProposedBoundaryFullBankBalance
open ProposedBoundaryFullResourceClearing
open ProposedBoundaryCapitalProducer

/-- Literal firm budget rows vanish at the SOURCE frontier, announced
date one, and each subsequent stationary date. -/
theorem sourceBoundaryDateData_firm_budget_row (G : ℝ) :
    ∀ t (i : FirmType),
      localReducedFirmBudgetResidual
        (boundaryPrimitives G boundarySourceRate)
        (sourceBoundaryDateData G t) i = 0 := by
  intro t i
  cases t with
  | zero =>
      rw [sourceBoundaryDateData_zero]
      exact (boundary_zero_firm_rows G boundarySourceRate
        boundarySourceRate_positiveRealDomain.1 LocalPrefixBranch.slack i).1
  | succ t =>
      cases t with
      | zero =>
          rw [sourceBoundaryDateData_one]
          exact (boundary_one_firm_rows G boundarySourceRate i).1
      | succ n =>
          change localReducedFirmBudgetResidual
            (boundaryPrimitives G boundarySourceRate)
            (sourceBoundaryDateData G (n + 2)) i = 0
          rw [sourceBoundaryDateData_tail G n]
          exact ((stationary_reduced_system
            (boundaryPrimitives G boundarySourceRate)
            (boundary_stationary_parameters G boundarySourceRate)
            0 1 (boundary_binary_payment_law G boundarySourceRate)).2 i).1

/-- The face issued at date t is literally the nominal face inherited at
t+1. This equality is separate from bank-equity renewal. -/
theorem sourceBoundaryDateData_firm_face_step (G : ℝ) (t : ℕ)
    (i : FirmType) :
    (sourceBoundaryDateData G t).nextFace i =
      (sourceBoundaryDateData G (t + 1)).inheritedFace i := by
  cases t with
  | zero =>
      rw [sourceBoundaryDateData_zero, sourceBoundaryDateData_one,
        boundary_oneData_fields]
      rfl
  | succ t =>
      cases t with
      | zero =>
          change (sourceBoundaryDateData G 1).nextFace i =
            (sourceBoundaryDateData G 2).inheritedFace i
          rw [sourceBoundaryDateData_one, sourceBoundaryDateData_tail G 0,
            boundary_oneData_fields]
          rfl
      | succ n =>
          change (sourceBoundaryDateData G (n + 2)).nextFace i =
            (sourceBoundaryDateData G ((n + 1) + 2)).inheritedFace i
          rw [sourceBoundaryDateData_tail G n,
            sourceBoundaryDateData_tail G (n + 1)]
          rfl

/-- The constructed first-date wealth formula uses the same original
nominal inherited firm promises as the SOURCE InheritedState. -/
theorem sourceBoundaryDateData_initial_firm_face (G : ℝ) (i : FirmType) :
    (boundaryInitialState G boundarySourceRate).firmFace i =
      (sourceBoundaryDateData G 0).inheritedFace i := by
  rw [sourceBoundaryDateData_zero]
  rfl

/-- General bridge from budget rows and interdate stock continuity
to the *literal* SOURCE FirmBudgetFlows predicate, including both
initial and successor wealth-flow equations. -/
theorem localSlackLiteralAllocation_firmBudgetFlows_of_aligned_rows
    (P : Primitives LocalBridgePhase) (I : InheritedState)
    (d : ℕ → LocalPrefixDateData)
    (hrow : ∀ t i, localReducedFirmBudgetResidual P (d t) i = 0)
    (hinitialK : ∀ i, I.capital i = (d 0).currentCapital i)
    (hinitialF : ∀ i, I.firmFace i = (d 0).inheritedFace i)
    (hnextK : ∀ t i, (d t).nextCapital i = (d (t + 1)).currentCapital i)
    (hnextF : ∀ t i, (d t).nextFace i = (d (t + 1)).inheritedFace i)
    (hproductivity : ∀ s, P.aggregateProductivity s = 1)
    (hdateproductivity : ∀ t, (d t).currentAggregateProductivity = 1) :
    FirmBudgetFlows P I (localSlackLiteralAllocation P I d) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i t h _hs
    have hr := hrow t i
    unfold localReducedFirmBudgetResidual at hr
    change localPrefixFirmConsumption (d t).controls i +
      (d t).controls.capitalPrice * (d t).nextCapital i + 0 =
      localPrefixFirmWealth P (d t) i +
        (d t).nextFace i / (d t).controls.loanRate
    linarith
  · intro i h _hs
    change localPrefixFirmWealth P (d 0) i =
      operatingProfit (d 0).controls.inputPrice
        (P.aggregateProductivity (currentState h) * P.productivity i)
        (I.capital i)
        (localPrefixLabor P (d 0) i)
        P.alpha P.beta (d 0).controls.wage +
      (d 0).controls.capitalPrice * (1 - P.depreciation) * I.capital i -
      realRepayment (I.firmFace i) (d 0).controls.inflation
    simp only [localPrefixFirmWealth, localPrefixOperatingProfit,
      localPrefixOutput, operatingProfit, realRepayment]
    rw [hinitialK i, hinitialF i,
      hproductivity (currentState h), hdateproductivity 0]
    ring
  · intro i t h s _hs
    change localPrefixFirmWealth P (d (t + 1)) i =
      operatingProfit (d (t + 1)).controls.inputPrice
        (P.aggregateProductivity s * P.productivity i)
        ((d t).nextCapital i)
        (localPrefixLabor P (d (t + 1)) i)
        P.alpha P.beta (d (t + 1)).controls.wage +
      (d (t + 1)).controls.capitalPrice *
        (1 - P.depreciation) * (d t).nextCapital i -
      realRepayment ((d t).nextFace i)
        (d (t + 1)).controls.inflation
    simp only [localPrefixFirmWealth, localPrefixOperatingProfit,
      localPrefixOutput, operatingProfit, realRepayment]
    rw [hnextK t i, hnextF t i,
      hproductivity s, hdateproductivity (t + 1)]
    ring

/-- All literal SOURCE firms satisfy their exact budgets and wealth
transitions in every supported Markov history. No optimality is implied. -/
theorem sourceBoundaryLiteralAllocation_firmBudgetFlows (G : ℝ) :
    FirmBudgetFlows
      (boundaryPrimitives G boundarySourceRate)
      (boundaryInitialState G boundarySourceRate)
      (sourceBoundaryLiteralAllocation G) := by
  exact localSlackLiteralAllocation_firmBudgetFlows_of_aligned_rows
    (boundaryPrimitives G boundarySourceRate)
    (boundaryInitialState G boundarySourceRate)
    (sourceBoundaryDateData G)
    (sourceBoundaryDateData_firm_budget_row G)
    (sourceBoundaryDateData_initial_capital G)
    (sourceBoundaryDateData_initial_firm_face G)
    (sourceBoundaryDateData_capital_step G)
    (sourceBoundaryDateData_firm_face_step G)
    (by intro s; rfl)
    (sourceBoundaryDateData_unit_productivity G)

#print axioms sourceBoundaryDateData_firm_budget_row
#print axioms sourceBoundaryDateData_firm_face_step
#print axioms sourceBoundaryDateData_initial_firm_face
#print axioms localSlackLiteralAllocation_firmBudgetFlows_of_aligned_rows
#print axioms sourceBoundaryLiteralAllocation_firmBudgetFlows

end ProposedBoundaryFullFirmBudget
end Ventura26LiquidityAllocation
