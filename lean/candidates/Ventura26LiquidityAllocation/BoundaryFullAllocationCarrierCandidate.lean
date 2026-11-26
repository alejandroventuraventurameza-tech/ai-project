import Ventura26LiquidityAllocation.BoundaryRealizedBankRowsCandidate

/-!
# Constructed full Allocation carrier at the exact SOURCE boundary

The 33-row SOURCE boundary rate has already been kernel-verified. Unlike a
conditional theorem assuming a realized Allocation, this file *constructs*
one using the original source model's literal-allocation constructor and
stationary recurrent coordinates. The constructor alone DOES NOT prove a
competitive equilibrium: private/global optimality, supported-history
feasibility, accounting/resource compatibility, monetary rules and TVCs
require separate obligations.

The source constructor has fields at every date/history. Its prefix
realization and literal bank transition identities are unconditional
theorems here; their economic interpretation remains strictly limited.
-/

namespace Ventura26LiquidityAllocation
namespace ProposedBoundaryFullAllocationCarrier

open ProposedBoundaryFullPrefix
open ProposedBoundaryResourceRoot
open ProposedBoundaryNormalizationBridge
open ProposedBoundaryRealizedBankRows

/-- Data at dates zero, one, and each recurrent date, with the certified
boundary root at the initial date and the stationary reduced tail thereafter.
This does not claim the recurrent data solve every source optimality condition. -/
noncomputable def sourceBoundaryDateData (G : ℝ) :
    ℕ → LocalPrefixDateData :=
  localSlackExactDateData
    (boundaryPrimitives G boundarySourceRate)
    (boundaryInitialState G boundarySourceRate)
    (boundaryCoordinates boundarySourceRate)
    boundaryTail
    (fun _ ↦ (boundaryCoordinates boundarySourceRate).stateTwo)
    (fun _ ↦ boundaryTail (boundaryCoordinates boundarySourceRate).stateTwo)

/-- Actual source Allocation over every date and history, not merely 33
abstract variables. This record is a candidate, not an equilibrium witness. -/
noncomputable def sourceBoundaryLiteralAllocation (G : ℝ) :
    Allocation LocalBridgePhase :=
  localSlackLiteralAllocation
    (boundaryPrimitives G boundarySourceRate)
    (boundaryInitialState G boundarySourceRate)
    (sourceBoundaryDateData G)

/-- The certified 33-dimensional SOURCE root is realized by an explicitly
constructed history-indexed allocation, without assuming realization. -/
theorem sourceBoundaryLiteralAllocation_realizes_prefix (G : ℝ) :
    LocalPrefixCoordinatesRealized
      (boundaryPrimitives G boundarySourceRate)
      (sourceBoundaryLiteralAllocation G) .dateOne .recurrent
      (boundaryCoordinates boundarySourceRate) := by
  unfold sourceBoundaryLiteralAllocation sourceBoundaryDateData
  apply localSlackLiteralAllocation_prefix_realized
    (boundaryPrimitives G boundarySourceRate)
    (boundaryInitialState G boundarySourceRate)
    (boundaryCoordinates boundarySourceRate)
    boundaryTail
    (fun _ ↦ (boundaryCoordinates boundarySourceRate).stateTwo)
    (fun _ ↦ boundaryTail (boundaryCoordinates boundarySourceRate).stateTwo)
  · rfl
  · rfl
  · norm_num [boundaryCoordinates, ProposedStationaryRealScale.controls]
  · norm_num [boundaryTail, ProposedStationaryRealScale.controls]
  · exact boundarySourceRate_reduced_prefix G LocalPrefixBranch.slack

/-- Exact banking equity transition residuals hold for the constructed
candidate at both initial dates. This does not verify the infinite-horizon
banking objective or bank population equilibrium. -/
theorem sourceBoundaryLiteralAllocation_bank_transitions (G : ℝ) :
    localBankEquityTransitionResidual
        (boundaryPrimitives G boundarySourceRate)
        (sourceBoundaryLiteralAllocation G) 0
        (bridgeDateZeroHistory (boundaryPrimitives G boundarySourceRate))
        .dateOne = 0 ∧
    localBankEquityTransitionResidual
        (boundaryPrimitives G boundarySourceRate)
        (sourceBoundaryLiteralAllocation G) 1
        (bridgeDateOneHistory (boundaryPrimitives G boundarySourceRate)
          .dateOne) .recurrent = 0 := by
  have hreal := sourceBoundaryLiteralAllocation_realizes_prefix G
  have hcurrent :
      (sourceBoundaryLiteralAllocation G).bankEquity 0
          (bridgeDateZeroHistory (boundaryPrimitives G boundarySourceRate)) =
        (boundaryInitialState G boundarySourceRate).bankFace /
          (sourceBoundaryLiteralAllocation G).inflation 0
            (bridgeDateZeroHistory (boundaryPrimitives G boundarySourceRate)) := by
    change (sourceBoundaryDateData G 0).currentBankFace /
        (sourceBoundaryDateData G 0).controls.inflation =
      (boundaryInitialState G boundarySourceRate).bankFace /
        (sourceBoundaryDateData G 0).controls.inflation
    rfl
  have hπ1 :
      (sourceBoundaryLiteralAllocation G).inflation 1
        (bridgeDateOneHistory (boundaryPrimitives G boundarySourceRate)
          .dateOne) ≠ 0 := by
    change (sourceBoundaryDateData G 1).controls.inflation ≠ 0
    norm_num [sourceBoundaryDateData, localSlackExactDateData,
      localPrefixDateOneData, boundaryCoordinates,
      ProposedStationaryRealScale.controls]
  have hπ2 :
      (sourceBoundaryLiteralAllocation G).inflation 2
        (bridgeDateTwoHistory (boundaryPrimitives G boundarySourceRate)
          .dateOne .recurrent) ≠ 0 := by
    change (sourceBoundaryDateData G 2).controls.inflation ≠ 0
    norm_num [sourceBoundaryDateData, localSlackExactDateData,
      localRecurrentDateData, boundaryCoordinates, boundaryTail,
      ProposedStationaryRealScale.controls]
  exact source_boundary_bank_equity_transitions G
    (sourceBoundaryLiteralAllocation G) hreal hcurrent hπ1 hπ2

/-- Three genuine, all-date/all-supported-history market-accounting
identities follow by construction, but they are only a subset of
CompetitiveEquilibrium and do not establish BankBalance or BankOptimal. -/
theorem sourceBoundaryLiteralAllocation_selected_clearing (G : ℝ) :
    CreditClears
        (boundaryPrimitives G boundarySourceRate)
        (sourceBoundaryLiteralAllocation G) ∧
    DepositsClear
        (boundaryPrimitives G boundarySourceRate)
        (sourceBoundaryLiteralAllocation G) ∧
    LaborClears
        (boundaryPrimitives G boundarySourceRate)
        (sourceBoundaryLiteralAllocation G) := by
  constructor
  · exact localSlackLiteralAllocation_creditClears
      (boundaryPrimitives G boundarySourceRate)
      (boundaryInitialState G boundarySourceRate)
      (sourceBoundaryDateData G)
  constructor
  · exact localSlackLiteralAllocation_depositsClear
      (boundaryPrimitives G boundarySourceRate)
      (boundaryInitialState G boundarySourceRate)
      (sourceBoundaryDateData G)
  · exact localSlackLiteralAllocation_laborClears
      (boundaryPrimitives G boundarySourceRate)
      (boundaryInitialState G boundarySourceRate)
      (sourceBoundaryDateData G)

#print axioms sourceBoundaryLiteralAllocation_realizes_prefix
#print axioms sourceBoundaryLiteralAllocation_bank_transitions
#print axioms sourceBoundaryLiteralAllocation_selected_clearing

end ProposedBoundaryFullAllocationCarrier
end Ventura26LiquidityAllocation
