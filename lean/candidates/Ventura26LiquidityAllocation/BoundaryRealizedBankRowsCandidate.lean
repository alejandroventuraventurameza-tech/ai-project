import Ventura26LiquidityAllocation.BoundaryNormalizationBridgeCandidate

/-!
# Literal bank transitions at the certified SOURCE boundary

This file specializes existing exact reduced-to-literal implications to the
named, kernel-verified SOURCE resource root. The remaining premises explicitly
refer to a *full* history-indexed Allocation, which has NOT yet been constructed.
No result below claims CompetitiveEquilibrium or BankOptimal.

This module also exposes the nonidentification of the full Allocation by
the 33-coordinate root: the reduced surface is invariant to changes in tax.
-/

namespace Ventura26LiquidityAllocation
namespace ProposedBoundaryRealizedBankRows

open ProposedBoundaryFullPrefix
open ProposedBoundaryResourceRoot
open ProposedBoundaryNormalizationBridge

/-- Once a full allocation actually realizes the 33 SOURCE coordinates,
the two reduced face equations imply both literal *real* bank equity
transition residuals, provided the inherited equity is identified and
child-date inflation is nonzero. These are necessary rows only, not a
bank optimality or equilibrium existence certificate. -/
theorem source_boundary_bank_equity_transitions
    (G : ℝ) (X : Allocation LocalBridgePhase)
    (hrealized : LocalPrefixCoordinatesRealized
      (boundaryPrimitives G boundarySourceRate) X .dateOne .recurrent
      (boundaryCoordinates boundarySourceRate))
    (hcurrent :
      X.bankEquity 0
          (bridgeDateZeroHistory (boundaryPrimitives G boundarySourceRate)) =
        (boundaryInitialState G boundarySourceRate).bankFace /
          X.inflation 0
            (bridgeDateZeroHistory (boundaryPrimitives G boundarySourceRate)))
    (hπ1 :
      X.inflation 1
        (bridgeDateOneHistory (boundaryPrimitives G boundarySourceRate)
          .dateOne) ≠ 0)
    (hπ2 :
      X.inflation 2
        (bridgeDateTwoHistory (boundaryPrimitives G boundarySourceRate)
          .dateOne .recurrent) ≠ 0) :
    localBankEquityTransitionResidual
        (boundaryPrimitives G boundarySourceRate) X 0
        (bridgeDateZeroHistory (boundaryPrimitives G boundarySourceRate))
        .dateOne = 0 ∧
    localBankEquityTransitionResidual
        (boundaryPrimitives G boundarySourceRate) X 1
        (bridgeDateOneHistory (boundaryPrimitives G boundarySourceRate)
          .dateOne) .recurrent = 0 := by
  have hred := boundarySourceRate_reduced_prefix G LocalPrefixBranch.slack
  constructor
  · exact localReducedPrefix_bankEquityTransition_zero_of_realized
      (boundaryPrimitives G boundarySourceRate)
      (boundaryInitialState G boundarySourceRate) X
      .dateOne .recurrent (boundaryCoordinates boundarySourceRate)
      boundaryTail hrealized hred hcurrent hπ1
  · exact localReducedPrefix_bankEquityTransition_one_of_realized
      (boundaryPrimitives G boundarySourceRate)
      (boundaryInitialState G boundarySourceRate) X
      .dateOne .recurrent (boundaryCoordinates boundarySourceRate)
      boundaryTail hrealized hred hπ1 hπ2

/-- Even at the unique certified SOURCE rate, the reduced root and an
honest realization of all 33 coordinates cannot identify the full
allocation: tax can be perturbed without modifying the coordinate
surface or any of the reduced equations. This does not imply that the
perturbed allocation is fiscally feasible or a competitive equilibrium. -/
theorem source_boundary_full_allocation_not_identified
    (G : ℝ) (X : Allocation LocalBridgePhase)
    (hrealized : LocalPrefixCoordinatesRealized
      (boundaryPrimitives G boundarySourceRate) X .dateOne .recurrent
      (boundaryCoordinates boundarySourceRate)) :
    ∃ X' : Allocation LocalBridgePhase,
      LocalPrefixCoordinatesRealized
        (boundaryPrimitives G boundarySourceRate) X'
        .dateOne .recurrent (boundaryCoordinates boundarySourceRate) ∧
      LocalReducedPrefixEquationsHold LocalPrefixBranch.slack
        (boundaryPrimitives G boundarySourceRate)
        (boundaryInitialState G boundarySourceRate)
        (boundaryCoordinates boundarySourceRate)
        .dateOne .recurrent boundaryTail ∧
      X' ≠ X := by
  exact localReducedPrefix_surface_does_not_identify_tax
    LocalPrefixBranch.slack
    (boundaryPrimitives G boundarySourceRate)
    (boundaryInitialState G boundarySourceRate) X
    .dateOne .recurrent (boundaryCoordinates boundarySourceRate)
    boundaryTail hrealized
    (boundarySourceRate_reduced_prefix G LocalPrefixBranch.slack)

#print axioms source_boundary_bank_equity_transitions
#print axioms source_boundary_full_allocation_not_identified

end ProposedBoundaryRealizedBankRows
end Ventura26LiquidityAllocation
