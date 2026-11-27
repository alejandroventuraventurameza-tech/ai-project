import Ventura26LiquidityAllocation.CurrentPinnedStationaryPrefix33Root
import Ventura26LiquidityAllocation.StationaryInheritedStateCandidate

/-!
# Explicit fiscal fiber for the stationary SOURCE finite-prefix root

The 33-row binding SOURCE root exists for any real G as a PARAMETER
because the finite reduced system omits the government-bond fiscal fiber.
Here we choose one concrete, exact G that meets the monetary primitive
domain and makes inherited household government bonds strictly positive.

The associated accounting carrier satisfies FiscalClosure independently,
but it is not thereby certified as globally optimal, terminally
admissible, or an infinite-horizon equilibrium. In particular, this
does not prove Jacobian invertibility or a switching-boundary root.
-/

namespace Ventura26LiquidityAllocation
namespace CurrentPinnedFiscalFiber

open ProposedStationaryRealScale
open ProposedStationaryPrimitives
open ProposedStationaryInheritedState
open CurrentPinnedStationaryRoot

/-- Positive illustrative exact public-debt supply: twice PRE-settlement
reserves. This is a normalization of the stationary fiscal fiber,
not an estimated policy parameter or a calibrated empirical datum. -/
noncomputable def pinnedFiscalG : ℝ := 2 * reservesPre

theorem pinnedFiscalG_gt_pre_reserves :
    reservesPre < pinnedFiscalG := by
  have hpre : 0 < reservesPre := bank_scale_pos.2.2
  unfold pinnedFiscalG
  linarith

#print axioms pinnedFiscalG_gt_pre_reserves

/-- The genuine inherited government-bond holdings are positive. -/
theorem pinnedFiscalG_household_bonds_pos :
    0 < (inheritedState pinnedFiscalG).householdBonds :=
  (inherited_householdBonds_pos_iff pinnedFiscalG).2
    pinnedFiscalG_gt_pre_reserves

#print axioms pinnedFiscalG_household_bonds_pos

/-- The same explicitly selected G meets the underlying SOURCE monetary
primitive domain, not just the algebraic 33-row root. -/
theorem pinnedFiscalG_monetary_domain :
    MonetaryPolicyPrimitiveDomain (primitives pinnedFiscalG)
      (inheritedState pinnedFiscalG) :=
  inherited_monetary_domain pinnedFiscalG
    (le_of_lt pinnedFiscalG_gt_pre_reserves)

#print axioms pinnedFiscalG_monetary_domain

/-- The actual stationary accounting carrier separately satisfies
the model's fiscal-closure predicate at the SAME selected G.
This does not prove an optimal equilibrium allocation. -/
theorem pinnedFiscalG_carrier_fiscal_closure :
    FiscalClosure (primitives pinnedFiscalG)
      (inheritedState pinnedFiscalG)
      (parentAllocation pinnedFiscalG) :=
  parentAllocation_fiscalClosure pinnedFiscalG

#print axioms pinnedFiscalG_carrier_fiscal_closure

/-- Exact 33-row SOURCE B root with the chosen monetarily admissible
fiscal fiber. The fixed P0 continuation and stationary log origin
are unchanged; the 34-row boundary is not inferred. -/
theorem pinnedFiscalG_binding_prefix33_root :
    localReducedPrefixLogResidualVector .binding
      (primitives pinnedFiscalG)
      (inheritedState pinnedFiscalG)
      fullyPinnedStationarySOURCEZ0 .dateOne .recurrent
      (sourceLogLinearContinuation
        ProposedStationaryRealScale.stateSix
        ProposedStationaryRealScale.controls
        sourceFrozenP0TenControls)
      (0 : Fin 33 → ℝ) = 0 :=
  pinned_stationary_binding_prefix33_root pinnedFiscalG

#print axioms pinnedFiscalG_binding_prefix33_root

end CurrentPinnedFiscalFiber
end Ventura26LiquidityAllocation
