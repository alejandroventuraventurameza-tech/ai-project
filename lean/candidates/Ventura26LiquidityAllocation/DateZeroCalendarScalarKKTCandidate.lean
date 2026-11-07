import Ventura26LiquidityAllocation.DateZeroCalendarEulerBridgeCandidate
import Ventura26LiquidityAllocation.DateZeroScalarBindingComplementarityCandidate

/-!
# Source calendar to the binding-borrower scalar capital KKT certificate

Under the original DeterministicBridgeCalendar and binding borrower regime,
probability-one transition and zero off-path support follow from the Markov
primitives. No ad hoc assumptions on date-zero/date-one history weights are
added. Source FirmOptimal with locally feasible capital increases then gives
a nonnegative scalar multiplier, a zero capital Euler row for a dual-replaced
carrier, and complementary slackness at the active root collateral constraint.

This is NOT a proof that X.collateralDual is the constructed scalar and NOT
a proof of a complete competitive equilibrium or Proposition 4.2.
-/

namespace Ventura26LiquidityAllocation
namespace ProposedDateZeroCalendarScalarKKT

open ProposedDateZeroCalendarEulerBridge
open ProposedDateZeroDeterministicMarkovBridge
open ProposedDateZeroScalarBindingComplementarity
open ProposedProposition42KKTIdentification

variable {S : Type*} [Fintype S] [DecidableEq S]

theorem firmOptimal_sourceCalendar_binding_scalarComplementarity
    (P : Primitives S) (I : InheritedState)
    (X : Allocation S) (i : FirmType)
    (dateOne recurrent : S)
    (hcalendar : DeterministicBridgeCalendar P dateOne recurrent)
    (hopt : FirmOptimal P I X i)
    (hbinding : DateZeroBindingBorrower P X i)
    (hcapital : ∀ h : History S 0,
      FirmHistoryAdmissible P 0 h → 0 < X.capital i 0 h)
    (hcoeff : ∀ h : History S 0,
      FirmHistoryAdmissible P 0 h → ∀ v : S,
      0 < P.tree.transition (currentState h) v →
      0 ≤ P.pledgeability i * (1 - P.depreciation) *
        (X.inflation 1 (childHistory h v) *
          X.capitalPrice 1 (childHistory h v)))
    (hunit : 0 < capitalEulerCollateralUnit
      P X i 0 (rootHistory P.tree) dateOne) :
    ∃ mu : ℝ, 0 ≤ mu ∧
      localFirmCapitalEulerResidual P
        (replaceCollateralDual X (fun _ _ _ => mu))
        i 0 (rootHistory P.tree) dateOne = 0 ∧
      0 ≤ rootCollateralSlack P X i dateOne ∧
      mu * rootCollateralSlack P X i dateOne = 0 := by
  have htrans : P.tree.transition P.tree.initial dateOne = 1 :=
    hcalendar.2.2.2.1
  have hothers : ∀ v : S, v ≠ dateOne →
      P.tree.transition P.tree.initial v = 0 :=
    sourceCalendar_other_transitions_zero P dateOne recurrent hcalendar
  obtain ⟨hw0, hz0, hw1, hz1⟩ :=
    deterministic_historyWeight_package P dateOne htrans hothers
  exact firmOptimal_binding_exists_scalarEulerComplementarity
    P I X i dateOne hopt hbinding hcapital hcoeff hw0 hz0
      hw1 hz1 hothers hunit

end ProposedDateZeroCalendarScalarKKT
end Ventura26LiquidityAllocation
