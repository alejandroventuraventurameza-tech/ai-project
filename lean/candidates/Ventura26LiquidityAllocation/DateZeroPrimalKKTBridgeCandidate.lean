import Ventura26LiquidityAllocation.DateZeroDeterministicMarkovBridgeCandidate
import Ventura26LiquidityAllocation.Proposition42KKTIdentificationCandidate

/-!
# Source optimality to the primal date-zero capital-Euler row

Under a degenerate Markov transition and strictly slack collateral for the
selected firm, the genuine infinite-horizon FirmOptimal implies the capital
Euler row WITHOUT a collateral premium. This is the identification of a
primal residual, not of the source Allocation.collateralDual field.
A final theorem constructs a canonical zero-dual carrier solely to show
that the primal equation can be expressed in the original residual notation.
No unconditional KKT, binding-collateral, or equilibrium-existence result.
-/

namespace Ventura26LiquidityAllocation
namespace ProposedDateZeroPrimalKKTBridge

open ProposedDateZeroDeterministicMarkovBridge
open ProposedDateZeroCapitalEulerDerivative
open ProposedProposition42KKTIdentification
open ProposedContinuationContractAudit

variable {S : Type*} [Fintype S] [DecidableEq S]

private theorem initial_history_admissible (P : Primitives S) :
    FirmHistoryAdmissible P 0 (rootHistory P.tree) := by
  simp [FirmHistoryAdmissible, FiniteMarkovTree.historyWeight,
    rootHistory, currentState]

/-- The marginal profit from an additional capital unit is the exact
    source Cobb-Douglas term appearing in the primal Euler row. -/
private theorem gain_is_primal_return (P : Primitives S) (X : Allocation S)
    (i : FirmType) (s : S) :
    dateOneMarginalCapitalPayoff P X i (firmPlanOfAllocation X i)
        (childHistory (rootHistory P.tree) s) =
      X.inputPrice 1 (childHistory (rootHistory P.tree) s) *
        (P.aggregateProductivity s * P.productivity i) * P.alpha *
        (X.capital i 0 (rootHistory P.tree)) ^ (P.alpha - 1) *
        (X.labor i 1 (childHistory (rootHistory P.tree) s)) ^ P.beta +
      (1 - P.depreciation) *
        X.capitalPrice 1 (childHistory (rootHistory P.tree) s) := by
  have hp : previousHistory (childHistory (rootHistory P.tree) s) =
      rootHistory P.tree := by
    funext j
    rfl
  simp only [dateOneMarginalCapitalPayoff, firmPlanOfAllocation, hp,
    currentState, childHistory]

/-- Primal Euler gap at the genuine root node: source optimality implies
    zero under slack collateral and deterministic aggregate state. -/
theorem firmOptimal_deterministic_root_primalGap_zero
    (P : Primitives S) (I : InheritedState)
    (X : Allocation S) (i : FirmType) (s : S)
    (hopt : FirmOptimal P I X i)
    (hcapital : ∀ h : History S 0,
      FirmHistoryAdmissible P 0 h → 0 < X.capital i 0 h)
    (hslack : DateZeroSlackBorrower P X i)
    (htrans : P.tree.transition P.tree.initial s = 1)
    (hothers : ∀ v : S, v ≠ s →
      P.tree.transition P.tree.initial v = 0) :
    capitalEulerPrimalGap P X i 0 (rootHistory P.tree) s = 0 := by
  let h0 : History S 0 := rootHistory P.tree
  let h1 : History S 1 := childHistory h0 s
  have heuler := firmOptimal_deterministicTransition_capitalEuler
    P I X i s hopt hcapital hslack htrans hothers
  have hc0 : 0 < X.firmConsumption i 0 h0 :=
    (hopt.1.1 0 h0 (initial_history_admissible P)).1
  have hu0 : crraMarginal P.entrepreneurRiskAversion
      (X.firmConsumption i 0 h0) ≠ 0 := by
    unfold crraMarginal
    exact ne_of_gt (Real.rpow_pos_of_pos hc0 _)
  have hpay := gain_is_primal_return P X i s
  change crraMarginal P.entrepreneurRiskAversion
        (X.firmConsumption i 0 h0) * X.capitalPrice 0 h0 =
      P.entrepreneurDiscount *
        (crraMarginal P.entrepreneurRiskAversion
          (X.firmConsumption i 1 h1) *
          dateOneMarginalCapitalPayoff P X i (firmPlanOfAllocation X i) h1)
    at heuler
  rw [hpay] at heuler
  unfold capitalEulerPrimalGap
  dsimp only
  change X.capitalPrice 0 h0 -
    (P.entrepreneurDiscount *
      crraMarginal P.entrepreneurRiskAversion (X.firmConsumption i 1 h1) /
      crraMarginal P.entrepreneurRiskAversion (X.firmConsumption i 0 h0)) *
      (X.inputPrice 1 h1 *
        (P.aggregateProductivity s * P.productivity i) * P.alpha *
        (X.capital i 0 h0) ^ (P.alpha - 1) *
        (X.labor i 1 h1) ^ P.beta +
        (1 - P.depreciation) * X.capitalPrice 1 h1) = 0
  field_simp [hu0]
  nlinarith [heuler]

/-- Once the primal gap vanishes, a zero collateralDual carrier makes the
    structural residual zero. This does NOT establish that an arbitrary
    existing Allocation.collateralDual satisfies complementary slackness. -/
theorem exists_zeroDual_carrier_rootEuler
    (P : Primitives S) (I : InheritedState)
    (X : Allocation S) (i : FirmType) (s : S)
    (hopt : FirmOptimal P I X i)
    (hcapital : ∀ h : History S 0,
      FirmHistoryAdmissible P 0 h → 0 < X.capital i 0 h)
    (hslack : DateZeroSlackBorrower P X i)
    (htrans : P.tree.transition P.tree.initial s = 1)
    (hothers : ∀ v : S, v ≠ s →
      P.tree.transition P.tree.initial v = 0) :
    localFirmCapitalEulerResidual P
      (replaceCollateralDual X (fun _ _ _ => 0))
      i 0 (rootHistory P.tree) s = 0 := by
  have hgap := firmOptimal_deterministic_root_primalGap_zero
    P I X i s hopt hcapital hslack htrans hothers
  rw [capitalEulerResidual_eq_primalGap_sub_dual]
  rw [capitalEulerPrimalGap_replaceDual]
  change capitalEulerPrimalGap P X i 0 (rootHistory P.tree) s -
    0 * capitalEulerCollateralUnit P X i 0 (rootHistory P.tree) s = 0
  simpa using hgap

end ProposedDateZeroPrimalKKTBridge
end Ventura26LiquidityAllocation
