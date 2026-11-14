import Ventura26LiquidityAllocation.DateZeroOneSidedDeterministicCostCandidate
import Ventura26LiquidityAllocation.ScalarKKTMultiplierConstructionCandidate

/-!
# A nonnegative normalized primal Euler gap from one-sided firm optimality

In a deterministic one-successor continuation, source optimality and feasible
nonnegative capital variations imply that the primal Euler gap is nonnegative.
With a positive collateral unit, a scalar nonnegative KKT-row multiplier exists.
This construction does not identify the Allocation.collateralDual field nor
prove a full equilibrium or shadow-price characterization.
-/

namespace Ventura26LiquidityAllocation
namespace ProposedDateZeroOneSidedPrimalGap

open ProposedDateZeroOneSidedDeterministicCost
open ProposedDateZeroCapitalEulerDerivative
open ProposedProposition42KKTIdentification
open ProposedScalarKKTMultiplierConstruction

variable {S : Type*} [Fintype S] [DecidableEq S]

private theorem marginal_gain_eq_primal_return
    (P : Primitives S) (X : Allocation S) (i : FirmType) (s : S) :
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
  have hcur : currentState (childHistory (rootHistory P.tree) s) = s := by
    rfl
  simp only [dateOneMarginalCapitalPayoff, firmPlanOfAllocation, hp, hcur]

/-- A one-sided optimum implies that date-zero investment costs weakly
    exceed discounted marginal returns at the positive-probability successor. -/
theorem firmOptimal_oneSided_root_primalGap_nonneg
    (P : Primitives S) (I : InheritedState)
    (X : Allocation S) (i : FirmType) (s : S)
    (hopt : FirmOptimal P I X i)
    (hcapital : ∀ h : History S 0,
      FirmHistoryAdmissible P 0 h → 0 < X.capital i 0 h)
    (hcoeff : ∀ h : History S 0,
      FirmHistoryAdmissible P 0 h → ∀ v : S,
      0 < P.tree.transition (currentState h) v →
      0 ≤ P.pledgeability i * (1 - P.depreciation) *
        (X.inflation 1 (childHistory h v) *
          X.capitalPrice 1 (childHistory h v)))
    (hw0 : P.tree.historyWeight 0 (rootHistory P.tree) = 1)
    (hz0 : ∀ h : History S 0, h ≠ rootHistory P.tree →
      P.tree.historyWeight 0 h = 0)
    (hw1 : P.tree.historyWeight 1
        (childHistory (rootHistory P.tree) s) = 1)
    (hz1 : ∀ h : History S 1,
      h ≠ childHistory (rootHistory P.tree) s →
      P.tree.historyWeight 1 h = 0) :
    0 ≤ capitalEulerPrimalGap P X i 0 (rootHistory P.tree) s := by
  let h0 : History S 0 := rootHistory P.tree
  let h1 : History S 1 := childHistory h0 s
  have hcost := firmOptimal_oneSided_singleSuccessor_cost_ge_benefit
    P I X i h0 h1 hopt hcapital hcoeff hw0 hz0 hw1 hz1
  have hadm : FirmHistoryAdmissible P 0 h0 := by
    unfold FirmHistoryAdmissible
    rw [hw0]
    norm_num
  have hc0 : 0 < X.firmConsumption i 0 h0 :=
    (hopt.1.1 0 h0 hadm).1
  have hu : 0 < crraMarginal P.entrepreneurRiskAversion
      (X.firmConsumption i 0 h0) := by
    unfold crraMarginal
    exact Real.rpow_pos_of_pos hc0 _
  have hpay := marginal_gain_eq_primal_return P X i s
  rw [hpay] at hcost
  have hbound :
      (P.entrepreneurDiscount *
        crraMarginal P.entrepreneurRiskAversion (X.firmConsumption i 1 h1) *
        (X.inputPrice 1 h1 *
          (P.aggregateProductivity s * P.productivity i) * P.alpha *
          (X.capital i 0 h0) ^ (P.alpha - 1) *
          (X.labor i 1 h1) ^ P.beta +
          (1 - P.depreciation) * X.capitalPrice 1 h1)) /
        crraMarginal P.entrepreneurRiskAversion (X.firmConsumption i 0 h0) ≤
      X.capitalPrice 0 h0 := by
    apply (div_le_iff₀ hu).2
    nlinarith [hcost]
  unfold capitalEulerPrimalGap
  change 0 ≤ X.capitalPrice 0 h0 -
    (P.entrepreneurDiscount *
      crraMarginal P.entrepreneurRiskAversion (X.firmConsumption i 1 h1) /
      crraMarginal P.entrepreneurRiskAversion (X.firmConsumption i 0 h0)) *
      (X.inputPrice 1 h1 *
        (P.aggregateProductivity s * P.productivity i) * P.alpha *
        (X.capital i 0 h0) ^ (P.alpha - 1) *
        (X.labor i 1 h1) ^ P.beta +
        (1 - P.depreciation) * X.capitalPrice 1 h1)
  have hrearrange :
      (P.entrepreneurDiscount *
        crraMarginal P.entrepreneurRiskAversion (X.firmConsumption i 1 h1) /
        crraMarginal P.entrepreneurRiskAversion (X.firmConsumption i 0 h0)) *
        (X.inputPrice 1 h1 *
          (P.aggregateProductivity s * P.productivity i) * P.alpha *
          (X.capital i 0 h0) ^ (P.alpha - 1) *
          (X.labor i 1 h1) ^ P.beta +
          (1 - P.depreciation) * X.capitalPrice 1 h1) =
      (P.entrepreneurDiscount *
        crraMarginal P.entrepreneurRiskAversion (X.firmConsumption i 1 h1) *
        (X.inputPrice 1 h1 *
          (P.aggregateProductivity s * P.productivity i) * P.alpha *
          (X.capital i 0 h0) ^ (P.alpha - 1) *
          (X.labor i 1 h1) ^ P.beta +
          (1 - P.depreciation) * X.capitalPrice 1 h1)) /
        crraMarginal P.entrepreneurRiskAversion (X.firmConsumption i 0 h0) := by
    ring
  rw [hrearrange]
  exact sub_nonneg.mpr hbound

end ProposedDateZeroOneSidedPrimalGap
end Ventura26LiquidityAllocation
