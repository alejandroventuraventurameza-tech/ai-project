import Ventura26LiquidityAllocation.OneSidedCollateralMonotonicityCandidate
import Ventura26LiquidityAllocation.DateZeroCapitalGainContinuityCandidate

/-!
# Right-sided feasible capital variations from source FirmOptimal

Even with binding robust collateral, positive current capital and nonnegative
collateral payoff coefficients admit sufficiently small capital increases.
The perturbation is the literal source plan; budgets, wealth recursion, and
the infinite-horizon objective domain are not assumed as independent
hypotheses. This is not yet the KKT inequality.
-/

namespace Ventura26LiquidityAllocation
namespace ProposedDateZeroOneSidedFeasibility

open Filter Topology
open ProposedDateZeroCapitalDeviation
open ProposedDateZeroCapitalUtility
open ProposedDateZeroCapitalGainContinuity
open ProposedOneSidedCollateralMonotonicity

variable {S : Type*} [Fintype S] [DecidableEq S]

theorem exists_right_feasible_optimality_radius
    (P : Primitives S) (I : InheritedState)
    (X : Allocation S) (i : FirmType)
    (hopt : FirmOptimal P I X i)
    (hcapital : ∀ h : History S 0,
      FirmHistoryAdmissible P 0 h → 0 < X.capital i 0 h)
    (hcoeff : ∀ h : History S 0,
      FirmHistoryAdmissible P 0 h → ∀ s : S,
      0 < P.tree.transition (currentState h) s →
      0 ≤ P.pledgeability i * (1 - P.depreciation) *
        (X.inflation 1 (childHistory h s) *
          X.capitalPrice 1 (childHistory h s))) :
    ∃ radius : ℝ, 0 < radius ∧
      ∀ epsilon : ℝ, 0 ≤ epsilon → epsilon < radius →
        FirmFeasible P I X i
          (capitalDateZeroVariation P X i (firmPlanOfAllocation X i) epsilon) ∧
        FirmObjectiveWellDefined P
          (capitalDateZeroVariation P X i (firmPlanOfAllocation X i) epsilon) ∧
        discountedFirmUtility P
          (capitalDateZeroVariation P X i (firmPlanOfAllocation X i) epsilon) ≤
          discountedFirmUtility P (firmPlanOfAllocation X i) := by
  have hfeas : FirmFeasible P I X i (firmPlanOfAllocation X i) := hopt.1
  rcases hfeas with ⟨hpos, _hface, _hbudget, hcoll, _hwealth0, _hwealthNext⟩
  have hdate0 : ∀ᶠ (epsilon : ℝ) in 𝓝 0,
      ∀ h : History S 0, FirmHistoryAdmissible P 0 h →
        0 < X.firmConsumption i 0 h - X.capitalPrice 0 h * epsilon := by
    rw [eventually_all]
    intro h
    by_cases hh : FirmHistoryAdmissible P 0 h
    · have hc : Continuous
          (fun epsilon : ℝ =>
            X.firmConsumption i 0 h - X.capitalPrice 0 h * epsilon) := by
          fun_prop
      have hb :
          0 < X.firmConsumption i 0 h - X.capitalPrice 0 h * (0 : ℝ) := by
        simpa using (hpos 0 h hh).1
      exact ((hc.tendsto 0).eventually (eventually_gt_nhds hb)).mono
        (fun _ hp _ => hp)
    · exact Filter.Eventually.of_forall (fun _ hgood => (hh hgood).elim)
  have hdate1 : ∀ᶠ (epsilon : ℝ) in 𝓝 0,
      ∀ h : History S 1, FirmHistoryAdmissible P 1 h →
        0 < X.firmConsumption i 1 h +
          dateOneCapitalGain P X i (firmPlanOfAllocation X i) epsilon h := by
    rw [eventually_all]
    intro h
    by_cases hh : FirmHistoryAdmissible P 1 h
    · have hgainZero :
          dateOneCapitalGain P X i (firmPlanOfAllocation X i) 0 h = 0 := by
        simp [dateOneCapitalGain]
      have hprev : FirmHistoryAdmissible P 0 (previousHistory h) :=
        admissible_predecessor_of_admissible_child P h hh
      have hgain : ContinuousAt (fun epsilon : ℝ =>
          dateOneCapitalGain P X i (firmPlanOfAllocation X i) epsilon h) 0 := by
        apply dateOneCapitalGain_continuousAt_zero P X i
          (firmPlanOfAllocation X i) h
        change 0 < X.capital i 0 (previousHistory h)
        exact hcapital _ hprev
      have hc : ContinuousAt (fun epsilon : ℝ =>
          X.firmConsumption i 1 h +
            dateOneCapitalGain P X i (firmPlanOfAllocation X i) epsilon h) 0 :=
        continuousAt_const.add hgain
      have hb :
          0 < X.firmConsumption i 1 h +
            dateOneCapitalGain P X i (firmPlanOfAllocation X i) 0 h := by
        simpa [hgainZero] using (hpos 1 h hh).1
      exact (hc.eventually (eventually_gt_nhds hb)).mono
        (fun _ hp _ => hp)
    · exact Filter.Eventually.of_forall (fun _ hgood => (hh hgood).elim)
  have hev : ∀ᶠ (epsilon : ℝ) in 𝓝 0,
      0 ≤ epsilon →
        CapitalVariationLocalBounds P X i
          (firmPlanOfAllocation X i) epsilon := by
    filter_upwards [hdate0, hdate1] with epsilon hc0 hc1
    intro heps
    refine ⟨?_, ?_⟩
    · intro h hh
      have hc : 0 < X.firmConsumption i 0 h -
          X.capitalPrice 0 h * epsilon := hc0 h hh
      have hk : 0 ≤ X.capital i 0 h + epsilon :=
        add_nonneg (hpos 0 h hh).2.1 heps
      have hcoll0 : RobustCollateral (P.pledgeability i) P.depreciation
          (X.loanRate 0 h) (X.loan i 0 h) (X.capital i 0 h)
          (fun s ↦ 0 < P.tree.transition (currentState h) s)
          (fun s ↦ X.inflation 1 (childHistory h s))
          (fun s ↦ X.capitalPrice 1 (childHistory h s)) :=
        hcoll 0 h hh
      have hcoll1 := robustCollateral_capital_mono
        (P.pledgeability i) P.depreciation
        (X.loanRate 0 h) (X.loan i 0 h) (X.capital i 0 h) epsilon
        (fun s ↦ 0 < P.tree.transition (currentState h) s)
        (fun s ↦ X.inflation 1 (childHistory h s))
        (fun s ↦ X.capitalPrice 1 (childHistory h s))
        hcoll0 heps (hcoeff h hh)
      change 0 < (firmPlanOfAllocation X i).consumption 0 h -
        X.capitalPrice 0 h * epsilon ∧
        0 ≤ (firmPlanOfAllocation X i).capital 0 h + epsilon ∧
        RobustCollateral (P.pledgeability i) P.depreciation
          (X.loanRate 0 h) ((firmPlanOfAllocation X i).loan 0 h)
          ((firmPlanOfAllocation X i).capital 0 h + epsilon)
          (fun s ↦ 0 < P.tree.transition (currentState h) s)
          (fun s ↦ X.inflation 1 (childHistory h s))
          (fun s ↦ X.capitalPrice 1 (childHistory h s))
      exact ⟨hc, hk, hcoll1⟩
    · intro h hh
      exact hc1 h hh
  obtain ⟨radius, hradius, hball⟩ := (Metric.eventually_nhds_iff).mp hev
  refine ⟨radius, hradius, ?_⟩
  intro epsilon heps hsmall
  have hdist : dist epsilon (0 : ℝ) < radius := by
    simpa [Real.dist_eq, abs_of_nonneg heps] using hsmall
  have hloc : CapitalVariationLocalBounds P X i
      (firmPlanOfAllocation X i) epsilon := hball hdist heps
  refine ⟨?_, ?_, ?_⟩
  · exact capitalDateZeroVariation_feasible P I X i
      (firmPlanOfAllocation X i) epsilon hopt.1 hloc
  · exact (capitalVariation_objectiveWellDefined_iff P X i
      (firmPlanOfAllocation X i) epsilon).2 hopt.2.1
  · exact firmOptimal_dominates_capitalDeviation P I X i epsilon hopt hloc

end ProposedDateZeroOneSidedFeasibility
end Ventura26LiquidityAllocation
