import Ventura26LiquidityAllocation.DateZeroCapitalUtilityCandidate

/-!
# Common local feasibility radius in the strictly slack date-zero regime

The source requires robust collateral at EACH possible child state.
Strict slack for type i, positive date-zero capital and positivity of
firm consumption give open sign conditions under a capital perturbation.
Since History S 0, History S 1 and S itself are finite, the conjunction
of these conditions holds in a common neighborhood of epsilon=0.

We separately record continuity of the date-one realized capital gain at
epsilon=0, because nonlinear rpow continuity at positive capital is an
analytic obligation. No derivative or KKT condition is assumed.

This module proves an EXISTING real radius on which the full source
FirmFeasible, FirmObjectiveWellDefined, and utility optimality bound hold
simultaneously. It does not assert equilibrium existence or Euler FOC.
-/

namespace Ventura26LiquidityAllocation
namespace ProposedDateZeroCapitalNeighborhood

open Filter Topology
open ProposedDateZeroCapitalDeviation
open ProposedDateZeroCapitalUtility

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- Source strict slack plus date-one gain continuity yields an open,
    TWO-SIDED set of local capital perturbations respecting every statewise
    robust collateral inequality and both consumption constraints. -/
theorem localBounds_eventually_of_strict_slack
    (P : Primitives S) (I : InheritedState)
    (X : Allocation S) (i : FirmType)
    (hfeas : FirmFeasible P I X i (firmPlanOfAllocation X i))
    (hcapital : ∀ h : History S 0,
      FirmHistoryAdmissible P 0 h → 0 < X.capital i 0 h)
    (hslack : DateZeroSlackBorrower P X i)
    (hgainContinuous : ∀ h : History S 1,
      FirmHistoryAdmissible P 1 h →
      ContinuousAt (fun epsilon : ℝ =>
        dateOneCapitalGain P X i (firmPlanOfAllocation X i) epsilon h) 0) :
    ∀ᶠ (epsilon : ℝ) in 𝓝 0,
      CapitalVariationLocalBounds P X i (firmPlanOfAllocation X i) epsilon := by
  have hdate0 : ∀ᶠ (epsilon : ℝ) in 𝓝 0,
      ∀ h : History S 0, FirmHistoryAdmissible P 0 h →
        0 < X.firmConsumption i 0 h - X.capitalPrice 0 h * epsilon ∧
        0 ≤ X.capital i 0 h + epsilon ∧
        RobustCollateral (P.pledgeability i) P.depreciation
          (X.loanRate 0 h) (X.loan i 0 h) (X.capital i 0 h + epsilon)
          (fun s ↦ 0 < P.tree.transition (currentState h) s)
          (fun s ↦ X.inflation 1 (childHistory h s))
          (fun s ↦ X.capitalPrice 1 (childHistory h s)) := by
    rw [eventually_all]
    intro h
    by_cases hh : FirmHistoryAdmissible P 0 h
    · have hcons : ∀ᶠ (epsilon : ℝ) in 𝓝 0,
          0 < X.firmConsumption i 0 h - X.capitalPrice 0 h * epsilon := by
        have hc : Continuous
            (fun epsilon : ℝ =>
              X.firmConsumption i 0 h - X.capitalPrice 0 h * epsilon) := by
          fun_prop
        have hb :
            0 < X.firmConsumption i 0 h - X.capitalPrice 0 h * (0 : ℝ) := by
          simpa using (hfeas.1 0 h hh).1
        exact (hc.tendsto 0).eventually (eventually_gt_nhds hb)
      have hcap : ∀ᶠ (epsilon : ℝ) in 𝓝 0,
          0 < X.capital i 0 h + epsilon := by
        have hc : Continuous (fun epsilon : ℝ => X.capital i 0 h + epsilon) :=
          by fun_prop
        have hb : 0 < X.capital i 0 h + (0 : ℝ) := by
          simpa using hcapital h hh
        exact (hc.tendsto 0).eventually (eventually_gt_nhds hb)
      have hcoll : ∀ᶠ (epsilon : ℝ) in 𝓝 0,
          RobustCollateral (P.pledgeability i) P.depreciation
            (X.loanRate 0 h) (X.loan i 0 h) (X.capital i 0 h + epsilon)
            (fun s ↦ 0 < P.tree.transition (currentState h) s)
            (fun s ↦ X.inflation 1 (childHistory h s))
            (fun s ↦ X.capitalPrice 1 (childHistory h s)) := by
        change ∀ᶠ (epsilon : ℝ) in 𝓝 0, ∀ s,
          0 < P.tree.transition (currentState h) s →
          X.loanRate 0 h * X.loan i 0 h ≤
            P.pledgeability i * (1 - P.depreciation) *
              (X.inflation 1 (childHistory h s) *
                X.capitalPrice 1 (childHistory h s)) *
                (X.capital i 0 h + epsilon)
        rw [eventually_all]
        intro s
        by_cases hs : 0 < P.tree.transition (currentState h) s
        · have hc : Continuous
              (fun epsilon : ℝ =>
                P.pledgeability i * (1 - P.depreciation) *
                  (X.inflation 1 (childHistory h s) *
                    X.capitalPrice 1 (childHistory h s)) *
                    (X.capital i 0 h + epsilon)) := by
            fun_prop
          have hb : X.loanRate 0 h * X.loan i 0 h <
              P.pledgeability i * (1 - P.depreciation) *
                (X.inflation 1 (childHistory h s) *
                  X.capitalPrice 1 (childHistory h s)) *
                  (X.capital i 0 h + (0 : ℝ)) := by
            simpa using (hslack h).2.2 s hs
          exact ((hc.tendsto 0).eventually (eventually_gt_nhds hb)).mono
            (fun _ hgt _ => hgt.le)
        · exact Filter.Eventually.of_forall
            (fun _ hpossible => (hs hpossible).elim)
      filter_upwards [hcons, hcap, hcoll] with epsilon hc hk hco
      exact fun _ => ⟨hc, hk.le, hco⟩
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
      have hc : ContinuousAt
          (fun epsilon : ℝ =>
            X.firmConsumption i 1 h +
              dateOneCapitalGain P X i (firmPlanOfAllocation X i) epsilon h)
          0 :=
        continuousAt_const.add (hgainContinuous h hh)
      have hb :
          0 < X.firmConsumption i 1 h +
            dateOneCapitalGain P X i (firmPlanOfAllocation X i) 0 h := by
        simpa [hgainZero] using (hfeas.1 1 h hh).1
      exact (hc.eventually (eventually_gt_nhds hb)).mono
        (fun _ hpos _ => hpos)
    · exact Filter.Eventually.of_forall (fun _ hgood => (hh hgood).elim)
  filter_upwards [hdate0, hdate1] with epsilon h0 h1
  exact ⟨h0, h1⟩

/-- Literal positive radius, source global feasibility, objective convergence
    and dominance for every |epsilon| < radius. -/
theorem exists_twoSided_feasible_optimality_radius
    (P : Primitives S) (I : InheritedState)
    (X : Allocation S) (i : FirmType)
    (hopt : FirmOptimal P I X i)
    (hcapital : ∀ h : History S 0,
      FirmHistoryAdmissible P 0 h → 0 < X.capital i 0 h)
    (hslack : DateZeroSlackBorrower P X i)
    (hgainContinuous : ∀ h : History S 1,
      FirmHistoryAdmissible P 1 h →
      ContinuousAt (fun epsilon : ℝ =>
        dateOneCapitalGain P X i (firmPlanOfAllocation X i) epsilon h) 0) :
    ∃ radius : ℝ, 0 < radius ∧
      ∀ epsilon : ℝ, |epsilon| < radius →
        FirmFeasible P I X i
          (capitalDateZeroVariation P X i (firmPlanOfAllocation X i) epsilon) ∧
        FirmObjectiveWellDefined P
          (capitalDateZeroVariation P X i (firmPlanOfAllocation X i) epsilon) ∧
        discountedFirmUtility P
          (capitalDateZeroVariation P X i (firmPlanOfAllocation X i) epsilon) ≤
          discountedFirmUtility P (firmPlanOfAllocation X i) := by
  have hev := localBounds_eventually_of_strict_slack P I X i
    hopt.1 hcapital hslack hgainContinuous
  obtain ⟨radius, hradius, hball⟩ := (Metric.eventually_nhds_iff).mp hev
  refine ⟨radius, hradius, ?_⟩
  intro epsilon hsmall
  have hdist : dist epsilon (0 : ℝ) < radius := by
    simpa [Real.dist_eq] using hsmall
  have hloc : CapitalVariationLocalBounds P X i
      (firmPlanOfAllocation X i) epsilon := hball hdist
  refine ⟨?_, ?_, ?_⟩
  · exact capitalDateZeroVariation_feasible P I X i
      (firmPlanOfAllocation X i) epsilon hopt.1 hloc
  · exact (capitalVariation_objectiveWellDefined_iff P X i
      (firmPlanOfAllocation X i) epsilon).2 hopt.2.1
  · exact firmOptimal_dominates_capitalDeviation P I X i epsilon hopt hloc

end ProposedDateZeroCapitalNeighborhood
end Ventura26LiquidityAllocation
