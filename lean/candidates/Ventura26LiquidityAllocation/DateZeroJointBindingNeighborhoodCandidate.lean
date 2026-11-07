import Ventura26LiquidityAllocation.DateZeroJointBindingCollateralCandidate
import Ventura26LiquidityAllocation.DateZeroJointCapitalLoanUtilityCandidate
import Ventura26LiquidityAllocation.DateZeroCapitalGainContinuityCandidate

/-!
# Two-sided locally feasible capital/loan tangent at a binding collateral node

The source deterministic Markov calendar gives only one admissible root and
one supported successor. At a binding borrower, the joint tangent
    dk = R_0^L * epsilon, db = Gamma_1 * epsilon
leaves robust collateral exactly equal for EVERY epsilon. Positivity of
initial capital, initial loan, and firm consumption remains true for small
positive AND negative epsilon by continuity. Date-one consumption uses the
literal nonlinear capital gain and changed real debt repayment.

A common neighborhood radius is extracted from finite-state continuity;
no Euler, shadow multiplier, or first-order condition is postulated here.
-/

namespace Ventura26LiquidityAllocation
namespace ProposedDateZeroJointBindingNeighborhood

open Filter Topology
open ProposedDateZeroJointCapitalLoanDeviation
open ProposedDateZeroCapitalDeviation
open ProposedDateZeroJointCapitalLoanFeasibility
open ProposedDateZeroJointBindingCollateral
open ProposedDateZeroCapitalGainContinuity
open ProposedDateZeroDeterministicMarkovBridge
open ProposedDateZeroCalendarEulerBridge
open ProposedProposition42KKTIdentification

variable {S : Type*} [Fintype S] [DecidableEq S]

theorem exists_twoSided_binding_jointTangent_radius
    (P : Primitives S) (I : InheritedState)
    (X : Allocation S) (i : FirmType)
    (dateOne recurrent : S)
    (hcalendar : DeterministicBridgeCalendar P dateOne recurrent)
    (hopt : FirmOptimal P I X i)
    (hbinding : DateZeroBindingBorrower P X i)
    (hcapital : ∀ h : History S 0,
      FirmHistoryAdmissible P 0 h → 0 < X.capital i 0 h) :
    ∃ radius : ℝ, 0 < radius ∧
      ∀ epsilon : ℝ, |epsilon| < radius →
        JointCapitalLoanVariationLocalBounds P X i
          (firmPlanOfAllocation X i)
          (X.loanRate 0 (rootHistory P.tree) * epsilon)
          (capitalEulerCollateralUnit P X i 0
            (rootHistory P.tree) dateOne * epsilon) := by
  let hroot : History S 0 := rootHistory P.tree
  let p : FirmPlan S := firmPlanOfAllocation X i
  let R : ℝ := X.loanRate 0 hroot
  let Gamma : ℝ := capitalEulerCollateralUnit P X i 0 hroot dateOne
  have htrans : P.tree.transition P.tree.initial dateOne = 1 :=
    hcalendar.2.2.2.1
  have hothers : ∀ v : S, v ≠ dateOne →
      P.tree.transition P.tree.initial v = 0 :=
    sourceCalendar_other_transitions_zero P dateOne recurrent hcalendar
  obtain ⟨_hw0, hz0, _hw1, _hz1⟩ :=
    deterministic_historyWeight_package P dateOne htrans hothers
  have hroot_of_adm : ∀ h : History S 0,
      FirmHistoryAdmissible P 0 h → h = hroot := by
    intro h hh
    by_contra hne
    have hz : P.tree.historyWeight 0 h = 0 := hz0 h hne
    have hp : 0 < P.tree.historyWeight 0 h := hh
    rw [hz] at hp
    exact (lt_irrefl (0 : ℝ)) hp
  have hrobust : ∀ epsilon : ℝ,
      ∀ h : History S 0, FirmHistoryAdmissible P 0 h →
      RobustCollateral (P.pledgeability i) P.depreciation
        (X.loanRate 0 h) (X.loan i 0 h + Gamma * epsilon)
        (X.capital i 0 h + R * epsilon)
        (fun s => 0 < P.tree.transition (currentState h) s)
        (fun s => X.inflation 1 (childHistory h s))
        (fun s => X.capitalPrice 1 (childHistory h s)) := by
    intro epsilon h hh
    have heq : h = hroot := hroot_of_adm h hh
    subst h
    simpa [hroot, R, Gamma, rootHistory, currentState] using
      (binding_sourceCalendar_robustCollateral_joint_tangent
        P X i dateOne recurrent hcalendar hbinding epsilon)
  have hdate0 : ∀ᶠ epsilon : ℝ in 𝓝 0,
      ∀ h : History S 0, FirmHistoryAdmissible P 0 h →
        0 < X.firmConsumption i 0 h -
          X.capitalPrice 0 h * (R * epsilon) + Gamma * epsilon ∧
        0 ≤ X.capital i 0 h + R * epsilon ∧
        0 ≤ X.loan i 0 h + Gamma * epsilon := by
    rw [eventually_all]
    intro h
    by_cases hh : FirmHistoryAdmissible P 0 h
    · have hc : ContinuousAt (fun epsilon : ℝ =>
          X.firmConsumption i 0 h -
            X.capitalPrice 0 h * (R * epsilon) +
              Gamma * epsilon) 0 := by fun_prop
      have hk : ContinuousAt (fun epsilon : ℝ =>
          X.capital i 0 h + R * epsilon) 0 := by fun_prop
      have hb : ContinuousAt (fun epsilon : ℝ =>
          X.loan i 0 h + Gamma * epsilon) 0 := by fun_prop
      have hc0 :
          0 < X.firmConsumption i 0 h -
            X.capitalPrice 0 h * (R * (0 : ℝ)) + Gamma * 0 := by
        simpa using (hopt.1.1 0 h hh).1
      have hk0 : 0 < X.capital i 0 h + R * (0 : ℝ) := by
        simpa using hcapital h hh
      have hb0 : 0 < X.loan i 0 h + Gamma * (0 : ℝ) := by
        simpa using (hbinding h).1
      have hce := hc.eventually (eventually_gt_nhds hc0)
      have hke := hk.eventually (eventually_gt_nhds hk0)
      have hbe := hb.eventually (eventually_gt_nhds hb0)
      filter_upwards [hce, hke, hbe] with epsilon hce hke hbe
      exact fun _ => ⟨hce, hke.le, hbe.le⟩
    · exact Filter.Eventually.of_forall
        (fun _ hgood => (hh hgood).elim)
  have hdate1 : ∀ᶠ epsilon : ℝ in 𝓝 0,
      ∀ h : History S 1, FirmHistoryAdmissible P 1 h →
        0 < X.firmConsumption i 1 h +
          dateOneJointGain P X i p (R * epsilon) (Gamma * epsilon) h := by
    rw [eventually_all]
    intro h
    by_cases hh : FirmHistoryAdmissible P 1 h
    · have hprev : FirmHistoryAdmissible P 0 (previousHistory h) :=
        admissible_predecessor_of_admissible_child P h hh
      have hposcap : 0 < p.capital 0 (previousHistory h) := by
        change 0 < X.capital i 0 (previousHistory h)
        exact hcapital _ hprev
      have hmap : ContinuousAt (fun epsilon : ℝ => R * epsilon) 0 := by
        fun_prop
      have hgainAt :
          ContinuousAt (fun z : ℝ => dateOneCapitalGain P X i p z h)
            (R * (0 : ℝ)) := by
        simpa using
          dateOneCapitalGain_continuousAt_zero P X i p h hposcap
      have hgain : ContinuousAt (fun epsilon : ℝ =>
          dateOneCapitalGain P X i p (R * epsilon) h) 0 :=
        hgainAt.comp hmap
      have hloan : ContinuousAt (fun epsilon : ℝ =>
          X.loanRate 0 (previousHistory h) *
            (Gamma * epsilon) / X.inflation 1 h) 0 := by
        fun_prop
      have hjoint : ContinuousAt (fun epsilon : ℝ =>
          dateOneJointGain P X i p (R * epsilon) (Gamma * epsilon) h) 0 := by
        change ContinuousAt (fun epsilon : ℝ =>
          dateOneCapitalGain P X i p (R * epsilon) h -
            X.loanRate 0 (previousHistory h) *
              (Gamma * epsilon) / X.inflation 1 h) 0
        exact hgain.sub hloan
      have hzero :
          dateOneJointGain P X i p (R * (0 : ℝ)) (Gamma * 0) h = 0 := by
        simp [dateOneJointGain, dateOneCapitalGain]
      have hc : ContinuousAt (fun epsilon : ℝ =>
          X.firmConsumption i 1 h +
            dateOneJointGain P X i p (R * epsilon) (Gamma * epsilon) h) 0 :=
        continuousAt_const.add hjoint
      have hc0 :
          0 < X.firmConsumption i 1 h +
            dateOneJointGain P X i p (R * (0 : ℝ)) (Gamma * 0) h := by
        simpa [hzero] using (hopt.1.1 1 h hh).1
      exact (hc.eventually (eventually_gt_nhds hc0)).mono
        (fun _ hpos _ => hpos)
    · exact Filter.Eventually.of_forall
        (fun _ hgood => (hh hgood).elim)
  have hlocal : ∀ᶠ epsilon : ℝ in 𝓝 0,
      JointCapitalLoanVariationLocalBounds P X i p
        (R * epsilon) (Gamma * epsilon) := by
    filter_upwards [hdate0, hdate1] with epsilon h0 h1
    refine ⟨?_, ?_⟩
    · intro h hh
      obtain ⟨hc, hk, hb⟩ := h0 h hh
      change 0 < p.consumption 0 h -
          X.capitalPrice 0 h * (R * epsilon) + Gamma * epsilon ∧
        0 ≤ p.capital 0 h + R * epsilon ∧
        0 ≤ p.loan 0 h + Gamma * epsilon ∧
        RobustCollateral (P.pledgeability i) P.depreciation
          (X.loanRate 0 h) (p.loan 0 h + Gamma * epsilon)
          (p.capital 0 h + R * epsilon)
          (fun s => 0 < P.tree.transition (currentState h) s)
          (fun s => X.inflation 1 (childHistory h s))
          (fun s => X.capitalPrice 1 (childHistory h s))
      exact ⟨hc, hk, hb, hrobust epsilon h hh⟩
    · intro h hh
      exact h1 h hh
  obtain ⟨radius, hradius, hball⟩ :=
    (Metric.eventually_nhds_iff).mp hlocal
  refine ⟨radius, hradius, ?_⟩
  intro epsilon hsmall
  have hdist : dist epsilon (0 : ℝ) < radius := by
    simpa [Real.dist_eq] using hsmall
  exact hball hdist

end ProposedDateZeroJointBindingNeighborhood
end Ventura26LiquidityAllocation
