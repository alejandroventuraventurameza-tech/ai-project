import Ventura26LiquidityAllocation.DateZeroCapitalEulerDerivativeCandidate

/-!
# Expected capital Euler from actual FirmOptimal and a feasible deviation

No Euler equality is assumed. Under the source FirmOptimal, positive
predetermined capital at admissible histories and strict date-zero collateral
slack, we derive expected marginal capital Euler stationarity by:
  (1) deriving weighted CRRA derivatives on finite Markov support;
  (2) deriving the marginal capital return in each successor;
  (3) eliminating the discounted utility tail exactly (earlier module);
  (4) using the two-sided admissible radius (earlier audited module);
  (5) applying Fermat's theorem to the original objective.

Zero-probability histories are explicitly handled and need no consumption
positivity. In the unrestricted Markov case the result is expectation-weighted,
NOT the single-successor residual of the deterministic bridge. The latter
specialization is a separate source-reconciliation obligation.

No new economic KKT/Euler assumptions, sorry, admit, or custom axioms.
-/

namespace Ventura26LiquidityAllocation
namespace ProposedDateZeroCapitalExpectedEuler

open Filter Topology
open ProposedDateZeroCapitalDeviation
open ProposedDateZeroCapitalUtility
open ProposedDateZeroCapitalNeighborhood
open ProposedDateZeroCapitalGainContinuity
open ProposedDateZeroCapitalEulerDerivative

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- Nonnegativity comes from the primitive transition law alone. -/
private theorem historyWeight_nonneg
    (T : FiniteMarkovTree S) :
    ∀ t (h : History S t), 0 ≤ T.historyWeight t h := by
  intro t
  induction t with
  | zero =>
    intro h
    change 0 ≤ (if currentState h = T.initial then (1 : ℝ) else 0)
    split <;> norm_num
  | succ t ih =>
    intro h
    change 0 ≤ T.historyWeight t (previousHistory h) *
      T.transition (currentState (previousHistory h)) (currentState h)
    exact mul_nonneg (ih _) (T.transition_nonneg _ _)

/-- A zero-probability term is identically zero even if its underlying
    infeasible history has no positive consumption. -/
private theorem weightedCrra_hasDerivAt
    (sigma weight c d : ℝ) (g : ℝ → ℝ)
    (hg : HasDerivAt g d 0)
    (hzero : g 0 = c)
    (hpos : weight ≠ 0 → 0 < c) :
    HasDerivAt (fun epsilon : ℝ => weight * crraUtility sigma (g epsilon))
      (weight * (crraMarginal sigma c * d)) 0 := by
  by_cases hw : weight = 0
  · subst weight
    simpa using (hasDerivAt_const (0 : ℝ) (0 : ℝ))
  · have hc : 0 < g 0 := by simpa only [hzero] using hpos hw
    have hd :=
      ((crraUtility_hasDerivAt sigma (g 0) hc).comp 0 hg).const_mul weight
    simpa only [hzero] using hd

noncomputable def dateZeroCapitalMarginalCost
    (P : Primitives S) (X : Allocation S) (i : FirmType)
    (p : FirmPlan S) : ℝ :=
  ∑ h : History S 0, P.tree.historyWeight 0 h *
    (crraMarginal P.entrepreneurRiskAversion (p.consumption 0 h) *
      X.capitalPrice 0 h)

noncomputable def dateOneCapitalMarginalBenefit
    (P : Primitives S) (X : Allocation S) (i : FirmType)
    (p : FirmPlan S) : ℝ :=
  P.entrepreneurDiscount * ∑ h : History S 1,
    P.tree.historyWeight 1 h *
      (crraMarginal P.entrepreneurRiskAversion (p.consumption 1 h) *
        dateOneMarginalCapitalPayoff P X i p h)

noncomputable def expectedCapitalEulerGradient
    (P : Primitives S) (X : Allocation S) (i : FirmType)
    (p : FirmPlan S) : ℝ :=
  (∑ h : History S 0, P.tree.historyWeight 0 h *
    (crraMarginal P.entrepreneurRiskAversion (p.consumption 0 h) *
      (-X.capitalPrice 0 h))) +
  dateOneCapitalMarginalBenefit P X i p

theorem utilityTerm_zero_hasDerivAt
    (P : Primitives S) (X : Allocation S) (i : FirmType)
    (I : InheritedState) (p : FirmPlan S)
    (hfeas : FirmFeasible P I X i p) :
    HasDerivAt
      (fun epsilon : ℝ =>
        firmUtilityTerm P (capitalDateZeroVariation P X i p epsilon) 0)
      (∑ h : History S 0, P.tree.historyWeight 0 h *
        (crraMarginal P.entrepreneurRiskAversion (p.consumption 0 h) *
          (-X.capitalPrice 0 h))) 0 := by
  have hsum : HasDerivAt
      (fun epsilon : ℝ =>
        ∑ h : History S 0,
          P.tree.historyWeight 0 h *
            crraUtility P.entrepreneurRiskAversion
              (p.consumption 0 h - X.capitalPrice 0 h * epsilon))
      (∑ h : History S 0, P.tree.historyWeight 0 h *
        (crraMarginal P.entrepreneurRiskAversion (p.consumption 0 h) *
          (-X.capitalPrice 0 h))) 0 := by
    apply HasDerivAt.fun_sum
    intro h _
    have hinner : HasDerivAt
        (fun epsilon : ℝ =>
          p.consumption 0 h - X.capitalPrice 0 h * epsilon)
        (-X.capitalPrice 0 h) 0 := by
      simpa only [id_eq, mul_one, neg_mul, sub_eq_add_neg] using
        (((hasDerivAt_id (0 : ℝ)).const_mul (-X.capitalPrice 0 h)).const_add
          (p.consumption 0 h))
    apply weightedCrra_hasDerivAt P.entrepreneurRiskAversion
      (P.tree.historyWeight 0 h) (p.consumption 0 h)
      (-X.capitalPrice 0 h)
      (fun epsilon : ℝ =>
        p.consumption 0 h - X.capitalPrice 0 h * epsilon)
      hinner (by simp)
    intro hw
    have hp : 0 < P.tree.historyWeight 0 h :=
      lt_of_le_of_ne (historyWeight_nonneg P.tree 0 h) (Ne.symm hw)
    exact (hfeas.1 0 h hp).1
  simpa only [firmUtilityTerm, pow_zero, one_mul,
    FiniteMarkovTree.expectationAt, variation_consumption_zero] using hsum

theorem utilityTerm_one_hasDerivAt
    (P : Primitives S) (X : Allocation S) (i : FirmType)
    (I : InheritedState) (p : FirmPlan S)
    (hfeas : FirmFeasible P I X i p)
    (hcapital : ∀ h : History S 0, FirmHistoryAdmissible P 0 h →
      0 < p.capital 0 h) :
    HasDerivAt
      (fun epsilon : ℝ =>
        firmUtilityTerm P (capitalDateZeroVariation P X i p epsilon) 1)
      (dateOneCapitalMarginalBenefit P X i p) 0 := by
  have hsum : HasDerivAt
      (fun epsilon : ℝ =>
        ∑ h : History S 1,
          P.tree.historyWeight 1 h *
            crraUtility P.entrepreneurRiskAversion
              (p.consumption 1 h +
                dateOneCapitalGain P X i p epsilon h))
      (∑ h : History S 1, P.tree.historyWeight 1 h *
        (crraMarginal P.entrepreneurRiskAversion (p.consumption 1 h) *
          dateOneMarginalCapitalPayoff P X i p h)) 0 := by
    apply HasDerivAt.fun_sum
    intro h _
    by_cases hw : P.tree.historyWeight 1 h = 0
    · simpa [hw] using (hasDerivAt_const (0 : ℝ) (0 : ℝ))
    · have hp : FirmHistoryAdmissible P 1 h :=
        lt_of_le_of_ne (historyWeight_nonneg P.tree 1 h) (Ne.symm hw)
      have hK : 0 < p.capital 0 (previousHistory h) :=
        hcapital _ (admissible_predecessor_of_admissible_child P h hp)
      have hinner : HasDerivAt
          (fun epsilon : ℝ =>
            p.consumption 1 h + dateOneCapitalGain P X i p epsilon h)
          (dateOneMarginalCapitalPayoff P X i p h) 0 :=
        (dateOneCapitalGain_hasDerivAt_zero P X i p h hK).const_add
          (p.consumption 1 h)
      apply weightedCrra_hasDerivAt P.entrepreneurRiskAversion
        (P.tree.historyWeight 1 h) (p.consumption 1 h)
        (dateOneMarginalCapitalPayoff P X i p h)
        (fun epsilon : ℝ =>
          p.consumption 1 h + dateOneCapitalGain P X i p epsilon h)
        hinner (by simp [dateOneCapitalGain])
      intro _
      exact (hfeas.1 1 h hp).1
  have hscaled := hsum.const_mul P.entrepreneurDiscount
  simpa only [firmUtilityTerm, pow_one,
    FiniteMarkovTree.expectationAt, variation_consumption_one,
    dateOneCapitalMarginalBenefit] using hscaled

/-- Full discounted value derivative is a finite calculation because the
    later utility terms cancel exactly for EVERY epsilon. -/
theorem discountedFirmUtility_dateZeroCapital_hasDerivAt
    (P : Primitives S) (I : InheritedState)
    (X : Allocation S) (i : FirmType)
    (p : FirmPlan S)
    (hfeas : FirmFeasible P I X i p)
    (hwell : FirmObjectiveWellDefined P p)
    (hcapital : ∀ h : History S 0, FirmHistoryAdmissible P 0 h →
      0 < p.capital 0 h) :
    HasDerivAt (fun epsilon : ℝ =>
      discountedFirmUtility P (capitalDateZeroVariation P X i p epsilon))
      (expectedCapitalEulerGradient P X i p) 0 := by
  have hzero := utilityTerm_zero_hasDerivAt P X i I p hfeas
  have hone := utilityTerm_one_hasDerivAt P X i I p hfeas hcapital
  let C : ℝ := discountedFirmUtility P p -
    firmUtilityTerm P p 0 - firmUtilityTerm P p 1
  have hfinite : HasDerivAt (fun epsilon : ℝ =>
      firmUtilityTerm P (capitalDateZeroVariation P X i p epsilon) 0 +
      firmUtilityTerm P (capitalDateZeroVariation P X i p epsilon) 1 + C)
      (expectedCapitalEulerGradient P X i p) 0 := by
    simpa only [expectedCapitalEulerGradient, dateOneCapitalMarginalBenefit] using
      (hzero.add hone).add_const C
  have heq : (fun epsilon : ℝ =>
        discountedFirmUtility P (capitalDateZeroVariation P X i p epsilon)) =
      (fun epsilon : ℝ =>
        firmUtilityTerm P (capitalDateZeroVariation P X i p epsilon) 0 +
        firmUtilityTerm P (capitalDateZeroVariation P X i p epsilon) 1 + C) := by
    funext epsilon
    have hd := discountedFirmUtility_capitalVariation_delta_eq
      P X i p epsilon hwell
    dsimp [C]
    linarith
  rw [heq]
  exact hfinite

/-- Expected capital Euler gradient is forced to zero by SOURCE optimality,
    not stated as a KKT axiom or an assumption of this theorem. -/
theorem firmOptimal_expectedCapitalEuler_gradient_zero
    (P : Primitives S) (I : InheritedState)
    (X : Allocation S) (i : FirmType)
    (hopt : FirmOptimal P I X i)
    (hcapital : ∀ h : History S 0, FirmHistoryAdmissible P 0 h →
      0 < X.capital i 0 h)
    (hslack : DateZeroSlackBorrower P X i) :
    expectedCapitalEulerGradient P X i (firmPlanOfAllocation X i) = 0 := by
  let p := firmPlanOfAllocation X i
  have hderiv := discountedFirmUtility_dateZeroCapital_hasDerivAt
    P I X i p hopt.1 hopt.2.1 hcapital
  obtain ⟨radius, hradius, hbound⟩ :=
    exists_twoSided_feasible_optimality_radius_of_interior_slack
      P I X i hopt hcapital hslack
  have hcons0 :
      (capitalDateZeroVariation P X i p 0).consumption 0 =
        p.consumption 0 := by
    funext h
    simp
  have hcons1 :
      (capitalDateZeroVariation P X i p 0).consumption 1 =
        p.consumption 1 := by
    funext h
    simp [dateOneCapitalGain]
  have hterm0 :
      firmUtilityTerm P (capitalDateZeroVariation P X i p 0) 0 =
        firmUtilityTerm P p 0 := by
    unfold firmUtilityTerm
    rw [hcons0]
  have hterm1 :
      firmUtilityTerm P (capitalDateZeroVariation P X i p 0) 1 =
        firmUtilityTerm P p 1 := by
    unfold firmUtilityTerm
    rw [hcons1]
  have hvalue0 :
      discountedFirmUtility P (capitalDateZeroVariation P X i p 0) =
        discountedFirmUtility P p := by
    have hdelta := discountedFirmUtility_capitalVariation_delta_eq
      P X i p 0 hopt.2.1
    rw [hterm0, hterm1] at hdelta
    linarith
  have hball : Set.Ioo (-radius) radius ∈ 𝓝 (0 : ℝ) := by
    exact isOpen_Ioo.mem_nhds ⟨by linarith, by linarith⟩
  have hmax : IsLocalMax (fun epsilon : ℝ =>
      discountedFirmUtility P (capitalDateZeroVariation P X i p epsilon)) 0 := by
    change ∀ᶠ epsilon : ℝ in 𝓝 (0 : ℝ),
      discountedFirmUtility P (capitalDateZeroVariation P X i p epsilon) ≤
      discountedFirmUtility P (capitalDateZeroVariation P X i p 0)
    filter_upwards [hball] with epsilon hepsilon
    rw [hvalue0]
    exact (hbound epsilon (abs_lt.mpr hepsilon)).2.2
  exact hmax.hasDerivAt_eq_zero hderiv

/-- Economic Euler in expectation: current marginal utility cost equals
    discounted expected marginal payoff, without any collateral premium
    because the L/S collateral constraint is strictly slack. -/
theorem firmOptimal_expectedCapitalEuler
    (P : Primitives S) (I : InheritedState)
    (X : Allocation S) (i : FirmType)
    (hopt : FirmOptimal P I X i)
    (hcapital : ∀ h : History S 0, FirmHistoryAdmissible P 0 h →
      0 < X.capital i 0 h)
    (hslack : DateZeroSlackBorrower P X i) :
    dateZeroCapitalMarginalCost P X i (firmPlanOfAllocation X i) =
      dateOneCapitalMarginalBenefit P X i (firmPlanOfAllocation X i) := by
  have hz := firmOptimal_expectedCapitalEuler_gradient_zero
    P I X i hopt hcapital hslack
  have hneg : (∑ h : History S 0, P.tree.historyWeight 0 h *
      (crraMarginal P.entrepreneurRiskAversion
        ((firmPlanOfAllocation X i).consumption 0 h) *
        (-X.capitalPrice 0 h))) =
      -dateZeroCapitalMarginalCost P X i (firmPlanOfAllocation X i) := by
    change _ = -(∑ h : History S 0,
      P.tree.historyWeight 0 h *
        (crraMarginal P.entrepreneurRiskAversion
          ((firmPlanOfAllocation X i).consumption 0 h) *
          X.capitalPrice 0 h))
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro h _
    ring
  unfold expectedCapitalEulerGradient at hz
  rw [hneg] at hz
  linarith

end ProposedDateZeroCapitalExpectedEuler
end Ventura26LiquidityAllocation
