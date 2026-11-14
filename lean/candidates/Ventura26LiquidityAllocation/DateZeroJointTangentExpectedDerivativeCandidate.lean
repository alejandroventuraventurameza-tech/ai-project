import Ventura26LiquidityAllocation.DateZeroJointCapitalLoanDeltaCandidate
import Ventura26LiquidityAllocation.DateZeroJointCapitalLoanTangentDerivativeCandidate
import Ventura26LiquidityAllocation.DateZeroCapitalEulerDerivativeCandidate

/-!
# Exact expected marginal objective along a joint capital-loan tangent

For any fixed real tangent coefficients R, Gamma, the source entrepreneur's
discounted objective has a derivative at zero, obtained from:
  - the CRRA marginal utility at each positive-probability history,
  - the genuine nonlinear date-one Cobb-Douglas payoff derivative,
  - the actual changed nominal loan face and real repayment,
  - the exact two-date delta of the infinite-horizon original objective.

No Euler equation, KKT balance, equilibrium witness, or objective derivative
is assumed. The gradient is one EXPECTED scalar, not a separate equation
at every successor state.
-/

namespace Ventura26LiquidityAllocation
namespace ProposedDateZeroJointTangentExpectedDerivative

open ProposedDateZeroJointCapitalLoanDeviation
open ProposedDateZeroCapitalDeviation
open ProposedDateZeroJointCapitalLoanDelta
open ProposedDateZeroJointCapitalLoanTangentDerivative
open ProposedDateZeroCapitalEulerDerivative

variable {S : Type*} [Fintype S] [DecidableEq S]

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

noncomputable def jointTangentExpectedGradient
    (P : Primitives S) (X : Allocation S) (i : FirmType)
    (p : FirmPlan S) (R Gamma : ℝ) : ℝ :=
  (∑ h : History S 0, P.tree.historyWeight 0 h *
    (crraMarginal P.entrepreneurRiskAversion (p.consumption 0 h) *
      (Gamma - X.capitalPrice 0 h * R))) +
  P.entrepreneurDiscount *
    (∑ h : History S 1, P.tree.historyWeight 1 h *
      (crraMarginal P.entrepreneurRiskAversion (p.consumption 1 h) *
        (R * dateOneMarginalCapitalPayoff P X i p h -
          X.loanRate 0 (previousHistory h) * Gamma /
            X.inflation 1 h)))

theorem jointUtilityTerm_zero_hasDerivAt
    (P : Primitives S) (X : Allocation S) (i : FirmType)
    (I : InheritedState) (p : FirmPlan S)
    (R Gamma : ℝ)
    (hfeas : FirmFeasible P I X i p) :
    HasDerivAt
      (fun epsilon : ℝ =>
        firmUtilityTerm P
          (jointDateZeroVariation P X i p (R * epsilon) (Gamma * epsilon))
          0)
      (∑ h : History S 0, P.tree.historyWeight 0 h *
        (crraMarginal P.entrepreneurRiskAversion (p.consumption 0 h) *
          (Gamma - X.capitalPrice 0 h * R))) 0 := by
  have hsum : HasDerivAt
      (fun epsilon : ℝ =>
        ∑ h : History S 0, P.tree.historyWeight 0 h *
          crraUtility P.entrepreneurRiskAversion
            (p.consumption 0 h -
              X.capitalPrice 0 h * (R * epsilon) + Gamma * epsilon))
      (∑ h : History S 0, P.tree.historyWeight 0 h *
        (crraMarginal P.entrepreneurRiskAversion (p.consumption 0 h) *
          (Gamma - X.capitalPrice 0 h * R))) 0 := by
    apply HasDerivAt.fun_sum
    intro h _
    by_cases hw : P.tree.historyWeight 0 h = 0
    · simpa [hw] using (hasDerivAt_const (0 : ℝ) (0 : ℝ))
    · have hp : FirmHistoryAdmissible P 0 h :=
        lt_of_le_of_ne (historyWeight_nonneg P.tree 0 h) (Ne.symm hw)
      have hc : 0 < p.consumption 0 h := (hfeas.1 0 h hp).1
      have hinner : HasDerivAt
          (fun epsilon : ℝ =>
            p.consumption 0 h -
              X.capitalPrice 0 h * (R * epsilon) + Gamma * epsilon)
          (Gamma - X.capitalPrice 0 h * R) 0 := by
        have hl :=
          ((hasDerivAt_id (0 : ℝ)).const_mul
            (Gamma - X.capitalPrice 0 h * R)).const_add
            (p.consumption 0 h)
        convert hl using 1
        · ext epsilon
          dsimp [id]
          ring
        · ring
      have hbase :
          HasDerivAt (fun z : ℝ => crraUtility P.entrepreneurRiskAversion z)
            (crraMarginal P.entrepreneurRiskAversion (p.consumption 0 h))
            (p.consumption 0 h -
              X.capitalPrice 0 h * (R * (0 : ℝ)) + Gamma * 0) := by
        simpa using crraUtility_hasDerivAt
          P.entrepreneurRiskAversion (p.consumption 0 h) hc
      have hd := (hbase.comp 0 hinner).const_mul
        (P.tree.historyWeight 0 h)
      simpa using hd
  simpa only [firmUtilityTerm, pow_zero, one_mul,
    FiniteMarkovTree.expectationAt, joint_consumption_zero] using hsum

theorem jointUtilityTerm_one_hasDerivAt
    (P : Primitives S) (X : Allocation S) (i : FirmType)
    (I : InheritedState) (p : FirmPlan S)
    (R Gamma : ℝ)
    (hfeas : FirmFeasible P I X i p)
    (hcapital : ∀ h : History S 0, FirmHistoryAdmissible P 0 h →
      0 < p.capital 0 h) :
    HasDerivAt
      (fun epsilon : ℝ =>
        firmUtilityTerm P
          (jointDateZeroVariation P X i p (R * epsilon) (Gamma * epsilon))
          1)
      (P.entrepreneurDiscount *
        (∑ h : History S 1, P.tree.historyWeight 1 h *
          (crraMarginal P.entrepreneurRiskAversion (p.consumption 1 h) *
            (R * dateOneMarginalCapitalPayoff P X i p h -
              X.loanRate 0 (previousHistory h) * Gamma /
                X.inflation 1 h)))) 0 := by
  have hsum : HasDerivAt
      (fun epsilon : ℝ =>
        ∑ h : History S 1, P.tree.historyWeight 1 h *
          crraUtility P.entrepreneurRiskAversion
            (p.consumption 1 h +
              dateOneJointGain P X i p (R * epsilon) (Gamma * epsilon) h))
      (∑ h : History S 1, P.tree.historyWeight 1 h *
        (crraMarginal P.entrepreneurRiskAversion (p.consumption 1 h) *
          (R * dateOneMarginalCapitalPayoff P X i p h -
            X.loanRate 0 (previousHistory h) * Gamma /
              X.inflation 1 h))) 0 := by
    apply HasDerivAt.fun_sum
    intro h _
    by_cases hw : P.tree.historyWeight 1 h = 0
    · simpa [hw] using (hasDerivAt_const (0 : ℝ) (0 : ℝ))
    · have hp : FirmHistoryAdmissible P 1 h :=
        lt_of_le_of_ne (historyWeight_nonneg P.tree 1 h) (Ne.symm hw)
      have hprev : FirmHistoryAdmissible P 0 (previousHistory h) :=
        ProposedDateZeroCapitalGainContinuity.admissible_predecessor_of_admissible_child
          P h hp
      have hK : 0 < p.capital 0 (previousHistory h) :=
        hcapital _ hprev
      have hc : 0 < p.consumption 1 h := (hfeas.1 1 h hp).1
      have hinner : HasDerivAt
          (fun epsilon : ℝ =>
            p.consumption 1 h +
              dateOneJointGain P X i p (R * epsilon) (Gamma * epsilon) h)
          (R * dateOneMarginalCapitalPayoff P X i p h -
            X.loanRate 0 (previousHistory h) * Gamma /
              X.inflation 1 h) 0 :=
        (dateOneJointGain_hasDerivAt_zero_along_tangent
          P X i p h R Gamma hK).const_add (p.consumption 1 h)
      have hgainZero :
          dateOneJointGain P X i p (R * (0 : ℝ)) (Gamma * 0) h = 0 := by
        simp [dateOneJointGain, dateOneCapitalGain]
      have hbase :
          HasDerivAt (fun z : ℝ => crraUtility P.entrepreneurRiskAversion z)
            (crraMarginal P.entrepreneurRiskAversion (p.consumption 1 h))
            (p.consumption 1 h +
              dateOneJointGain P X i p (R * (0 : ℝ)) (Gamma * 0) h) := by
        rw [hgainZero]
        simpa using crraUtility_hasDerivAt
          P.entrepreneurRiskAversion (p.consumption 1 h) hc
      have hd := (hbase.comp 0 hinner).const_mul
        (P.tree.historyWeight 1 h)
      simpa [hgainZero] using hd
  have hscaled := hsum.const_mul P.entrepreneurDiscount
  simpa only [firmUtilityTerm, pow_one,
    FiniteMarkovTree.expectationAt, joint_consumption_one] using hscaled

theorem discountedFirmUtility_jointTangent_hasDerivAt
    (P : Primitives S) (I : InheritedState)
    (X : Allocation S) (i : FirmType)
    (p : FirmPlan S) (R Gamma : ℝ)
    (hfeas : FirmFeasible P I X i p)
    (hwell : FirmObjectiveWellDefined P p)
    (hcapital : ∀ h : History S 0, FirmHistoryAdmissible P 0 h →
      0 < p.capital 0 h) :
    HasDerivAt
      (fun epsilon : ℝ =>
        discountedFirmUtility P
          (jointDateZeroVariation P X i p (R * epsilon) (Gamma * epsilon)))
      (jointTangentExpectedGradient P X i p R Gamma) 0 := by
  have hzero := jointUtilityTerm_zero_hasDerivAt P X i I p R Gamma hfeas
  have hone := jointUtilityTerm_one_hasDerivAt P X i I p R Gamma hfeas hcapital
  let C : ℝ := discountedFirmUtility P p -
    firmUtilityTerm P p 0 - firmUtilityTerm P p 1
  have hfinite : HasDerivAt (fun epsilon : ℝ =>
      firmUtilityTerm P
        (jointDateZeroVariation P X i p (R * epsilon) (Gamma * epsilon)) 0 +
      firmUtilityTerm P
        (jointDateZeroVariation P X i p (R * epsilon) (Gamma * epsilon)) 1 + C)
      (jointTangentExpectedGradient P X i p R Gamma) 0 := by
    simpa only [jointTangentExpectedGradient] using
      (hzero.add hone).add_const C
  have heq : (fun epsilon : ℝ =>
        discountedFirmUtility P
          (jointDateZeroVariation P X i p (R * epsilon) (Gamma * epsilon))) =
      (fun epsilon : ℝ =>
        firmUtilityTerm P
          (jointDateZeroVariation P X i p (R * epsilon) (Gamma * epsilon)) 0 +
        firmUtilityTerm P
          (jointDateZeroVariation P X i p (R * epsilon) (Gamma * epsilon)) 1 + C) := by
    funext epsilon
    have hd := discountedFirmUtility_jointVariation_delta_eq P X i p
      (R * epsilon) (Gamma * epsilon) hwell
    dsimp [C]
    linarith
  rw [heq]
  exact hfinite

end ProposedDateZeroJointTangentExpectedDerivative
end Ventura26LiquidityAllocation
