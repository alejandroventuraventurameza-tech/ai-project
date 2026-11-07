import Ventura26LiquidityAllocation.DateZeroJointCapitalLoanUtilityCandidate
import Ventura26LiquidityAllocation.DateZeroCapitalEulerDerivativeCandidate

/-!
# Date-zero joint capital-loan tangent: analytic derivatives at epsilon=0

Along dk = R*epsilon, db = Gamma*epsilon, the source nonlinear date-one
wealth/consumption gain differentiates to R times the exact Cobb-Douglas
marginal capital payoff MINUS the real repayment derivative on the new
nominal loan face. Current consumption has derivative Gamma - q0*R.

These are local derivative lemmas; they do not yet derive a two-sided
feasibility radius nor the full discounted-objective tangent equality.
-/

namespace Ventura26LiquidityAllocation
namespace ProposedDateZeroJointCapitalLoanTangentDerivative

open ProposedDateZeroJointCapitalLoanDeviation
open ProposedDateZeroCapitalEulerDerivative

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- Exact nonlinear date-one marginal gain along the binding tangent. -/
theorem dateOneJointGain_hasDerivAt_zero_along_tangent
    (P : Primitives S) (X : Allocation S) (i : FirmType)
    (p : FirmPlan S) (h : History S 1)
    (R Gamma : ℝ)
    (hcapital : 0 < p.capital 0 (previousHistory h)) :
    HasDerivAt
      (fun epsilon : ℝ =>
        dateOneJointGain P X i p (R * epsilon) (Gamma * epsilon) h)
      (R * dateOneMarginalCapitalPayoff P X i p h -
        X.loanRate 0 (previousHistory h) * Gamma / X.inflation 1 h) 0 := by
  have hscale :
      HasDerivAt (fun epsilon : ℝ => R * epsilon) R 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).const_mul R)
  have hprofit :=
    (dateOneCapitalGain_hasDerivAt_zero P X i p h hcapital).comp
      (0 : ℝ) hscale
  have hloan :
      HasDerivAt (fun epsilon : ℝ =>
        X.loanRate 0 (previousHistory h) * (Gamma * epsilon) /
          X.inflation 1 h)
      (X.loanRate 0 (previousHistory h) * Gamma / X.inflation 1 h) 0 := by
    have hl :=
      (((hasDerivAt_id (0 : ℝ)).const_mul Gamma).const_mul
        (X.loanRate 0 (previousHistory h))).div_const (X.inflation 1 h)
    convert hl using 1 <;> ring
  have hderiv := hprofit.sub hloan
  convert hderiv using 1 <;>
    dsimp [dateOneJointGain] <;> ring

/-- Date-zero cash budget derivative for the true joint plan. -/
theorem jointConsumption_zero_hasDerivAt_along_tangent
    (P : Primitives S) (X : Allocation S) (i : FirmType)
    (p : FirmPlan S) (h : History S 0)
    (R Gamma : ℝ) :
    HasDerivAt (fun epsilon : ℝ =>
      (jointDateZeroVariation P X i p
        (R * epsilon) (Gamma * epsilon)).consumption 0 h)
      (Gamma - X.capitalPrice 0 h * R) 0 := by
  have hlin :
      HasDerivAt (fun epsilon : ℝ =>
        p.consumption 0 h -
          X.capitalPrice 0 h * (R * epsilon) + Gamma * epsilon)
        (Gamma - X.capitalPrice 0 h * R) 0 := by
    have hl := ((hasDerivAt_id (0 : ℝ)).const_mul
      (Gamma - X.capitalPrice 0 h * R)).const_add (p.consumption 0 h)
    convert hl using 1 <;> ring
  simpa only [joint_consumption_zero] using hlin

end ProposedDateZeroJointCapitalLoanTangentDerivative
end Ventura26LiquidityAllocation
