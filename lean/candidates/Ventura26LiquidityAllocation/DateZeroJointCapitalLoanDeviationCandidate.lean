import Ventura26LiquidityAllocation.DateZeroCapitalDeviationCandidate

/-!
# Joint date-zero loan and capital deviation of the literal source FirmPlan

The perturbation changes date-zero capital by dk and the gross loan by db.
The face is raised by R^L*db, current consumption changes by db-q0*dk,
and date-one wealth/consumption incorporate the *nonlinear* capital gain
minus the real repayment on the changed nominal face.

This is a genuine infinite-horizon plan transformation, not merely a
reduced KKT equation. We first prove the source face identity and budgets
at dates zero/one exactly. Feasibility of all collateral constraints, sign
constraints and optimality of tangent variations remain further tasks.
-/

namespace Ventura26LiquidityAllocation
namespace ProposedDateZeroJointCapitalLoanDeviation

open ProposedDateZeroCapitalDeviation

variable {S : Type*} [Fintype S] [DecidableEq S]

noncomputable def dateOneJointGain
    (P : Primitives S) (X : Allocation S) (i : FirmType)
    (p : FirmPlan S) (dk db : ℝ) (h : History S 1) : ℝ :=
  dateOneCapitalGain P X i p dk h -
    X.loanRate 0 (previousHistory h) * db / X.inflation 1 h

/-- Joint finite-date variation, with every t>=2 field unchanged. -/
noncomputable def jointDateZeroVariation
    (P : Primitives S) (X : Allocation S) (i : FirmType)
    (p : FirmPlan S) (dk db : ℝ) : FirmPlan S where
  consumption :=
    Function.update
      (Function.update p.consumption 0
        (fun h => p.consumption 0 h - X.capitalPrice 0 h * dk + db))
      1 (fun h => p.consumption 1 h + dateOneJointGain P X i p dk db h)
  capital := Function.update p.capital 0
    (fun h => p.capital 0 h + dk)
  labor := p.labor
  loan := Function.update p.loan 0 (fun h => p.loan 0 h + db)
  deposit := p.deposit
  face := Function.update p.face 0
    (fun h => p.face 0 h + X.loanRate 0 h * db)
  wealth := Function.update p.wealth 1
    (fun h => p.wealth 1 h + dateOneJointGain P X i p dk db h)

@[simp] theorem joint_consumption_zero
    (P : Primitives S) (X : Allocation S) (i : FirmType)
    (p : FirmPlan S) (dk db : ℝ) (h : History S 0) :
    (jointDateZeroVariation P X i p dk db).consumption 0 h =
      p.consumption 0 h - X.capitalPrice 0 h * dk + db := by
  simp [jointDateZeroVariation]

@[simp] theorem joint_consumption_one
    (P : Primitives S) (X : Allocation S) (i : FirmType)
    (p : FirmPlan S) (dk db : ℝ) (h : History S 1) :
    (jointDateZeroVariation P X i p dk db).consumption 1 h =
      p.consumption 1 h + dateOneJointGain P X i p dk db h := by
  simp [jointDateZeroVariation]

@[simp] theorem joint_capital_zero
    (P : Primitives S) (X : Allocation S) (i : FirmType)
    (p : FirmPlan S) (dk db : ℝ) (h : History S 0) :
    (jointDateZeroVariation P X i p dk db).capital 0 h =
      p.capital 0 h + dk := by
  simp [jointDateZeroVariation]

@[simp] theorem joint_loan_zero
    (P : Primitives S) (X : Allocation S) (i : FirmType)
    (p : FirmPlan S) (dk db : ℝ) (h : History S 0) :
    (jointDateZeroVariation P X i p dk db).loan 0 h =
      p.loan 0 h + db := by
  simp [jointDateZeroVariation]

@[simp] theorem joint_face_zero
    (P : Primitives S) (X : Allocation S) (i : FirmType)
    (p : FirmPlan S) (dk db : ℝ) (h : History S 0) :
    (jointDateZeroVariation P X i p dk db).face 0 h =
      p.face 0 h + X.loanRate 0 h * db := by
  simp [jointDateZeroVariation]

@[simp] theorem joint_wealth_one
    (P : Primitives S) (X : Allocation S) (i : FirmType)
    (p : FirmPlan S) (dk db : ℝ) (h : History S 1) :
    (jointDateZeroVariation P X i p dk db).wealth 1 h =
      p.wealth 1 h + dateOneJointGain P X i p dk db h := by
  simp [jointDateZeroVariation]

/-- The nominal face identity is preserved, without holding face fixed. -/
theorem joint_signed_face_zero
    (P : Primitives S) (X : Allocation S) (i : FirmType)
    (p : FirmPlan S) (dk db : ℝ) (h : History S 0)
    (hface : p.face 0 h =
      signedFace (X.loanRate 0 h) (p.loan 0 h)
        (X.depositRate 0 h) (p.deposit 0 h)) :
    (jointDateZeroVariation P X i p dk db).face 0 h =
      signedFace (X.loanRate 0 h)
        ((jointDateZeroVariation P X i p dk db).loan 0 h)
        (X.depositRate 0 h)
        ((jointDateZeroVariation P X i p dk db).deposit 0 h) := by
  rw [joint_face_zero, joint_loan_zero]
  change p.face 0 h + X.loanRate 0 h * db =
    signedFace (X.loanRate 0 h) (p.loan 0 h + db)
      (X.depositRate 0 h) (p.deposit 0 h)
  rw [hface]
  simp only [signedFace]
  ring

/-- Current budget is exact for arbitrary joint dk and db. -/
theorem joint_budget_zero
    (P : Primitives S) (X : Allocation S) (i : FirmType)
    (p : FirmPlan S) (dk db : ℝ) (h : History S 0)
    (hbudget : p.consumption 0 h + X.capitalPrice 0 h * p.capital 0 h +
      p.deposit 0 h = p.wealth 0 h + p.loan 0 h) :
    (jointDateZeroVariation P X i p dk db).consumption 0 h +
      X.capitalPrice 0 h *
        (jointDateZeroVariation P X i p dk db).capital 0 h +
      (jointDateZeroVariation P X i p dk db).deposit 0 h =
      (jointDateZeroVariation P X i p dk db).wealth 0 h +
        (jointDateZeroVariation P X i p dk db).loan 0 h := by
  rw [joint_consumption_zero, joint_capital_zero, joint_loan_zero]
  change p.consumption 0 h - X.capitalPrice 0 h * dk + db +
    X.capitalPrice 0 h * (p.capital 0 h + dk) + p.deposit 0 h =
    p.wealth 0 h + (p.loan 0 h + db)
  nlinarith [hbudget]

/-- Date-one budget remains exact because consumption and wealth absorb
    the same realized gain and loan-repayment adjustment. -/
theorem joint_budget_one
    (P : Primitives S) (X : Allocation S) (i : FirmType)
    (p : FirmPlan S) (dk db : ℝ) (h : History S 1)
    (hbudget : p.consumption 1 h + X.capitalPrice 1 h * p.capital 1 h +
      p.deposit 1 h = p.wealth 1 h + p.loan 1 h) :
    (jointDateZeroVariation P X i p dk db).consumption 1 h +
      X.capitalPrice 1 h *
        (jointDateZeroVariation P X i p dk db).capital 1 h +
      (jointDateZeroVariation P X i p dk db).deposit 1 h =
      (jointDateZeroVariation P X i p dk db).wealth 1 h +
        (jointDateZeroVariation P X i p dk db).loan 1 h := by
  rw [joint_consumption_one, joint_wealth_one]
  change p.consumption 1 h + dateOneJointGain P X i p dk db h +
    X.capitalPrice 1 h * p.capital 1 h + p.deposit 1 h =
    p.wealth 1 h + dateOneJointGain P X i p dk db h + p.loan 1 h
  linarith [hbudget]

/-- The date-one nonlinear wealth transition is preserved EXACTLY after
    changing both installed capital and nominal loan repayment. There is no
    linear approximation of operating profits or of real repayment. -/
theorem joint_wealth_transition_one
    (P : Primitives S) (X : Allocation S) (i : FirmType)
    (p : FirmPlan S) (dk db : ℝ) (h : History S 0) (s : S)
    (hwealth :
      p.wealth 1 (childHistory h s) =
        operatingProfit (X.inputPrice 1 (childHistory h s))
          (P.aggregateProductivity s * P.productivity i)
          (p.capital 0 h)
          (p.labor 1 (childHistory h s))
          P.alpha P.beta (X.wage 1 (childHistory h s)) +
        X.capitalPrice 1 (childHistory h s) *
          (1 - P.depreciation) * p.capital 0 h -
        realRepayment (p.face 0 h)
          (X.inflation 1 (childHistory h s))) :
    (jointDateZeroVariation P X i p dk db).wealth 1 (childHistory h s) =
      operatingProfit (X.inputPrice 1 (childHistory h s))
        (P.aggregateProductivity s * P.productivity i)
        ((jointDateZeroVariation P X i p dk db).capital 0 h)
        ((jointDateZeroVariation P X i p dk db).labor 1 (childHistory h s))
        P.alpha P.beta (X.wage 1 (childHistory h s)) +
      X.capitalPrice 1 (childHistory h s) *
        (1 - P.depreciation) *
          ((jointDateZeroVariation P X i p dk db).capital 0 h) -
      realRepayment
        ((jointDateZeroVariation P X i p dk db).face 0 h)
        (X.inflation 1 (childHistory h s)) := by
  rw [joint_wealth_one, joint_capital_zero, joint_face_zero]
  change p.wealth 1 (childHistory h s) +
      dateOneJointGain P X i p dk db (childHistory h s) = _
  rw [hwealth]
  have hprev : previousHistory (childHistory h s) = h := by
    funext j
    rfl
  have hcur : currentState (childHistory h s) = s := by
    rfl
  simp only [dateOneJointGain, dateOneCapitalGain, hprev, hcur]
  simp only [jointDateZeroVariation, realRepayment]
  ring

end ProposedDateZeroJointCapitalLoanDeviation
end Ventura26LiquidityAllocation
