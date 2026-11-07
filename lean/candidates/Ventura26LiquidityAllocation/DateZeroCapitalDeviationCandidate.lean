import Ventura26LiquidityAllocation.FirmOptimalVariationCandidate

/-!
# Explicit date-zero capital perturbation in the source firm problem

For a literal firm plan p and real epsilon, raise date-zero capital by
epsilon while reducing date-zero consumption by q_0 * epsilon. Hold
loans, deposits, nominal face and labor unchanged. At date one, add the
resulting realized operating-profit and undepreciated-capital gain BOTH
to wealth and consumption. All later values are unchanged.

Therefore the date-zero and date-one budgets and the wealth transition
are preserved EXACTLY, including nonlinear Cobb-Douglas production and
state-specific prices. The only remaining local feasibility tests are
(i) date-zero positive consumption and nonnegative capital,
(ii) date-one positive consumption at admissible histories,
(iii) date-zero robust collateral in each positive-probability child.

Theorem capitalDateZeroVariation_feasible uses precisely these signs and
the unchanged original FirmFeasible; it does not posit new budget,
transition, or Euler equations. These local sign hypotheses will be
discharged by strict slack/interiority and continuity in a later module.

The variation is one-sided when collateral binds and two-sided under
strict slack. No claims about derivatives or KKT are hidden here.
-/

namespace Ventura26LiquidityAllocation
namespace ProposedDateZeroCapitalDeviation

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- Realized date-one payoff from an additional unit of DATE-ZERO capital,
    with labor and fixed aggregate prices taken from the original plan. -/
noncomputable def dateOneCapitalGain
    (P : Primitives S) (X : Allocation S) (i : FirmType)
    (p : FirmPlan S) (ε : ℝ) (h : History S 1) : ℝ :=
  operatingProfit (X.inputPrice 1 h)
      (P.aggregateProductivity (currentState h) * P.productivity i)
      (p.capital 0 (previousHistory h) + ε)
      (p.labor 1 h) P.alpha P.beta (X.wage 1 h) -
  operatingProfit (X.inputPrice 1 h)
      (P.aggregateProductivity (currentState h) * P.productivity i)
      (p.capital 0 (previousHistory h))
      (p.labor 1 h) P.alpha P.beta (X.wage 1 h) +
  X.capitalPrice 1 h * (1 - P.depreciation) * ε

/-- Genuine finite perturbation of a full infinite-horizon gross firm plan.
    Nominal face, loan, deposit and labor are left identically unchanged. -/
noncomputable def capitalDateZeroVariation
    (P : Primitives S) (X : Allocation S) (i : FirmType)
    (p : FirmPlan S) (ε : ℝ) : FirmPlan S where
  consumption :=
    Function.update
      (Function.update p.consumption 0
        (fun h ↦ p.consumption 0 h - X.capitalPrice 0 h * ε))
      1 (fun h ↦ p.consumption 1 h + dateOneCapitalGain P X i p ε h)
  capital := Function.update p.capital 0 (fun h ↦ p.capital 0 h + ε)
  labor := p.labor
  loan := p.loan
  deposit := p.deposit
  face := p.face
  wealth := Function.update p.wealth 1
    (fun h ↦ p.wealth 1 h + dateOneCapitalGain P X i p ε h)

@[simp] theorem variation_consumption_zero
    (P : Primitives S) (X : Allocation S) (i : FirmType)
    (p : FirmPlan S) (ε : ℝ) (h : History S 0) :
    (capitalDateZeroVariation P X i p ε).consumption 0 h =
      p.consumption 0 h - X.capitalPrice 0 h * ε := by
  simp [capitalDateZeroVariation]

@[simp] theorem variation_consumption_one
    (P : Primitives S) (X : Allocation S) (i : FirmType)
    (p : FirmPlan S) (ε : ℝ) (h : History S 1) :
    (capitalDateZeroVariation P X i p ε).consumption 1 h =
      p.consumption 1 h + dateOneCapitalGain P X i p ε h := by
  simp [capitalDateZeroVariation]

@[simp] theorem variation_capital_zero
    (P : Primitives S) (X : Allocation S) (i : FirmType)
    (p : FirmPlan S) (ε : ℝ) (h : History S 0) :
    (capitalDateZeroVariation P X i p ε).capital 0 h =
      p.capital 0 h + ε := by
  simp [capitalDateZeroVariation]

@[simp] theorem variation_capital_succ
    (P : Primitives S) (X : Allocation S) (i : FirmType)
    (p : FirmPlan S) (ε : ℝ) (t : ℕ) (h : History S (t + 1)) :
    (capitalDateZeroVariation P X i p ε).capital (t + 1) h =
      p.capital (t + 1) h := by
  simp [capitalDateZeroVariation]

@[simp] theorem variation_wealth_zero
    (P : Primitives S) (X : Allocation S) (i : FirmType)
    (p : FirmPlan S) (ε : ℝ) (h : History S 0) :
    (capitalDateZeroVariation P X i p ε).wealth 0 h =
      p.wealth 0 h := by
  simp [capitalDateZeroVariation]

@[simp] theorem variation_wealth_one
    (P : Primitives S) (X : Allocation S) (i : FirmType)
    (p : FirmPlan S) (ε : ℝ) (h : History S 1) :
    (capitalDateZeroVariation P X i p ε).wealth 1 h =
      p.wealth 1 h + dateOneCapitalGain P X i p ε h := by
  simp [capitalDateZeroVariation]

private theorem variation_consumption_later
    (P : Primitives S) (X : Allocation S) (i : FirmType)
    (p : FirmPlan S) (ε : ℝ) (t : ℕ) (h : History S (t + 2)) :
    (capitalDateZeroVariation P X i p ε).consumption (t + 2) h =
      p.consumption (t + 2) h := by
  simp [capitalDateZeroVariation]

private theorem variation_wealth_later
    (P : Primitives S) (X : Allocation S) (i : FirmType)
    (p : FirmPlan S) (ε : ℝ) (t : ℕ) (h : History S (t + 2)) :
    (capitalDateZeroVariation P X i p ε).wealth (t + 2) h =
      p.wealth (t + 2) h := by
  simp [capitalDateZeroVariation]

/-- Date-zero budget is unchanged: the extra investment is paid for
    by the reduction of CURRENT consumption. -/
theorem variation_budget_zero
    (P : Primitives S) (X : Allocation S) (i : FirmType)
    (p : FirmPlan S) (ε : ℝ) (h : History S 0)
    (hbudget : p.consumption 0 h + X.capitalPrice 0 h * p.capital 0 h +
      p.deposit 0 h = p.wealth 0 h + p.loan 0 h) :
    (capitalDateZeroVariation P X i p ε).consumption 0 h +
      X.capitalPrice 0 h * (capitalDateZeroVariation P X i p ε).capital 0 h +
      (capitalDateZeroVariation P X i p ε).deposit 0 h =
      (capitalDateZeroVariation P X i p ε).wealth 0 h +
        (capitalDateZeroVariation P X i p ε).loan 0 h := by
  simp only [variation_consumption_zero, variation_capital_zero,
    variation_wealth_zero]
  change p.consumption 0 h - X.capitalPrice 0 h * ε +
    X.capitalPrice 0 h * (p.capital 0 h + ε) + p.deposit 0 h =
    p.wealth 0 h + p.loan 0 h
  nlinarith [hbudget]

/-- Date-one budget unchanged: the realized additional wealth is consumed
    rather than carried as a new position, hence future faces stay fixed. -/
theorem variation_budget_one
    (P : Primitives S) (X : Allocation S) (i : FirmType)
    (p : FirmPlan S) (ε : ℝ) (h : History S 1)
    (hbudget : p.consumption 1 h + X.capitalPrice 1 h * p.capital 1 h +
      p.deposit 1 h = p.wealth 1 h + p.loan 1 h) :
    (capitalDateZeroVariation P X i p ε).consumption 1 h +
      X.capitalPrice 1 h * (capitalDateZeroVariation P X i p ε).capital 1 h +
      (capitalDateZeroVariation P X i p ε).deposit 1 h =
      (capitalDateZeroVariation P X i p ε).wealth 1 h +
        (capitalDateZeroVariation P X i p ε).loan 1 h := by
  simp only [variation_consumption_one, variation_capital_succ,
    variation_wealth_one]
  change p.consumption 1 h + dateOneCapitalGain P X i p ε h +
    X.capitalPrice 1 h * p.capital 1 h + p.deposit 1 h =
    p.wealth 1 h + dateOneCapitalGain P X i p ε h + p.loan 1 h
  linarith [hbudget]

/-- The NONLINEAR profit equation and predetermined capital transition
    survive the date-zero change exactly in EVERY successor state. -/
theorem variation_wealth_transition_one
    (P : Primitives S) (X : Allocation S) (i : FirmType)
    (p : FirmPlan S) (ε : ℝ) (h : History S 0) (s : S)
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
    (capitalDateZeroVariation P X i p ε).wealth 1 (childHistory h s) =
        operatingProfit (X.inputPrice 1 (childHistory h s))
          (P.aggregateProductivity s * P.productivity i)
          ((capitalDateZeroVariation P X i p ε).capital 0 h)
          ((capitalDateZeroVariation P X i p ε).labor 1 (childHistory h s))
          P.alpha P.beta (X.wage 1 (childHistory h s)) +
        X.capitalPrice 1 (childHistory h s) *
          (1 - P.depreciation) *
          ((capitalDateZeroVariation P X i p ε).capital 0 h) -
        realRepayment
          ((capitalDateZeroVariation P X i p ε).face 0 h)
          (X.inflation 1 (childHistory h s)) := by
  rw [variation_wealth_one, variation_capital_zero]
  change p.wealth 1 (childHistory h s) +
      dateOneCapitalGain P X i p ε (childHistory h s) = _
  rw [hwealth]
  have hprev : previousHistory (childHistory h s) = h := by
    funext j
    rfl
  have hcur : currentState (childHistory h s) = s := by rfl
  simp only [dateOneCapitalGain, hprev, hcur]
  simp only [capitalDateZeroVariation]
  ring

/-- All adjusted inequalities, and ONLY the adjusted inequalities, are
    explicitly isolated. Date-one wealth, budgets and capital laws are
    NOT postulated as assumptions. -/
def CapitalVariationLocalBounds
    (P : Primitives S) (X : Allocation S) (i : FirmType)
    (p : FirmPlan S) (ε : ℝ) : Prop :=
  (∀ h : History S 0, FirmHistoryAdmissible P 0 h →
    0 < p.consumption 0 h - X.capitalPrice 0 h * ε ∧
    0 ≤ p.capital 0 h + ε ∧
    RobustCollateral (P.pledgeability i) P.depreciation
      (X.loanRate 0 h) (p.loan 0 h) (p.capital 0 h + ε)
      (fun s ↦ 0 < P.tree.transition (currentState h) s)
      (fun s ↦ X.inflation 1 (childHistory h s))
      (fun s ↦ X.capitalPrice 1 (childHistory h s))) ∧
  (∀ h : History S 1, FirmHistoryAdmissible P 1 h →
    0 < p.consumption 1 h + dateOneCapitalGain P X i p ε h)

/-- The literal global feasible set remains invariant under the
    explicit finite-date perturbation if its three LOCAL sign constraints
    hold; source budgets, nominal promises, and wealth law are derived. -/
theorem capitalDateZeroVariation_feasible
    (P : Primitives S) (I : InheritedState)
    (X : Allocation S) (i : FirmType)
    (p : FirmPlan S) (ε : ℝ)
    (hfeas : FirmFeasible P I X i p)
    (hloc : CapitalVariationLocalBounds P X i p ε) :
    FirmFeasible P I X i (capitalDateZeroVariation P X i p ε) := by
  rcases hfeas with ⟨hpos, hface, hbudget, hcoll, hwealth0, hwealthNext⟩
  rcases hloc with ⟨hloc0, hloc1⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro t h hadm
    by_cases ht0 : t = 0
    · subst t
      obtain ⟨hc, hk, _⟩ := hloc0 h hadm
      obtain ⟨_, _, hl, hb, hd⟩ := hpos 0 h hadm
      simpa [capitalDateZeroVariation] using
        (show 0 < p.consumption 0 h - X.capitalPrice 0 h * ε ∧
          0 ≤ p.capital 0 h + ε ∧ 0 ≤ p.labor 0 h ∧
          0 ≤ p.loan 0 h ∧ 0 ≤ p.deposit 0 h from
          ⟨hc, hk, hl, hb, hd⟩)
    · by_cases ht1 : t = 1
      · subst t
        obtain ⟨_, hk, hl, hb, hd⟩ := hpos 1 h hadm
        simpa [capitalDateZeroVariation] using
          (show 0 < p.consumption 1 h + dateOneCapitalGain P X i p ε h ∧
            0 ≤ p.capital 1 h ∧ 0 ≤ p.labor 1 h ∧
            0 ≤ p.loan 1 h ∧ 0 ≤ p.deposit 1 h from
            ⟨hloc1 h hadm, hk, hl, hb, hd⟩)
      · simpa [capitalDateZeroVariation, ht0, ht1] using
          hpos t h hadm
  · intro t h hadm
    exact hface t h hadm
  · intro t h hadm
    by_cases ht0 : t = 0
    · subst t
      exact variation_budget_zero P X i p ε h (hbudget 0 h hadm)
    · by_cases ht1 : t = 1
      · subst t
        exact variation_budget_one P X i p ε h (hbudget 1 h hadm)
      · simpa [capitalDateZeroVariation, ht0, ht1] using
          hbudget t h hadm
  · intro t h hadm
    by_cases ht0 : t = 0
    · subst t
      simpa [capitalDateZeroVariation] using (hloc0 h hadm).2.2
    · simpa [capitalDateZeroVariation, ht0] using hcoll t h hadm
  · intro h hadm
    exact hwealth0 h hadm
  · intro t h s hadm
    cases t with
    | zero =>
      exact variation_wealth_transition_one P X i p ε h s
        (hwealthNext 0 h s hadm)
    | succ t =>
      simpa [capitalDateZeroVariation] using
        hwealthNext (t + 1) h s hadm

end ProposedDateZeroCapitalDeviation
end Ventura26LiquidityAllocation
