import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Financial core for Ventura (2026)

This module formalizes the paper's signed promise, funding cash function,
supergradient inequality, and the equivalence between the gross and signed
financial KKT systems.  All rates, capital, collateral, and discount domains
used by the source lemmas are explicit.  In particular, the results below do
not cover zero capital, zero collateral, or equal borrowing and deposit rates.
-/

namespace Ventura26LiquidityAllocation

/-! ## Source domains and signed positions -/

/-- The source domain `R_L > R_D > 0`. -/
def PositiveRateDomain (loanRate depositRate : ℝ) : Prop :=
  0 < depositRate ∧ depositRate < loanRate

/-- The positive-domain assumptions of the financial KKT equivalence. -/
def PositiveFinancialDomain
    (loanRate depositRate collateral capital discount : ℝ) : Prop :=
  PositiveRateDomain loanRate depositRate ∧
    0 < collateral ∧ 0 < capital ∧ 0 < discount

/-- The loan position recovered from a signed nominal promise. -/
noncomputable def signedLoanPosition (loanRate promise : ℝ) : ℝ :=
  max promise 0 / loanRate

/-- The deposit position recovered from a signed nominal promise. -/
noncomputable def signedDepositPosition (depositRate promise : ℝ) : ℝ :=
  max (-promise) 0 / depositRate

/-- The paper's concave net cash inflow from a signed nominal promise. -/
noncomputable def fundingCash (loanRate depositRate promise : ℝ) : ℝ :=
  if 0 ≤ promise then promise / loanRate else promise / depositRate

@[simp] theorem fundingCash_of_nonneg
    {loanRate depositRate promise : ℝ} (hpromise : 0 ≤ promise) :
    fundingCash loanRate depositRate promise = promise / loanRate := by
  simp [fundingCash, hpromise]

@[simp] theorem fundingCash_of_neg
    {loanRate depositRate promise : ℝ} (hpromise : promise < 0) :
    fundingCash loanRate depositRate promise = promise / depositRate := by
  simp [fundingCash, not_le.mpr hpromise]

@[simp] theorem fundingCash_zero (loanRate depositRate : ℝ) :
    fundingCash loanRate depositRate 0 = 0 := by
  simp [fundingCash]

@[simp] theorem signedLoanPosition_zero (loanRate : ℝ) :
    signedLoanPosition loanRate 0 = 0 := by
  simp [signedLoanPosition]

@[simp] theorem signedDepositPosition_zero (depositRate : ℝ) :
    signedDepositPosition depositRate 0 = 0 := by
  simp [signedDepositPosition]

theorem signedLoanPosition_nonneg
    {loanRate promise : ℝ} (hloanRate : 0 < loanRate) :
    0 ≤ signedLoanPosition loanRate promise := by
  exact div_nonneg (le_max_right promise 0) hloanRate.le

theorem signedDepositPosition_nonneg
    {depositRate promise : ℝ} (hdepositRate : 0 < depositRate) :
    0 ≤ signedDepositPosition depositRate promise := by
  exact div_nonneg (le_max_right (-promise) 0) hdepositRate.le

theorem signed_positions_recover_promise
    {loanRate depositRate promise : ℝ}
    (hloanRate : 0 < loanRate) (hdepositRate : 0 < depositRate) :
    loanRate * signedLoanPosition loanRate promise -
        depositRate * signedDepositPosition depositRate promise = promise := by
  by_cases hpromise : 0 ≤ promise
  · have hnegative : max (-promise) 0 = 0 := by
      simp [max_eq_right (neg_nonpos.mpr hpromise)]
    rw [signedLoanPosition, signedDepositPosition, max_eq_left hpromise, hnegative]
    field_simp [hloanRate.ne', hdepositRate.ne']
    ring
  · have hpromiseNeg : promise < 0 := lt_of_not_ge hpromise
    have hpositive : 0 ≤ -promise := neg_nonneg.mpr hpromiseNeg.le
    rw [signedLoanPosition, signedDepositPosition,
      max_eq_right hpromiseNeg.le, max_eq_left hpositive]
    field_simp [hloanRate.ne', hdepositRate.ne']
    ring

theorem fundingCash_eq_recovered_net_cash
    {loanRate depositRate promise : ℝ}
    (hloanRate : 0 < loanRate) (hdepositRate : 0 < depositRate) :
    fundingCash loanRate depositRate promise =
      signedLoanPosition loanRate promise - signedDepositPosition depositRate promise := by
  by_cases hpromise : 0 ≤ promise
  · have hnegative : max (-promise) 0 = 0 := by
      simp [max_eq_right (neg_nonpos.mpr hpromise)]
    simp [fundingCash, hpromise, signedLoanPosition, signedDepositPosition]
  · have hpromiseNeg : promise < 0 := lt_of_not_ge hpromise
    have hpositive : 0 ≤ -promise := neg_nonneg.mpr hpromiseNeg.le
    simp [fundingCash, hpromise, signedLoanPosition, signedDepositPosition,
      max_eq_right hpromiseNeg.le, max_eq_left hpositive]
    ring

/-! ## Gross portfolios and signed feasibility -/

/-- A nonnegative gross loan/deposit portfolio implementing a promise and
satisfying the paper's repayment-collateral limit. -/
def GrossPortfolioFeasible
    (loanRate depositRate collateral capital promise loan deposit : ℝ) : Prop :=
  0 ≤ loan ∧ 0 ≤ deposit ∧
    loanRate * loan - depositRate * deposit = promise ∧
    loanRate * loan ≤ collateral * capital

/-- Feasibility of the same promise in the signed representation. -/
def SignedPromiseFeasible (collateral capital promise : ℝ) : Prop :=
  promise ≤ collateral * capital

theorem gross_net_cash_le_fundingCash
    {loanRate depositRate loan deposit : ℝ}
    (hrates : PositiveRateDomain loanRate depositRate)
    (hloan : 0 ≤ loan) (hdeposit : 0 ≤ deposit) :
    loan - deposit ≤
      fundingCash loanRate depositRate (loanRate * loan - depositRate * deposit) := by
  rcases hrates with ⟨hdepositRate, hrate⟩
  have hloanRate : 0 < loanRate := hdepositRate.trans hrate
  by_cases hpromise : 0 ≤ loanRate * loan - depositRate * deposit
  · rw [fundingCash_of_nonneg hpromise]
    have hratio : depositRate / loanRate < 1 := (div_lt_one hloanRate).2 hrate
    have hmul : depositRate / loanRate * deposit ≤ deposit := by
      exact (mul_le_mul_of_nonneg_right hratio.le hdeposit).trans_eq (one_mul deposit)
    calc
      loan - deposit ≤ loan - depositRate / loanRate * deposit :=
        sub_le_sub_left hmul loan
      _ = (loanRate * loan - depositRate * deposit) / loanRate := by
        field_simp [hloanRate.ne']
  · have hpromiseNeg : loanRate * loan - depositRate * deposit < 0 :=
      lt_of_not_ge hpromise
    rw [fundingCash_of_neg hpromiseNeg]
    have hratio : 1 < loanRate / depositRate := (one_lt_div hdepositRate).2 hrate
    have hmul : loan ≤ loanRate / depositRate * loan := by
      exact (one_mul loan).symm.trans_le (mul_le_mul_of_nonneg_right hratio.le hloan)
    calc
      loan - deposit ≤ loanRate / depositRate * loan - deposit :=
        sub_le_sub_right hmul deposit
      _ = (loanRate * loan - depositRate * deposit) / depositRate := by
        field_simp [hdepositRate.ne']

theorem gross_net_cash_lt_fundingCash_of_both_pos
    {loanRate depositRate loan deposit : ℝ}
    (hrates : PositiveRateDomain loanRate depositRate)
    (hloan : 0 < loan) (hdeposit : 0 < deposit) :
    loan - deposit <
      fundingCash loanRate depositRate (loanRate * loan - depositRate * deposit) := by
  rcases hrates with ⟨hdepositRate, hrate⟩
  have hloanRate : 0 < loanRate := hdepositRate.trans hrate
  by_cases hpromise : 0 ≤ loanRate * loan - depositRate * deposit
  · rw [fundingCash_of_nonneg hpromise]
    have hratio : depositRate / loanRate < 1 := (div_lt_one hloanRate).2 hrate
    have hmul : depositRate / loanRate * deposit < deposit := by
      simpa only [one_mul] using mul_lt_mul_of_pos_right hratio hdeposit
    calc
      loan - deposit < loan - depositRate / loanRate * deposit :=
        sub_lt_sub_left hmul loan
      _ = (loanRate * loan - depositRate * deposit) / loanRate := by
        field_simp [hloanRate.ne']
  · have hpromiseNeg : loanRate * loan - depositRate * deposit < 0 :=
      lt_of_not_ge hpromise
    rw [fundingCash_of_neg hpromiseNeg]
    have hratio : 1 < loanRate / depositRate := (one_lt_div hdepositRate).2 hrate
    have hmul : loan < loanRate / depositRate * loan := by
      simpa only [one_mul] using mul_lt_mul_of_pos_right hratio hloan
    calc
      loan - deposit < loanRate / depositRate * loan - deposit :=
        sub_lt_sub_right hmul deposit
      _ = (loanRate * loan - depositRate * deposit) / depositRate := by
        field_simp [hdepositRate.ne']

theorem recovered_portfolio_feasible_iff
    {loanRate depositRate collateral capital promise : ℝ}
    (hrates : PositiveRateDomain loanRate depositRate)
    (hcollateral : 0 < collateral) (hcapital : 0 < capital) :
    GrossPortfolioFeasible loanRate depositRate collateral capital promise
        (signedLoanPosition loanRate promise)
        (signedDepositPosition depositRate promise) ↔
      SignedPromiseFeasible collateral capital promise := by
  rcases hrates with ⟨hdepositRate, hrate⟩
  have hloanRate : 0 < loanRate := hdepositRate.trans hrate
  constructor
  · intro h
    rcases h with ⟨hloan, hdeposit, hrecover, hcoverage⟩
    unfold SignedPromiseFeasible
    have hnonneg : 0 ≤ depositRate * signedDepositPosition depositRate promise :=
      mul_nonneg hdepositRate.le (signedDepositPosition_nonneg hdepositRate)
    linarith
  · intro hpromise
    refine ⟨signedLoanPosition_nonneg hloanRate,
      signedDepositPosition_nonneg hdepositRate,
      signed_positions_recover_promise hloanRate hdepositRate, ?_⟩
    have hproduct : 0 < collateral * capital := mul_pos hcollateral hcapital
    have hmax : max promise 0 ≤ collateral * capital :=
      max_le hpromise hproduct.le
    calc
      loanRate * signedLoanPosition loanRate promise = max promise 0 := by
        rw [signedLoanPosition, mul_div_cancel₀ _ hloanRate.ne']
      _ ≤ collateral * capital := hmax

/-- Source Lemma 3.4, in its exact financial content.  Every feasible gross
portfolio induces a signed-feasible promise whose recovered portfolio keeps the
same future payment, weakly increases current cash (strictly when both gross
positions are positive), and preserves collateral feasibility.  Conversely,
every signed-feasible promise is implemented by its recovered gross portfolio.
Strictly increasing utility therefore rules out a positive loan and deposit in
an optimum without adding an objective or optimality conclusion as an input. -/
theorem signedFundingEquivalence
    {loanRate depositRate collateral capital : ℝ}
    (hrates : PositiveRateDomain loanRate depositRate)
    (hcollateral : 0 < collateral) (hcapital : 0 < capital) :
    (∀ loan deposit : ℝ,
      GrossPortfolioFeasible loanRate depositRate collateral capital
          (loanRate * loan - depositRate * deposit) loan deposit →
        SignedPromiseFeasible collateral capital
            (loanRate * loan - depositRate * deposit) ∧
        loan - deposit ≤ fundingCash loanRate depositRate
            (loanRate * loan - depositRate * deposit) ∧
        ((0 < loan ∧ 0 < deposit) →
          loan - deposit < fundingCash loanRate depositRate
            (loanRate * loan - depositRate * deposit)) ∧
        GrossPortfolioFeasible loanRate depositRate collateral capital
            (loanRate * loan - depositRate * deposit)
            (signedLoanPosition loanRate
              (loanRate * loan - depositRate * deposit))
            (signedDepositPosition depositRate
              (loanRate * loan - depositRate * deposit))) ∧
    (∀ promise : ℝ,
      SignedPromiseFeasible collateral capital promise →
        GrossPortfolioFeasible loanRate depositRate collateral capital promise
          (signedLoanPosition loanRate promise)
          (signedDepositPosition depositRate promise)) := by
  constructor
  · intro loan deposit hgross
    have hsigned : SignedPromiseFeasible collateral capital
        (loanRate * loan - depositRate * deposit) := by
      rcases hrates with ⟨hdepositRate, hrate⟩
      have hnonneg : 0 ≤ depositRate * deposit :=
        mul_nonneg hdepositRate.le hgross.2.1
      unfold SignedPromiseFeasible
      linarith [hgross.2.2.2]
    refine ⟨hsigned,
      gross_net_cash_le_fundingCash hrates hgross.1 hgross.2.1,
      ?_, (recovered_portfolio_feasible_iff hrates hcollateral hcapital).2 hsigned⟩
    rintro ⟨hloan, hdeposit⟩
    exact gross_net_cash_lt_fundingCash_of_both_pos hrates hloan hdeposit
  · intro promise hsigned
    exact (recovered_portfolio_feasible_iff hrates hcollateral hcapital).2 hsigned

/-! ## Theorem 3.3: financing capacity -/

/-- Maximum capital financed from own resources under the repayment limit. -/
noncomputable def financingCapacity
    (ownResources capitalPrice collateral loanRate : ℝ) : ℝ :=
  ownResources / (capitalPrice - collateral / loanRate)

/-- Source Proposition 3.3: holding own resources, the capital price, and
collateral fixed, the derivative with respect to the loan rate has the displayed
formula and is strictly negative on the paper's positive domain. -/
theorem financingCapacity_hasDerivAt_and_deriv_neg
    {ownResources capitalPrice collateral loanRate : ℝ}
    (hresources : 0 < ownResources) (hcollateral : 0 < collateral)
    (hloanRate : 0 < loanRate)
    (hbounded : collateral / loanRate < capitalPrice) :
    HasDerivAt
        (fun rate ↦ financingCapacity ownResources capitalPrice collateral rate)
        (-ownResources * collateral /
          (loanRate ^ 2 * (capitalPrice - collateral / loanRate) ^ 2))
        loanRate ∧
      -ownResources * collateral /
          (loanRate ^ 2 * (capitalPrice - collateral / loanRate) ^ 2) < 0 := by
  have hdenomPos : 0 < capitalPrice - collateral / loanRate := sub_pos.mpr hbounded
  have hdenomNe : capitalPrice - collateral / loanRate ≠ 0 := hdenomPos.ne'
  have hquotRaw := (hasDerivAt_inv hloanRate.ne').const_mul collateral
  have hquot : HasDerivAt
      (fun rate : ℝ ↦ collateral / rate)
      (-collateral / loanRate ^ 2) loanRate := by
    simpa [div_eq_mul_inv] using hquotRaw
  have hinner : HasDerivAt
      (fun rate : ℝ ↦ capitalPrice - collateral / rate)
      (collateral / loanRate ^ 2) loanRate := by
    unfold HasDerivAt HasDerivAtFilter at hquot ⊢
    convert hquot.const_sub capitalPrice using 1
    ext
    simp [div_eq_mul_inv]
  have hderiv := (hasDerivAt_const loanRate ownResources).div hinner hdenomNe
  constructor
  · unfold financingCapacity
    have hcoef :
        -ownResources * collateral /
            (loanRate ^ 2 * (capitalPrice - collateral / loanRate) ^ 2) =
          (0 * (capitalPrice - collateral / loanRate) -
              ownResources * (collateral / loanRate ^ 2)) /
            (capitalPrice - collateral / loanRate) ^ 2 := by
      field_simp [hloanRate.ne', hdenomNe]
      ring
    rw [hcoef]
    exact hderiv
  · have hnumNeg : -ownResources * collateral < 0 :=
      mul_neg_of_neg_of_pos (neg_neg_of_pos hresources) hcollateral
    have hdenomSqPos :
        0 < loanRate ^ 2 * (capitalPrice - collateral / loanRate) ^ 2 :=
      mul_pos (sq_pos_of_pos hloanRate) (sq_pos_of_pos hdenomPos)
    exact div_neg_of_neg_of_pos hnumNeg hdenomSqPos

/-! ## Theorem 3.5: exact funding supergradient -/

/-- The source definition of a supergradient of the concave funding-cash
function: its affine support is above the function at every promise. -/
def IsFundingSupergradient
    (loanRate depositRate promise slope : ℝ) : Prop :=
  ∀ alternative : ℝ,
    fundingCash loanRate depositRate alternative ≤
      fundingCash loanRate depositRate promise + slope * (alternative - promise)

/-- The three branches of the paper's exact superdifferential.  The middle
branch is deliberately an interval rather than either interior Euler equation. -/
def FundingSupergradientCases
    (loanRate depositRate promise slope : ℝ) : Prop :=
  (promise < 0 ∧ slope = 1 / depositRate) ∨
  (promise = 0 ∧ 1 / loanRate ≤ slope ∧ slope ≤ 1 / depositRate) ∨
  (0 < promise ∧ slope = 1 / loanRate)

/-- Source Lemma 3.5: exact characterization of the funding supergradient,
including the zero-promise kink. -/
theorem isFundingSupergradient_iff_cases
    {loanRate depositRate promise slope : ℝ}
    (hrates : PositiveRateDomain loanRate depositRate) :
    IsFundingSupergradient loanRate depositRate promise slope ↔
      FundingSupergradientCases loanRate depositRate promise slope := by
  rcases hrates with ⟨hdepositRate, hrate⟩
  have hloanRate : 0 < loanRate := hdepositRate.trans hrate
  have hinv : 1 / loanRate < 1 / depositRate :=
    one_div_lt_one_div_of_lt hdepositRate hrate
  constructor
  · intro hsuper
    rcases lt_trichotomy promise 0 with hneg | hzero | hpos
    · left
      refine ⟨hneg, le_antisymm ?_ ?_⟩
      · have htest := hsuper (2 * promise)
        have htestNeg : 2 * promise < 0 := mul_neg_of_pos_of_neg (by norm_num) hneg
        rw [fundingCash_of_neg htestNeg, fundingCash_of_neg hneg] at htest
        rw [div_eq_mul_inv] at htest ⊢
        ring_nf at htest
        nlinarith
      · have htest := hsuper (promise / 2)
        have htestNeg : promise / 2 < 0 := div_neg_of_neg_of_pos hneg (by norm_num)
        rw [fundingCash_of_neg htestNeg, fundingCash_of_neg hneg] at htest
        rw [div_eq_mul_inv] at htest ⊢
        ring_nf at htest
        nlinarith
    · subst promise
      right
      left
      refine ⟨rfl, ?_, ?_⟩
      · have htest := hsuper 1
        norm_num [fundingCash] at htest ⊢
        exact htest
      · have htest := hsuper (-1)
        norm_num [fundingCash] at htest ⊢
        rw [div_eq_mul_inv] at htest
        linarith
    · right
      right
      refine ⟨hpos, le_antisymm ?_ ?_⟩
      · have htest := hsuper (promise / 2)
        have htestPos : 0 < promise / 2 := div_pos hpos (by norm_num)
        rw [fundingCash_of_nonneg htestPos.le, fundingCash_of_nonneg hpos.le] at htest
        rw [div_eq_mul_inv] at htest ⊢
        ring_nf at htest
        nlinarith
      · have htest := hsuper (2 * promise)
        have htestPos : 0 < 2 * promise := mul_pos (by norm_num) hpos
        rw [fundingCash_of_nonneg htestPos.le, fundingCash_of_nonneg hpos.le] at htest
        rw [div_eq_mul_inv] at htest ⊢
        ring_nf at htest
        nlinarith
  · intro hcases alternative
    rcases hcases with ⟨hpromise, rfl⟩ | ⟨hzero, hlower, hupper⟩ |
        ⟨hpromise, rfl⟩
    · rw [fundingCash_of_neg hpromise]
      by_cases halternative : 0 ≤ alternative
      · rw [fundingCash_of_nonneg halternative]
        have hmul := mul_le_mul_of_nonneg_left hinv.le halternative
        calc
          alternative / loanRate ≤ alternative / depositRate := by
            simpa [div_eq_mul_inv] using hmul
          _ = promise / depositRate +
              1 / depositRate * (alternative - promise) := by ring
      · have halternativeNeg : alternative < 0 := lt_of_not_ge halternative
        rw [fundingCash_of_neg halternativeNeg]
        exact le_of_eq (by ring)
    · subst promise
      rw [fundingCash_zero]
      by_cases halternative : 0 ≤ alternative
      · rw [fundingCash_of_nonneg halternative]
        have hmul := mul_le_mul_of_nonneg_left hlower halternative
        rw [div_eq_mul_inv] at hmul ⊢
        simpa [mul_comm] using hmul
      · have halternativeNeg : alternative < 0 := lt_of_not_ge halternative
        rw [fundingCash_of_neg halternativeNeg]
        have hmul := mul_le_mul_of_nonpos_left hupper halternativeNeg.le
        rw [div_eq_mul_inv] at hmul ⊢
        simpa [mul_comm] using hmul
    · rw [fundingCash_of_nonneg hpromise.le]
      by_cases halternative : 0 ≤ alternative
      · rw [fundingCash_of_nonneg halternative]
        exact le_of_eq (by ring)
      · have halternativeNeg : alternative < 0 := lt_of_not_ge halternative
        rw [fundingCash_of_neg halternativeNeg]
        have hmul := mul_le_mul_of_nonpos_left hinv.le halternativeNeg.le
        calc
          alternative / depositRate ≤ alternative / loanRate := by
            simpa [div_eq_mul_inv] using hmul
          _ = promise / loanRate +
              1 / loanRate * (alternative - promise) := by ring

/-! ## Gross and signed financial KKT systems -/

/-- The paper's normalized gross financial KKT conditions.  Nonnegativity of
the gross positions is kept outside this predicate, as in Lemma 3.6. -/
def GrossFinancialKKT
    (loanRate depositRate collateral capital discount loan deposit dual : ℝ) : Prop :=
  0 ≤ collateral * capital - loanRate * loan ∧
  0 ≤ dual ∧
  dual * (collateral * capital - loanRate * loan) = 0 ∧
  0 ≤ loanRate * (discount + dual) - 1 ∧
  (loanRate * (discount + dual) - 1) * loan = 0 ∧
  0 ≤ 1 - depositRate * discount ∧
  (1 - depositRate * discount) * deposit = 0

/-- The signed financial KKT conditions: signed collateral feasibility,
complementarity, and the global supergradient inequality. -/
def SignedFinancialKKT
    (loanRate depositRate collateral capital discount promise dual : ℝ) : Prop :=
  0 ≤ collateral * capital - promise ∧
  0 ≤ dual ∧
  dual * (collateral * capital - promise) = 0 ∧
  IsFundingSupergradient loanRate depositRate promise (discount + dual)

/-- Source Lemma 3.2 in normalized financial variables: the gross KKT
conditions cannot hold with both a strictly positive loan and a strictly
positive deposit when the loan rate is strictly above the deposit rate. -/
theorem no_simultaneous_saving_and_borrowing
    {loanRate depositRate collateral capital discount loan deposit dual : ℝ}
    (hdomain : PositiveFinancialDomain
      loanRate depositRate collateral capital discount)
    (hloan : 0 ≤ loan) (hdeposit : 0 ≤ deposit)
    (hkkt : GrossFinancialKKT
      loanRate depositRate collateral capital discount loan deposit dual) :
    loan = 0 ∨ deposit = 0 := by
  rcases hdomain with ⟨⟨hdepositRate, hrate⟩, hcollateral, hcapital, hdiscount⟩
  have hloanRate : 0 < loanRate := hdepositRate.trans hrate
  have hinv : 1 / loanRate < 1 / depositRate :=
    one_div_lt_one_div_of_lt hdepositRate hrate
  rcases hkkt with ⟨hcoverage, hdual, hcollateralComp,
    hloanSlack, hloanComp, hdepositSlack, hdepositComp⟩
  by_cases hloanZero : loan = 0
  · exact Or.inl hloanZero
  · right
    by_contra hdepositZero
    have hloanPos : 0 < loan := lt_of_le_of_ne hloan (Ne.symm hloanZero)
    have hdepositPos : 0 < deposit :=
      lt_of_le_of_ne hdeposit (Ne.symm hdepositZero)
    have hloanSlackZero : loanRate * (discount + dual) - 1 = 0 :=
      (mul_eq_zero.mp hloanComp).resolve_right hloanPos.ne'
    have hdepositSlackZero : 1 - depositRate * discount = 0 :=
      (mul_eq_zero.mp hdepositComp).resolve_right hdepositPos.ne'
    have hloanEuler : discount + dual = 1 / loanRate := by
      apply (eq_div_iff hloanRate.ne').2
      nlinarith
    have hdepositEuler : discount = 1 / depositRate := by
      apply (eq_div_iff hdepositRate.ne').2
      nlinarith
    linarith

/-- The source's first regime: positive borrowing at the collateral limit with
a strictly valuable collateral constraint. -/
def ValuableCollateralLoan
    (loanRate collateral capital discount promise dual : ℝ) : Prop :=
  promise = collateral * capital ∧ 0 < promise ∧ 0 < dual ∧
  discount < 1 / loanRate ∧ dual = 1 / loanRate - discount

/-- Positive borrowing with strictly slack collateral. -/
def SlackCollateralLoan
    (loanRate collateral capital discount promise dual : ℝ) : Prop :=
  0 < promise ∧ promise < collateral * capital ∧ dual = 0 ∧
  discount = 1 / loanRate

/-- The zero-funding kink: neither a loan nor a deposit. -/
def SelfFinancingWithoutDeposit
    (loanRate depositRate discount promise dual : ℝ) : Prop :=
  promise = 0 ∧ dual = 0 ∧
  1 / loanRate ≤ discount ∧ discount ≤ 1 / depositRate

/-- A strictly negative promise, hence a positive entrepreneurial deposit. -/
def EntrepreneurDeposit
    (depositRate discount promise dual : ℝ) : Prop :=
  promise < 0 ∧ dual = 0 ∧ discount = 1 / depositRate

/-- The separate source boundary: collateral is active but has zero marginal
value.  It must not be folded into the strictly valuable-collateral regime. -/
def ActiveCollateralZeroDual
    (loanRate collateral capital discount promise dual : ℝ) : Prop :=
  promise = collateral * capital ∧ 0 < promise ∧ dual = 0 ∧
  discount = 1 / loanRate

/-- The exhaustive five-way source classification, including the active
collateral/zero-dual boundary. -/
def FinancialRegimeCases
    (loanRate depositRate collateral capital discount promise dual : ℝ) : Prop :=
  ValuableCollateralLoan loanRate collateral capital discount promise dual ∨
  SlackCollateralLoan loanRate collateral capital discount promise dual ∨
  SelfFinancingWithoutDeposit loanRate depositRate discount promise dual ∨
  EntrepreneurDeposit depositRate discount promise dual ∨
  ActiveCollateralZeroDual loanRate collateral capital discount promise dual

/-- The signed KKT system is exactly the union of the five financial regimes
listed by the paper (the table's four rows plus its zero-dual active boundary). -/
theorem signedFinancialKKT_iff_five_regimes
    {loanRate depositRate collateral capital discount promise dual : ℝ}
    (hdomain : PositiveFinancialDomain
      loanRate depositRate collateral capital discount) :
    SignedFinancialKKT loanRate depositRate collateral capital discount promise dual ↔
      FinancialRegimeCases
        loanRate depositRate collateral capital discount promise dual := by
  rcases hdomain with ⟨hrates, hcollateral, hcapital, hdiscount⟩
  have hproduct : 0 < collateral * capital := mul_pos hcollateral hcapital
  have hsuperIff := isFundingSupergradient_iff_cases
    (promise := promise) (slope := discount + dual) hrates
  constructor
  · intro hkkt
    rcases hkkt with ⟨hfeasible, hdual, hcomp, hsuper⟩
    have hcases := hsuperIff.mp hsuper
    rcases hcases with ⟨hpromise, hslope⟩ |
        ⟨hzero, hlower, hupper⟩ | ⟨hpromise, hslope⟩
    · right
      right
      right
      left
      have hslackPos : 0 < collateral * capital - promise := by linarith
      have hdualZero : dual = 0 := by nlinarith
      exact ⟨hpromise, hdualZero, by linarith⟩
    · right
      right
      left
      have hslackPos : 0 < collateral * capital - promise := by linarith
      have hdualZero : dual = 0 := by nlinarith
      subst promise
      exact ⟨rfl, hdualZero, by linarith, by linarith⟩
    · by_cases hdualZero : dual = 0
      · have hdiscountEq : discount = 1 / loanRate := by linarith
        have hpromiseLe : promise ≤ collateral * capital := by linarith
        rcases hpromiseLe.eq_or_lt with heq | hlt
        · right
          right
          right
          right
          exact ⟨heq, hpromise, hdualZero, hdiscountEq⟩
        · right
          left
          exact ⟨hpromise, hlt, hdualZero, hdiscountEq⟩
      · left
        have hdualPos : 0 < dual := lt_of_le_of_ne hdual (Ne.symm hdualZero)
        have hslackZero : collateral * capital - promise = 0 := by
          exact (mul_eq_zero.mp hcomp).resolve_left hdualZero
        refine ⟨by linarith, hpromise, hdualPos, ?_, by linarith⟩
        linarith
  · intro hregime
    rcases hregime with hvaluable | hslack | hself | hdeposit | hboundary
    · rcases hvaluable with ⟨rfl, hpromise, hdual, hdiscount, hdualEq⟩
      refine ⟨by linarith, hdual.le, by ring, hsuperIff.mpr ?_⟩
      right
      right
      exact ⟨hpromise, by linarith⟩
    · rcases hslack with ⟨hpromise, hstrict, rfl, hdiscountEq⟩
      refine ⟨by linarith, le_rfl, by ring, hsuperIff.mpr ?_⟩
      right
      right
      exact ⟨hpromise, by linarith⟩
    · rcases hself with ⟨rfl, rfl, hlower, hupper⟩
      refine ⟨by simpa using hproduct.le, le_rfl, by ring, hsuperIff.mpr ?_⟩
      right
      left
      exact ⟨rfl, by simpa using hlower, by simpa using hupper⟩
    · rcases hdeposit with ⟨hpromise, rfl, hdiscountEq⟩
      refine ⟨by linarith, le_rfl, by ring, hsuperIff.mpr ?_⟩
      left
      exact ⟨hpromise, by linarith⟩
    · rcases hboundary with ⟨rfl, hpromise, rfl, hdiscountEq⟩
      refine ⟨by linarith, le_rfl, by ring, hsuperIff.mpr ?_⟩
      right
      right
      exact ⟨hpromise, by linarith⟩

end Ventura26LiquidityAllocation
