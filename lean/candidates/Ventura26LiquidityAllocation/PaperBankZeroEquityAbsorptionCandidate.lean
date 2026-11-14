import Ventura26LiquidityAllocation.PaperBankPathwiseGrowthInductionCandidate

/-!
# Zero bank equity is absorbing under the SOURCE continuation constraint

This addresses a stronger-than-necessary hypothesis in the previous
strict-positive-equity pathwise induction. The SOURCE bank continuation
feasibility demands only nonnegative individual bank equity. If bank
equity is zero at a supported history, the feasible portfolio is
identically zero, hence next-period equity is zero for every supported
transition and payment shock.

No claim is made about new banks entering or any exogenous equity
injection: this is a property of one continuing bank's existing policy.
-/

namespace Ventura26LiquidityAllocation
namespace ProposedBankZeroEquityAbsorption

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- The literal detailed OTC return is zero on a zero-sized portfolio.
Homogeneity of the exact matching and facility functions proves it. -/
theorem source_zero_portfolio_detailed_return
    (P : Primitives S) (X : Allocation S)
    (t : ℕ) (h : History S t) (tightness : ℝ)
    (omega : BankPayment) :
    bankDetailedPortfolioReturnAt P X t h tightness 0 0 0 omega = 0 := by
  have hscale := bankDetailedPortfolioReturnAt_scale
    P X t h tightness 0 0 0 2 (by norm_num) omega
  simp only [mul_zero] at hscale
  linarith

/-- Zero individual equity is an absorbing boundary on the SOURCE
dynamically feasible, aggregate-supported continuation tree.
This never divides by zero or pretends that bank entry recapitalizes
a preexisting bank. -/
theorem source_feasible_zero_equity_is_absorbing
    (P : Primitives S) (X : Allocation S)
    (t : ℕ) (h : History S t) (initialEquity : ℝ)
    (q : BankContinuationPolicy S P.paymentSupport)
    (hfeasible : BankContinuationFeasibleAt P X t h initialEquity q)
    (n : ℕ) (future : Fin n → S)
    (payments : Fin n → P.paymentSupport)
    (hpath : FuturePathSupported P.tree (currentState h) n future)
    (hzero : q.equity n future payments = 0)
    (s : S) (omega : P.paymentSupport)
    (htrans : 0 < P.tree.transition
      (currentState (continuationHistory h future)) s) :
    q.equity (n + 1)
      (childFutureHistory future s)
      (childPaymentHistory payments omega) = 0 := by
  have hn := hfeasible.2 n future payments hpath
  rcases hn with
    ⟨_, _, _, _, _, _, hzeroControls, _, _, _, _, _, _, hsettlement⟩
  obtain ⟨_, _, hloans, hreserves, hdeposits⟩ := hzeroControls hzero
  have hchild := (hsettlement omega).2.2 s htrans
  rw [hloans, hreserves, hdeposits,
    source_zero_portfolio_detailed_return] at hchild
  simpa using hchild

#print axioms source_zero_portfolio_detailed_return
#print axioms source_feasible_zero_equity_is_absorbing

end ProposedBankZeroEquityAbsorption
end Ventura26LiquidityAllocation
