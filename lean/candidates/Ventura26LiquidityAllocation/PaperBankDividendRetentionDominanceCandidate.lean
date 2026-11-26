import Ventura26LiquidityAllocation.PaperBankSourceNextEquityBridgeCandidate

/-!
# Bank dividends and retained equity: conditional global dominance

This file isolates the missing dividend/retention choice in the SOURCE
bank Bellman problem. It is NOT a derivation of the multiplier k, of
the all-portfolios continuation upper bound, or of BankOptimal.

Unlike bank KKT statements at fixed retained equity, the second
theorem compares arbitrary dynamically feasible continuations with
DIFFERENT initial dividends and retained equity. The candidate's
attainment and the global one-step bound are explicit premises.
-/

namespace Ventura26LiquidityAllocation
namespace ProposedBankDividendRetentionDominance

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- Algebra: when the marginal continuation coefficient is at least one,
a dividend cannot increase the value beyond full retained equity, if
continuation is itself bounded by k times retained equity. -/
theorem dividend_retention_algebraic_upper_bound
    (equity dividend retained continuation multiplier : ℝ)
    (hretained : retained = equity - dividend)
    (hdividend : 0 ≤ dividend)
    (hmultiplier : 1 ≤ multiplier)
    (hcontinuation : continuation ≤ multiplier * retained) :
    dividend + continuation ≤ multiplier * equity := by
  rw [hretained] at hcontinuation
  have hnonneg : 0 ≤ (multiplier - 1) * dividend :=
    mul_nonneg (sub_nonneg.mpr hmultiplier) hdividend
  nlinarith

/-- A SOURCE-feasible continuation chooses nonnegative dividends and
retained equity satisfying the source balance identity at date zero.
Given a one-step continuation bound at its own retained equity, its
full dividend-plus-Bellman objective is bounded by k times initial
equity. Here deposits and dividends are distinct source decisions. -/
theorem source_bank_dividend_portfolio_upper_bound
    (P : Primitives S) (X : Allocation S)
    (t : ℕ) (h : History S t)
    (equity multiplier : ℝ)
    (q : BankContinuationPolicy S P.paymentSupport)
    (V : ℝ → History S (t + 1) → ℝ)
    (hfeasible : BankContinuationFeasibleAt P X t h equity q)
    (hmultiplier : 1 ≤ multiplier)
    (hportfolio : bankBellmanContinuationAt P X t h
        (bankOTCDeficitSlopeAt P X t h (X.bankTightness t h))
        (bankOTCSurplusSlopeAt P X t h (X.bankTightness t h))
        (q.loans 0 (fun j => Fin.elim0 j) (fun j => Fin.elim0 j))
        (q.reserves 0 (fun j => Fin.elim0 j) (fun j => Fin.elim0 j))
        (q.deposits 0 (fun j => Fin.elim0 j) (fun j => Fin.elim0 j))
        V ≤ multiplier *
          q.retainedEquity 0 (fun j => Fin.elim0 j) (fun j => Fin.elim0 j)) :
    q.dividend 0 (fun j => Fin.elim0 j) (fun j => Fin.elim0 j) +
      bankBellmanContinuationAt P X t h
        (bankOTCDeficitSlopeAt P X t h (X.bankTightness t h))
        (bankOTCSurplusSlopeAt P X t h (X.bankTightness t h))
        (q.loans 0 (fun j => Fin.elim0 j) (fun j => Fin.elim0 j))
        (q.reserves 0 (fun j => Fin.elim0 j) (fun j => Fin.elim0 j))
        (q.deposits 0 (fun j => Fin.elim0 j) (fun j => Fin.elim0 j))
        V ≤ multiplier * equity := by
  let emptyS : Fin 0 → S := fun j => Fin.elim0 j
  let emptyOmega : Fin 0 → P.paymentSupport := fun j => Fin.elim0 j
  have hdateZero := hfeasible.2 0 emptyS emptyOmega (by trivial)
  rcases hdateZero with
    ⟨_, hdividend, _, _, _, _, _, _, hretained, _, _, _, _, _⟩
  have hinitial : q.equity 0 emptyS emptyOmega = equity := hfeasible.1
  have hretainedActual :
      q.retainedEquity 0 emptyS emptyOmega =
        equity - q.dividend 0 emptyS emptyOmega := by
    rw [hretained, hinitial]
  exact dividend_retention_algebraic_upper_bound equity
    (q.dividend 0 emptyS emptyOmega)
    (q.retainedEquity 0 emptyS emptyOmega)
    (bankBellmanContinuationAt P X t h
      (bankOTCDeficitSlopeAt P X t h (X.bankTightness t h))
      (bankOTCSurplusSlopeAt P X t h (X.bankTightness t h))
      (q.loans 0 emptyS emptyOmega)
      (q.reserves 0 emptyS emptyOmega)
      (q.deposits 0 emptyS emptyOmega) V)
    multiplier hretainedActual hdividend hmultiplier hportfolio

/-- Joint one-step Bellman ranking over ALL feasible continuation policies
at the same starting equity. The global portfolio envelope, the existence
of a feasible candidate with zero dividend, and attainment of the upper
bound are transparent hypotheses, not secretly proved by static KKT.

This theorem alone does not compare the actual infinite-horizon payoffs
without the separate tail bound, equality and terminal arguments. -/
theorem source_bank_joint_dividend_portfolio_ranking
    (P : Primitives S) (X : Allocation S)
    (t : ℕ) (h : History S t)
    (equity multiplier : ℝ)
    (V : ℝ → History S (t + 1) → ℝ)
    (candidate : BankContinuationPolicy S P.paymentSupport)
    (hmultiplier : 1 ≤ multiplier)
    (hcandidate : BankContinuationFeasibleAt P X t h equity candidate)
    (hzeroDividend :
      candidate.dividend 0 (fun j => Fin.elim0 j) (fun j => Fin.elim0 j) = 0)
    (hattains : bankBellmanContinuationAt P X t h
        (bankOTCDeficitSlopeAt P X t h (X.bankTightness t h))
        (bankOTCSurplusSlopeAt P X t h (X.bankTightness t h))
        (candidate.loans 0 (fun j => Fin.elim0 j) (fun j => Fin.elim0 j))
        (candidate.reserves 0 (fun j => Fin.elim0 j) (fun j => Fin.elim0 j))
        (candidate.deposits 0 (fun j => Fin.elim0 j) (fun j => Fin.elim0 j))
        V = multiplier * equity)
    (hglobalPortfolioBound : ∀ alternative,
      BankContinuationFeasibleAt P X t h equity alternative →
      bankBellmanContinuationAt P X t h
        (bankOTCDeficitSlopeAt P X t h (X.bankTightness t h))
        (bankOTCSurplusSlopeAt P X t h (X.bankTightness t h))
        (alternative.loans 0 (fun j => Fin.elim0 j) (fun j => Fin.elim0 j))
        (alternative.reserves 0 (fun j => Fin.elim0 j) (fun j => Fin.elim0 j))
        (alternative.deposits 0 (fun j => Fin.elim0 j) (fun j => Fin.elim0 j))
        V ≤ multiplier *
          alternative.retainedEquity 0
            (fun j => Fin.elim0 j) (fun j => Fin.elim0 j)) :
    ∀ alternative,
      BankContinuationFeasibleAt P X t h equity alternative →
      alternative.dividend 0 (fun j => Fin.elim0 j) (fun j => Fin.elim0 j) +
        bankBellmanContinuationAt P X t h
          (bankOTCDeficitSlopeAt P X t h (X.bankTightness t h))
          (bankOTCSurplusSlopeAt P X t h (X.bankTightness t h))
          (alternative.loans 0 (fun j => Fin.elim0 j) (fun j => Fin.elim0 j))
          (alternative.reserves 0 (fun j => Fin.elim0 j) (fun j => Fin.elim0 j))
          (alternative.deposits 0 (fun j => Fin.elim0 j) (fun j => Fin.elim0 j))
          V ≤
      candidate.dividend 0 (fun j => Fin.elim0 j) (fun j => Fin.elim0 j) +
        bankBellmanContinuationAt P X t h
          (bankOTCDeficitSlopeAt P X t h (X.bankTightness t h))
          (bankOTCSurplusSlopeAt P X t h (X.bankTightness t h))
          (candidate.loans 0 (fun j => Fin.elim0 j) (fun j => Fin.elim0 j))
          (candidate.reserves 0 (fun j => Fin.elim0 j) (fun j => Fin.elim0 j))
          (candidate.deposits 0 (fun j => Fin.elim0 j) (fun j => Fin.elim0 j))
          V := by
  intro alternative hfeasible
  calc
    alternative.dividend 0 (fun j => Fin.elim0 j) (fun j => Fin.elim0 j) +
        bankBellmanContinuationAt P X t h
          (bankOTCDeficitSlopeAt P X t h (X.bankTightness t h))
          (bankOTCSurplusSlopeAt P X t h (X.bankTightness t h))
          (alternative.loans 0 (fun j => Fin.elim0 j) (fun j => Fin.elim0 j))
          (alternative.reserves 0 (fun j => Fin.elim0 j) (fun j => Fin.elim0 j))
          (alternative.deposits 0 (fun j => Fin.elim0 j) (fun j => Fin.elim0 j))
          V ≤ multiplier * equity :=
        source_bank_dividend_portfolio_upper_bound P X t h equity multiplier
          alternative V hfeasible hmultiplier
          (hglobalPortfolioBound alternative hfeasible)
    _ = candidate.dividend 0 (fun j => Fin.elim0 j) (fun j => Fin.elim0 j) +
        bankBellmanContinuationAt P X t h
          (bankOTCDeficitSlopeAt P X t h (X.bankTightness t h))
          (bankOTCSurplusSlopeAt P X t h (X.bankTightness t h))
          (candidate.loans 0 (fun j => Fin.elim0 j) (fun j => Fin.elim0 j))
          (candidate.reserves 0 (fun j => Fin.elim0 j) (fun j => Fin.elim0 j))
          (candidate.deposits 0 (fun j => Fin.elim0 j) (fun j => Fin.elim0 j))
          V := by rw [hzeroDividend, hattains]; ring

#print axioms dividend_retention_algebraic_upper_bound
#print axioms source_bank_dividend_portfolio_upper_bound
#print axioms source_bank_joint_dividend_portfolio_ranking

end ProposedBankDividendRetentionDominance
end Ventura26LiquidityAllocation
