import Ventura26LiquidityAllocation.PaperBankSourceOneStepEnvelopeCandidate

/-!
# Literal bank successor-equity bridge for every feasible continuation policy

The SOURCE feasibility predicate uses the detailed OTC/facility settlement
return, while bankBellmanContinuationAt uses bankRealPortfolioReturnAt
(the reduced OTC payoff divided by successor inflation).

For a source-feasible policy, a supported history and successor payment/state,
the two generate EXACTLY the same next equity. The reserve rate is positive
as part of source feasibility; it is NOT introduced as an extra assumption.

This theorem is a transition-identity only; it is neither a Bellman
super-solution nor a BankContinuationOptimalAt proof.
-/

namespace Ventura26LiquidityAllocation
namespace ProposedBankSourceNextEquityBridge

variable {S : Type*} [Fintype S] [DecidableEq S]

theorem bankContinuationFeasibleAt_nextEquity_eq_realPortfolioReturn
    (P : Primitives S) (X : Allocation S)
    (t : ℕ) (h : History S t)
    (initialEquity : ℝ)
    (q : BankContinuationPolicy S P.paymentSupport)
    (hfeasible : BankContinuationFeasibleAt P X t h initialEquity q)
    (n : ℕ) (future : Fin n → S)
    (payments : Fin n → P.paymentSupport)
    (hfuture : FuturePathSupported P.tree (currentState h) n future)
    (ω : P.paymentSupport)
    (s : S)
    (hs : 0 < P.tree.transition (currentState (continuationHistory h future)) s) :
    q.equity (n + 1) (childFutureHistory future s)
        (childPaymentHistory payments ω) =
      bankRealPortfolioReturnAt P X (t + n) (continuationHistory h future)
        (bankOTCDeficitSlopeAt P X (t + n) (continuationHistory h future)
          (X.bankTightness (t + n) (continuationHistory h future)))
        (bankOTCSurplusSlopeAt P X (t + n) (continuationHistory h future)
          (X.bankTightness (t + n) (continuationHistory h future)))
        (q.loans n future payments)
        (q.reserves n future payments)
        (q.deposits n future payments)
        ω s := by
  obtain ⟨_, hpath⟩ := hfeasible
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, hreserveRate, hsettlement⟩ :=
    hpath n future payments hfuture
  have hreserveNonzero :
      X.reserveRate (t + n) (continuationHistory h future) ≠ 0 :=
    ne_of_gt hreserveRate
  have hsource := (hsettlement ω).2.2 s hs
  rw [bankDetailedPortfolioReturn_eq_reduced
      P X (t + n) (continuationHistory h future)
      (X.bankTightness (t + n) (continuationHistory h future))
      (q.loans n future payments)
      (q.reserves n future payments)
      (q.deposits n future payments)
      (ω : BankPayment) hreserveNonzero] at hsource
  simpa only [bankRealPortfolioReturnAt] using hsource

#print axioms bankContinuationFeasibleAt_nextEquity_eq_realPortfolioReturn

end ProposedBankSourceNextEquityBridge
end Ventura26LiquidityAllocation
