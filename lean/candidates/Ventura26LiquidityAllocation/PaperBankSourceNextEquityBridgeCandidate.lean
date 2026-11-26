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


/-- For a SOURCE-feasible continuation policy, its first-step envelope
is exactly the literal source Bellman expression evaluated at that
policy's date-zero controls. This is an IDENTITY, not optimality. -/
theorem bankTailEnvelopeAt_eq_dividend_add_sourceBellman
    (P : Primitives S) (X : Allocation S)
    (t : ℕ) (h : History S t)
    (initialEquity : ℝ)
    (q : BankContinuationPolicy S P.paymentSupport)
    (hfeasible : BankContinuationFeasibleAt P X t h initialEquity q)
    (V : ℝ → History S (t + 1) → ℝ) :
    ProposedBankSourceOneStepEnvelope.bankTailEnvelopeAt P X t h q V =
      q.dividend 0 (fun j => Fin.elim0 j) (fun j => Fin.elim0 j) +
      bankBellmanContinuationAt P X t h
        (bankOTCDeficitSlopeAt P X t h (X.bankTightness t h))
        (bankOTCSurplusSlopeAt P X t h (X.bankTightness t h))
        (q.loans 0 (fun j => Fin.elim0 j) (fun j => Fin.elim0 j))
        (q.reserves 0 (fun j => Fin.elim0 j) (fun j => Fin.elim0 j))
        (q.deposits 0 (fun j => Fin.elim0 j) (fun j => Fin.elim0 j))
        V := by
  let emptyS : Fin 0 → S := fun j => Fin.elim0 j
  let emptyOmega : Fin 0 → P.paymentSupport := fun j => Fin.elim0 j
  unfold ProposedBankSourceOneStepEnvelope.bankTailEnvelopeAt
  apply congrArg (fun z =>
    q.dividend 0 (fun j => Fin.elim0 j) (fun j => Fin.elim0 j) + z)
  unfold bankBellmanContinuationAt
  rw [Finset.sum_subtype P.paymentSupport (fun x => Iff.rfl)]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro omega _hOmega
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro state _hState
  by_cases hzero : P.tree.transition (currentState h) state = 0
  · simp [hzero]
  have hpos : 0 < P.tree.transition (currentState h) state :=
    lt_of_le_of_ne (P.tree.transition_nonneg _ _) (Ne.symm hzero)
  have hposAtZero :
      0 < P.tree.transition
        (currentState (continuationHistory h emptyS)) state := by
    simpa [emptyS, continuationHistory_zero] using hpos
  have hnext :=
    bankContinuationFeasibleAt_nextEquity_eq_realPortfolioReturn
      P X t h initialEquity q hfeasible
        0 emptyS emptyOmega (by trivial) omega state hposAtZero
  have hchildFuture :
      childFutureHistory emptyS state = (fun _ => state) := by
    funext j
    exact Fin.eq_zero j ▸ rfl
  have hchildPayment :
      childPaymentHistory emptyOmega omega = (fun _ => omega) := by
    funext j
    exact Fin.eq_zero j ▸ rfl
  rw [hchildFuture, hchildPayment] at hnext
  have hequity :
      q.equity 1 (fun _ => state) (fun _ => omega) =
        bankRealPortfolioReturnAt P X t h
          (bankOTCDeficitSlopeAt P X t h (X.bankTightness t h))
          (bankOTCSurplusSlopeAt P X t h (X.bankTightness t h))
          (q.loans 0 emptyS emptyOmega)
          (q.reserves 0 emptyS emptyOmega)
          (q.deposits 0 emptyS emptyOmega) omega state := by
    simpa [emptyS, emptyOmega, continuationHistory_zero] using hnext
  rw [hequity]
  ring

/-- Conditional one-step comparison for EVERY feasible alternative.
Tail payoffs must already be bounded by the chosen V; this conclusion
does not assume that all such bounds hold globally at every history. -/
theorem bankContinuationPayoffAt_le_sourceBellman_of_tailBound
    (P : Primitives S) (X : Allocation S)
    (t : ℕ) (h : History S t)
    (initialEquity : ℝ)
    (q : BankContinuationPolicy S P.paymentSupport)
    (hfeasible : BankContinuationFeasibleAt P X t h initialEquity q)
    (V : ℝ → History S (t + 1) → ℝ)
    (hcurrent : 0 < X.workerConsumption t h)
    (hchild : ∀ s, 0 < P.tree.transition (currentState h) s →
      0 < X.workerConsumption (t + 1) (childHistory h s))
    (htails : ∀ s, 0 < P.tree.transition (currentState h) s → ∀ omega,
      Summable (bankContinuationPayoffTermAt P X (t + 1)
        (childHistory h s) (tailBankContinuationPolicy q s omega)))
    (htailUpper : ∀ s, 0 < P.tree.transition (currentState h) s →
      ∀ omega : P.paymentSupport,
      bankContinuationPayoffAt P X (t + 1) (childHistory h s)
        (tailBankContinuationPolicy q s omega) ≤
          V (q.equity 1 (fun _ => s) (fun _ => omega))
            (childHistory h s)) :
    bankContinuationPayoffAt P X t h q ≤
      q.dividend 0 (fun j => Fin.elim0 j) (fun j => Fin.elim0 j) +
      bankBellmanContinuationAt P X t h
        (bankOTCDeficitSlopeAt P X t h (X.bankTightness t h))
        (bankOTCSurplusSlopeAt P X t h (X.bankTightness t h))
        (q.loans 0 (fun j => Fin.elim0 j) (fun j => Fin.elim0 j))
        (q.reserves 0 (fun j => Fin.elim0 j) (fun j => Fin.elim0 j))
        (q.deposits 0 (fun j => Fin.elim0 j) (fun j => Fin.elim0 j))
        V := by
  calc
    bankContinuationPayoffAt P X t h q ≤
        ProposedBankSourceOneStepEnvelope.bankTailEnvelopeAt P X t h q V :=
      ProposedBankSourceOneStepEnvelope.bankContinuationPayoffAt_le_tailEnvelope
        P X t h q V hcurrent hchild htails htailUpper
    _ = _ :=
      bankTailEnvelopeAt_eq_dividend_add_sourceBellman
        P X t h initialEquity q hfeasible V


/-- Every dynamically feasible alternative also has a literally
feasible date-zero static portfolio at ITS OWN retained equity.
Unlike the source theorem for a named BankPlan candidate, this
quantifies over an arbitrary continuation policy. In particular,
this does NOT establish optimality across dividend choices. -/
theorem bankContinuationFeasibleAt_initialStaticPortfolio
    (P : Primitives S) (X : Allocation S)
    (t : ℕ) (h : History S t)
    (initialEquity : ℝ)
    (q : BankContinuationPolicy S P.paymentSupport)
    (hfeasible : BankContinuationFeasibleAt P X t h initialEquity q) :
    BankStaticPortfolioFeasibleAt P X t h
      (bankOTCDeficitSlopeAt P X t h (X.bankTightness t h))
      (bankOTCSurplusSlopeAt P X t h (X.bankTightness t h))
      (q.retainedEquity 0 (fun j => Fin.elim0 j) (fun j => Fin.elim0 j))
      (q.loans 0 (fun j => Fin.elim0 j) (fun j => Fin.elim0 j))
      (q.reserves 0 (fun j => Fin.elim0 j) (fun j => Fin.elim0 j))
      (q.deposits 0 (fun j => Fin.elim0 j) (fun j => Fin.elim0 j)) := by
  let emptyS : Fin 0 → S := fun j => Fin.elim0 j
  let emptyOmega : Fin 0 → P.paymentSupport := fun j => Fin.elim0 j
  have hzero := hfeasible.2 0 emptyS emptyOmega (by trivial)
  rcases hzero with ⟨equityNonneg, dividendNonneg, hretainedNonneg,
    hloansNonneg, hreservesNonneg, hdepositsNonneg, zeroBoundary,
    retainedPos, retention, hbalance, hdepositCap, hloanCap,
    hreserveRate, hsettlement⟩
  have hreserveRate' : 0 < X.reserveRate t h := by
    simpa [emptyS, continuationHistory_zero] using hreserveRate
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [emptyS, emptyOmega] using hloansNonneg
  · simpa [emptyS, emptyOmega] using hreservesNonneg
  · simpa [emptyS, emptyOmega] using hdepositsNonneg
  · simpa [emptyS, emptyOmega] using hbalance
  · simpa [emptyS, emptyOmega] using hdepositCap
  · simpa [emptyS, emptyOmega] using hloanCap
  · intro omega hOmega state hs
    change 0 ≤ bankReducedPortfolioReturn P X t h
      (bankOTCDeficitSlopeAt P X t h (X.bankTightness t h))
      (bankOTCSurplusSlopeAt P X t h (X.bankTightness t h))
      (q.loans 0 emptyS emptyOmega)
      (q.reserves 0 emptyS emptyOmega)
      (q.deposits 0 emptyS emptyOmega)
      omega / X.inflation (t + 1) (childHistory h state)
    let omegaS : P.paymentSupport := ⟨omega, hOmega⟩
    have htransition := (hsettlement omegaS).2.2 state hs
    have hsupported : FuturePathSupported P.tree (currentState h) 1
        (fun _ => state) := by
      simpa [FuturePathSupported] using hs
    have hone := hfeasible.2 1 (fun _ => state)
      (fun _ => omegaS) hsupported
    have hEquityNonneg : 0 ≤ q.equity 1
        (fun _ => state) (fun _ => omegaS) := hone.1
    have hchildFuture : childFutureHistory emptyS state =
        (fun _ => state) := by
      funext j
      exact Fin.eq_zero j ▸ rfl
    have hchildPayment : childPaymentHistory emptyOmega omegaS =
        (fun _ => omegaS) := by
      funext j
      exact Fin.eq_zero j ▸ rfl
    rw [hchildFuture, hchildPayment] at htransition
    rw [htransition] at hEquityNonneg
    rw [← bankDetailedPortfolioReturn_eq_reduced P X t h
      (X.bankTightness t h)
      (q.loans 0 emptyS emptyOmega)
      (q.reserves 0 emptyS emptyOmega)
      (q.deposits 0 emptyS emptyOmega)
      omega hreserveRate'.ne']
    simpa [emptyS, emptyOmega, continuationHistory_zero]
      using hEquityNonneg

#print axioms bankContinuationFeasibleAt_initialStaticPortfolio

#print axioms bankTailEnvelopeAt_eq_dividend_add_sourceBellman
#print axioms bankContinuationPayoffAt_le_sourceBellman_of_tailBound

#print axioms bankContinuationFeasibleAt_nextEquity_eq_realPortfolioReturn

end ProposedBankSourceNextEquityBridge
end Ventura26LiquidityAllocation
