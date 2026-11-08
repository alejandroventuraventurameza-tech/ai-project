import Ventura26LiquidityAllocation.PaperBankLiteralBellmanMonotonicityCandidate

/-!
# SOURCE infinite payoff: a one-step upper envelope from tail bounds

This module uses the EXACT source theorem
`bankContinuationPayoffAt_first_step`. Under summable tails, source
consumption positivity, and an upper bound for the payoff of each
supported successor tail, it bounds an arbitrary continuation policy's
initial payoff by the one-step envelope evaluated at the SAME successor
equity/history. In particular, no future-path terminal condition is
imposed on alternative policies.

This is not a BankOptimal proof: the tail upper bound and compatibility
with a value super-solution remain obligations.
-/

namespace Ventura26LiquidityAllocation
namespace ProposedBankSourceOneStepEnvelope

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- One-step source envelope for an arbitrary bank continuation policy.
The source next-equity field is indexed by the aggregate successor and
payment realization, rather than by a fabricated macro transition. -/
noncomputable def bankTailEnvelopeAt
    (P : Primitives S) (X : Allocation S) (t : ℕ) (h : History S t)
    (q : BankContinuationPolicy S P.paymentSupport)
    (V : ℝ → History S (t + 1) → ℝ) : ℝ :=
  q.dividend 0 (fun j => Fin.elim0 j) (fun j => Fin.elim0 j) +
    ∑ s, ∑ ω : P.paymentSupport,
      P.tree.transition (currentState h) s * P.paymentProbability ω *
        bankStochasticDiscountAt P X t h s *
          ((1 - P.bankExit) *
              V (q.equity 1 (fun _ => s) (fun _ => ω))
                (childHistory h s) +
            P.bankExit * q.equity 1 (fun _ => s) (fun _ => ω))

/-- A policy's source infinite payoff is bounded by the envelope when
every supported successor's own infinite payoff is bounded by V.
The result still applies when zero-transition successors have no
consumption or tail summability assumption. -/
theorem bankContinuationPayoffAt_le_tailEnvelope
    (P : Primitives S) (X : Allocation S) (t : ℕ) (h : History S t)
    (q : BankContinuationPolicy S P.paymentSupport)
    (V : ℝ → History S (t + 1) → ℝ)
    (hcurrent : 0 < X.workerConsumption t h)
    (hchild : ∀ s, 0 < P.tree.transition (currentState h) s →
      0 < X.workerConsumption (t + 1) (childHistory h s))
    (htails : ∀ s, 0 < P.tree.transition (currentState h) s → ∀ ω,
      Summable (bankContinuationPayoffTermAt P X (t + 1)
        (childHistory h s) (tailBankContinuationPolicy q s ω)))
    (htailUpper : ∀ s, 0 < P.tree.transition (currentState h) s →
      ∀ ω : P.paymentSupport,
      bankContinuationPayoffAt P X (t + 1) (childHistory h s)
        (tailBankContinuationPolicy q s ω) ≤
          V (q.equity 1 (fun _ => s) (fun _ => ω))
            (childHistory h s)) :
    bankContinuationPayoffAt P X t h q ≤ bankTailEnvelopeAt P X t h q V := by
  rw [bankContinuationPayoffAt_first_step P X t h q hcurrent hchild htails]
  unfold bankTailEnvelopeAt
  apply add_le_add_left
  apply Finset.sum_le_sum
  intro s hs
  apply Finset.sum_le_sum
  intro ω hω
  by_cases hzero : P.tree.transition (currentState h) s = 0
  · simp [hzero]
  have hpos : 0 < P.tree.transition (currentState h) s :=
    lt_of_le_of_ne (P.tree.transition_nonneg _ _) (Ne.symm hzero)
  have hsdf : 0 < bankStochasticDiscountAt P X t h s :=
    bankStochasticDiscountAt_pos_of_consumption P X t h s
      hcurrent (hchild s hpos)
  have hweight :
      0 ≤ P.tree.transition (currentState h) s *
        P.paymentProbability ω * bankStochasticDiscountAt P X t h s := by
    exact mul_nonneg
      (mul_nonneg hpos.le (P.payment_probability_nonneg ω)) hsdf.le
  have hsurvival : 0 ≤ 1 - P.bankExit :=
    sub_nonneg.mpr P.bank_exit_mem.2
  have htail :
      (1 - P.bankExit) *
          bankContinuationPayoffAt P X (t + 1) (childHistory h s)
            (tailBankContinuationPolicy q s ω) ≤
      (1 - P.bankExit) *
          V (q.equity 1 (fun _ => s) (fun _ => ω))
            (childHistory h s) :=
    mul_le_mul_of_nonneg_left (htailUpper s hpos ω) hsurvival
  exact mul_le_mul_of_nonneg_left
    (add_le_add_right htail
      (P.bankExit * q.equity 1 (fun _ => s) (fun _ => ω)))
    hweight

#print axioms bankContinuationPayoffAt_le_tailEnvelope

end ProposedBankSourceOneStepEnvelope
end Ventura26LiquidityAllocation
