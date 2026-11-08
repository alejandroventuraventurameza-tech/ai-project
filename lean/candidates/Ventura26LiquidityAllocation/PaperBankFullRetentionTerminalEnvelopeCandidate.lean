import Ventura26LiquidityAllocation.PaperBankConcreteFullRetentionOptimalityCandidate

/-!
# A SINGLE geometric survivor-equity envelope for a no-dividend bank

For a source bank continuation policy which distributes ZERO dividends
at EVERY supported history, its positive-date owner-payoff term is
proportional to its surviving-equity term:

  (1 - exit) * payoff(n+1) = exit * survivor(n+1).

Consequently, whenever exit < 1, summability of the survivor-value
series is sufficient for summability of the owner-payoff series, even
though the two economic objects are conceptually distinct. A SINGLE
geometric survivor-value envelope proves both objective well-definedness
and terminality for the exact SOURCE full-retention candidate.

This reduces one analytic premise. It DOES NOT prove a geometric
envelope for any particular equilibrium allocation or construct
a global BankOptimal equilibrium.
-/

namespace Ventura26LiquidityAllocation
namespace ProposedBankFullRetentionTerminalEnvelope

open ProposedBankConcreteFullRetentionOptimality
variable {S : Type*} [Fintype S] [DecidableEq S]

/-- Exact algebraic identity for every strictly positive relative
date, for ANY source bank policy with no dividends. It does not
require stochastic discount factors to be positive. -/
theorem zero_dividend_owner_payoff_eq_exit_survivor
    (P : Primitives S) (X : Allocation S) (t : ℕ) (h : History S t)
    (p : BankContinuationPolicy S P.paymentSupport)
    (hzero : ∀ n (future : Fin n → S)
      (payments : Fin n → P.paymentSupport),
        p.dividend n future payments = 0)
    (n : ℕ) :
    (1 - P.bankExit) *
        bankContinuationPayoffTermAt P X t h p (n + 1) =
      P.bankExit * bankSurvivingValueTermAt P X t h p (n + 1) := by
  classical
  unfold bankContinuationPayoffTermAt bankSurvivingValueTermAt
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro future _
  apply Finset.sum_congr rfl
  intro payments _
  simp [hzero (n + 1) future payments, pow_succ]
  ring

/-- For a zero-dividend policy and exit probability STRICTLY less
than one, summability of surviving equity implies summability of
the bank's full discounted owner-payoff objective. There is no
assumption of summability for alternative policies. -/
theorem zero_dividend_objective_summable_of_survivor_summable
    (P : Primitives S) (X : Allocation S) (t : ℕ) (h : History S t)
    (p : BankContinuationPolicy S P.paymentSupport)
    (hzero : ∀ n (future : Fin n → S)
      (payments : Fin n → P.paymentSupport),
        p.dividend n future payments = 0)
    (hexit : P.bankExit < 1)
    (hsurvivor : Summable (bankSurvivingValueTermAt P X t h p)) :
    BankContinuationObjectiveWellDefinedAt P X t h p := by
  have hsurviveTail :
      Summable (fun n : ℕ =>
        bankSurvivingValueTermAt P X t h p (n + 1)) :=
    (summable_nat_add_iff 1).mpr hsurvivor
  have hscaled :
      Summable (fun n : ℕ =>
        (1 - P.bankExit) *
          bankContinuationPayoffTermAt P X t h p (n + 1)) := by
    apply (hsurviveTail.mul_left P.bankExit).congr
    intro n
    exact (zero_dividend_owner_payoff_eq_exit_survivor
      P X t h p hzero n).symm
  have hgap : 1 - P.bankExit ≠ 0 :=
    (sub_pos.mpr hexit).ne'
  exact (summable_nat_add_iff 1).mp
    ((summable_mul_left_iff hgap).mp hscaled)

/-- The literal source full-retention plan pays zero dividends at
EVERY payment history, not only at the current aggregate history. -/
theorem source_full_retention_dividends_zero
    (P : Primitives S) (X : Allocation S) (t : ℕ) (h : History S t)
    (n : ℕ) (future : Fin n → S)
    (payments : Fin n → P.paymentSupport) :
    (sourceFullRetentionCandidate P X t h).dividend n future payments = 0 := by
  simp [sourceFullRetentionCandidate, bankContinuationPolicyFromPlan,
    fullRetentionCommonBankPlan]

/-- SINGLE weighted survivor-value envelope -> BOTH summability and
terminal condition for the source full-retention bank candidate.
The envelope itself is a substantive economic/numerical obligation.
The strict inequality exit < 1 is essential to this argument. -/
theorem source_full_retention_objective_and_terminal_of_surviving_envelope
    (P : Primitives S) (X : Allocation S) (t : ℕ) (h : History S t)
    (C alpha : ℝ)
    (hC : 0 ≤ C) (halpha0 : 0 ≤ alpha) (halpha1 : alpha < 1)
    (hexit : P.bankExit < 1)
    (hbound : ∀ T,
      |bankSurvivingValueTermAt P X t h
        (sourceFullRetentionCandidate P X t h) T| ≤ C * alpha ^ T) :
    BankContinuationObjectiveWellDefinedAt P X t h
      (sourceFullRetentionCandidate P X t h) ∧
    BankContinuationTerminalConditionAt P X t h
      (sourceFullRetentionCandidate P X t h) := by
  have henv := summable_tendsto_zero_of_abs_le_geometric
    (bankSurvivingValueTermAt P X t h
      (sourceFullRetentionCandidate P X t h))
    C alpha hC halpha0 halpha1 hbound
  exact ⟨zero_dividend_objective_summable_of_survivor_summable
      P X t h (sourceFullRetentionCandidate P X t h)
      (source_full_retention_dividends_zero P X t h) hexit henv.1,
    henv.2⟩

#print axioms zero_dividend_owner_payoff_eq_exit_survivor
#print axioms zero_dividend_objective_summable_of_survivor_summable
#print axioms source_full_retention_dividends_zero
#print axioms source_full_retention_objective_and_terminal_of_surviving_envelope

end ProposedBankFullRetentionTerminalEnvelope
end Ventura26LiquidityAllocation
