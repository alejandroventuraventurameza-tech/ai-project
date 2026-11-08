import Ventura26LiquidityAllocation.PaperBankFullRetentionTerminalEnvelopeCandidate

/-!
# A contractive surviving-equity process gives the SOURCE bank TVC

This separates the real economic burden from the analytic one:
the model must establish a nonnegative one-step contraction
of the discounted, survival-weighted source bank-equity process.
Once that is available, the geometric envelope, payoff summability
and the terminal condition follow by induction and SOURCE lemmas.

DO NOT interpret contraction as proved for any calibrated economy:
the one-step inequality remains an explicit input, to be linked
to bank settlement returns, household SDF, Markov transitions and
survival probabilities in the next proof gate.
-/

namespace Ventura26LiquidityAllocation
namespace ProposedBankSurvivingContraction

open ProposedBankFullRetentionTerminalEnvelope

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- No bank-specific content: a nonnegative subgeometric recursion
generates an absolute geometric envelope. -/
theorem nonnegative_contraction_gives_geometric_bound
    (u : ℕ → ℝ) (C rho : ℝ)
    (hC : 0 ≤ C)
    (hrho0 : 0 ≤ rho) (hrho1 : rho < 1)
    (hu : ∀ n, 0 ≤ u n)
    (hbase : u 0 ≤ C)
    (hstep : ∀ n, u (n + 1) ≤ rho * u n) :
    ∀ n, |u n| ≤ C * rho ^ n := by
  have hbound : ∀ n, u n ≤ C * rho ^ n := by
    intro n
    induction n with
    | zero =>
      simpa only [pow_zero, mul_one] using hbase
    | succ n ih =>
      calc
        u (n + 1) ≤ rho * u n := hstep n
        _ ≤ rho * (C * rho ^ n) :=
          mul_le_mul_of_nonneg_left ih hrho0
        _ = C * rho ^ (n + 1) := by rw [pow_succ]; ring
  intro n
  simpa only [abs_of_nonneg (hu n)] using hbound n

/-- The single-step surviving-equity contraction directly discharges
the TWO analytic conditions required by the source dynamic bank
optimality predicate, for the concrete full-retention candidate.

The first-step contraction and pointwise nonnegativity are economic
hypotheses, not consequences of an arbitrary numerical picture. -/
theorem full_retention_analytic_conditions_of_survivor_contraction
    (P : Primitives S) (X : Allocation S)
    (t : ℕ) (h : History S t)
    (C rho : ℝ)
    (hC : 0 ≤ C)
    (hrho0 : 0 ≤ rho) (hrho1 : rho < 1)
    (hexit : P.bankExit < 1)
    (hnonneg : ∀ n,
      0 ≤ bankSurvivingValueTermAt P X t h
        (ProposedBankConcreteFullRetentionOptimality.sourceFullRetentionCandidate
          P X t h) n)
    (hbase : bankSurvivingValueTermAt P X t h
        (ProposedBankConcreteFullRetentionOptimality.sourceFullRetentionCandidate
          P X t h) 0 ≤ C)
    (hcontract : ∀ n,
      bankSurvivingValueTermAt P X t h
        (ProposedBankConcreteFullRetentionOptimality.sourceFullRetentionCandidate
          P X t h) (n + 1) ≤
      rho * bankSurvivingValueTermAt P X t h
        (ProposedBankConcreteFullRetentionOptimality.sourceFullRetentionCandidate
          P X t h) n) :
    BankContinuationObjectiveWellDefinedAt P X t h
      (ProposedBankConcreteFullRetentionOptimality.sourceFullRetentionCandidate
        P X t h) ∧
    BankContinuationTerminalConditionAt P X t h
      (ProposedBankConcreteFullRetentionOptimality.sourceFullRetentionCandidate
        P X t h) := by
  have hbound :=
    nonnegative_contraction_gives_geometric_bound
      (bankSurvivingValueTermAt P X t h
        (ProposedBankConcreteFullRetentionOptimality.sourceFullRetentionCandidate
          P X t h))
      C rho hC hrho0 hrho1 hnonneg hbase hcontract
  exact source_full_retention_objective_and_terminal_of_surviving_envelope
    P X t h C rho hC hrho0 hrho1 hexit hbound

/-- The economically more interpretable contraction factor is
survival probability times a bounded discounted equity-return
multiplier g. The hypothesis itself is still a one-step inequality;
identifying g from the source OTC and SDF laws is a separate task. -/
theorem full_retention_analytic_conditions_of_survival_return_bound
    (P : Primitives S) (X : Allocation S)
    (t : ℕ) (h : History S t)
    (C grossDiscountedReturn : ℝ)
    (hC : 0 ≤ C)
    (hgross : 0 ≤ grossDiscountedReturn)
    (hsurvive : 0 ≤ 1 - P.bankExit)
    (hcontraction :
      (1 - P.bankExit) * grossDiscountedReturn < 1)
    (hexit : P.bankExit < 1)
    (hnonneg : ∀ n,
      0 ≤ bankSurvivingValueTermAt P X t h
        (ProposedBankConcreteFullRetentionOptimality.sourceFullRetentionCandidate
          P X t h) n)
    (hbase : bankSurvivingValueTermAt P X t h
        (ProposedBankConcreteFullRetentionOptimality.sourceFullRetentionCandidate
          P X t h) 0 ≤ C)
    (hreturnBound : ∀ n,
      bankSurvivingValueTermAt P X t h
        (ProposedBankConcreteFullRetentionOptimality.sourceFullRetentionCandidate
          P X t h) (n + 1) ≤
      ((1 - P.bankExit) * grossDiscountedReturn) *
        bankSurvivingValueTermAt P X t h
          (ProposedBankConcreteFullRetentionOptimality.sourceFullRetentionCandidate
            P X t h) n) :
    BankContinuationObjectiveWellDefinedAt P X t h
      (ProposedBankConcreteFullRetentionOptimality.sourceFullRetentionCandidate
        P X t h) ∧
    BankContinuationTerminalConditionAt P X t h
      (ProposedBankConcreteFullRetentionOptimality.sourceFullRetentionCandidate
        P X t h) := by
  exact full_retention_analytic_conditions_of_survivor_contraction
    P X t h C ((1 - P.bankExit) * grossDiscountedReturn)
    hC (mul_nonneg hsurvive hgross) hcontraction
    hexit hnonneg hbase hreturnBound

#print axioms nonnegative_contraction_gives_geometric_bound
#print axioms full_retention_analytic_conditions_of_survivor_contraction
#print axioms full_retention_analytic_conditions_of_survival_return_bound

end ProposedBankSurvivingContraction
end Ventura26LiquidityAllocation
