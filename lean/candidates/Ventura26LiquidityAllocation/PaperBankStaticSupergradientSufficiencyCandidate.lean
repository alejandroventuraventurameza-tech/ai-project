import Ventura26LiquidityAllocation.MainTheorems

/-!
# Conditional global sufficiency of the literal one-history bank portfolio

This module does NOT assume that an Euler/KKT equation itself establishes
the source bank's dynamic optimum. It proves a substantive, one-history
global portfolio comparison for ANY admissible competing portfolio, using:

1. The source bankReducedPortfolioReturnWithShock and bankSettlementSurplus
   (including the payment-dependent coefficient);
2. A valid supporting supergradient of the source piecewise OTC payoff
   at candidate settlement for EVERY supported idiosyncratic payment;
3. Source-conformable loan/deposit pricing equalities using the finite
   probability-weighted mean and shock covariance of those slopes;
4. The SAME bank retained-equity balance for candidate and alternative.

The proof includes zero-surplus atoms if their supergradient is provided.
It does not assume a strict payment regime, no alternative sign changes,
or that the bank's actual infinite-horizon continuation is optimal.

This is a conditional SUFFICIENCY theorem for the source
BankStaticPortfolioOptimalAt, not an existence/selection theorem for
macroeconomic equilibria.
-/

namespace Ventura26LiquidityAllocation
namespace ProposedPaperBankStaticSupergradientSufficiency

variable {S : Type*} [Fintype S] [DecidableEq S]

theorem source_bank_static_portfolio_optimal_of_supergradients
    (P : Primitives S) (X : Allocation S)
    (t : ℕ) (h : History S t)
    (deficitSlope surplusSlope retainedEquity : ℝ)
    (candidateLoans candidateReserves candidateDeposits : ℝ)
    (marginal : BankPayment → ℝ)
    (hcandidate : BankStaticPortfolioFeasibleAt P X t h
      deficitSlope surplusSlope retainedEquity
      candidateLoans candidateReserves candidateDeposits)
    (hgradient : ∀ ω ∈ P.paymentSupport,
      IsOTCLiquiditySupergradient deficitSlope surplusSlope
        (bankSettlementSurplus candidateReserves
          (P.reserveRequirementPath t h)
          (X.depositRate t h / X.reserveRate t h)
          candidateDeposits (P.paymentShock ω))
        (marginal ω))
    (hpricingLoans :
      X.loanRate t h = X.reserveRate t h +
        finiteSupportExpectation P.paymentSupport P.paymentProbability marginal)
    (hpricingDeposits :
      X.depositRate t h = X.reserveRate t h +
        (1 - P.reserveRequirementPath t h) *
          finiteSupportExpectation P.paymentSupport P.paymentProbability marginal +
        (X.depositRate t h / X.reserveRate t h -
            P.reserveRequirementPath t h) *
          finiteSupportExpectation P.paymentSupport P.paymentProbability
            (fun ω => marginal ω * P.paymentShock ω)) :
    BankStaticPortfolioOptimalAt P X t h deficitSlope surplusSlope
      retainedEquity candidateLoans candidateReserves candidateDeposits := by
  let rL : ℝ := X.loanRate t h
  let rR : ℝ := X.reserveRate t h
  let rD : ℝ := X.depositRate t h
  let rho : ℝ := P.reserveRequirementPath t h
  let xi : ℝ := rD / rR
  let muMean : ℝ :=
    finiteSupportExpectation P.paymentSupport P.paymentProbability marginal
  let muShock : ℝ :=
    finiteSupportExpectation P.paymentSupport P.paymentProbability
      (fun ω => marginal ω * P.paymentShock ω)
  let s : ℝ → ℝ → BankPayment → ℝ := fun reserves deposits ω =>
    bankSettlementSurplus reserves rho xi deposits (P.paymentShock ω)
  let payoffLiquidity : ℝ → ℝ → ℝ := fun reserves deposits =>
    finiteSupportExpectation P.paymentSupport P.paymentProbability
      (fun ω => otcLiquidityPayoff deficitSlope surplusSlope (s reserves deposits ω))
  have hLoanPrice : rL = rR + muMean := hpricingLoans
  have hDepositPrice :
      rD = rR + (1 - rho) * muMean + (xi - rho) * muShock :=
    hpricingDeposits
  have hPayoff (loans reserves deposits : ℝ) :
      bankStaticPortfolioPayoffAt P X t h deficitSlope surplusSlope
        loans reserves deposits =
        (rL * loans + rR * reserves - rD * deposits) +
          payoffLiquidity reserves deposits := by
    change
      finiteSupportExpectation P.paymentSupport P.paymentProbability
        (fun ω => (rL * loans + rR * reserves - rD * deposits) +
          otcLiquidityPayoff deficitSlope surplusSlope (s reserves deposits ω)) =
        (rL * loans + rR * reserves - rD * deposits) +
          payoffLiquidity reserves deposits
    rw [finiteSupportExpectation_add]
    rw [finiteSupportExpectation_const _ _ P.payment_probability_sum_one]
  have hCandBalance :
      candidateLoans + candidateReserves =
        candidateDeposits + retainedEquity := by
    rcases hcandidate with ⟨_, _, _, hb, _, _, _⟩
    exact hb
  intro loans reserves deposits hfeasible
  have hAltBalance : loans + reserves = deposits + retainedEquity := by
    rcases hfeasible with ⟨_, _, _, hb, _, _, _⟩
    exact hb
  let deltaBase : ℝ :=
    (reserves - candidateReserves) -
      rho * (deposits - candidateDeposits)
  let deltaShock : ℝ :=
    (xi - rho) * (deposits - candidateDeposits)
  have hDelta (ω : BankPayment) :
      s reserves deposits ω - s candidateReserves candidateDeposits ω =
        deltaBase + deltaShock * P.paymentShock ω := by
    dsimp [s, deltaBase, deltaShock, bankSettlementSurplus]
    ring
  have hPoint (ω : BankPayment) (hω : ω ∈ P.paymentSupport) :
      otcLiquidityPayoff deficitSlope surplusSlope (s reserves deposits ω) ≤
        otcLiquidityPayoff deficitSlope surplusSlope
          (s candidateReserves candidateDeposits ω) +
        marginal ω *
          (s reserves deposits ω -
            s candidateReserves candidateDeposits ω) :=
    hgradient ω hω (s reserves deposits ω)
  have hExpectedUpper :
      payoffLiquidity reserves deposits ≤
        finiteSupportExpectation P.paymentSupport P.paymentProbability
          (fun ω =>
            otcLiquidityPayoff deficitSlope surplusSlope
              (s candidateReserves candidateDeposits ω) +
            marginal ω *
              (s reserves deposits ω -
                s candidateReserves candidateDeposits ω)) := by
    dsimp [payoffLiquidity, finiteSupportExpectation]
    apply Finset.sum_le_sum
    intro ω hω
    exact mul_le_mul_of_nonneg_left
      (hPoint ω hω) (P.payment_probability_pos_on_support ω hω).le
  have hDeltaExpected :
      finiteSupportExpectation P.paymentSupport P.paymentProbability
        (fun ω =>
          marginal ω * (s reserves deposits ω -
            s candidateReserves candidateDeposits ω)) =
        deltaBase * muMean + deltaShock * muShock := by
    have hpointeq :
        (fun ω =>
          marginal ω * (s reserves deposits ω -
            s candidateReserves candidateDeposits ω)) =
        (fun ω => deltaBase * marginal ω +
          deltaShock * (marginal ω * P.paymentShock ω)) := by
      funext ω
      rw [hDelta ω]
      ring
    rw [hpointeq, finiteSupportExpectation_add,
      finiteSupportExpectation_const_mul, finiteSupportExpectation_const_mul]
  have hLiquidityBound :
      payoffLiquidity reserves deposits ≤
        payoffLiquidity candidateReserves candidateDeposits +
          deltaBase * muMean + deltaShock * muShock := by
    have hRight :
        finiteSupportExpectation P.paymentSupport P.paymentProbability
          (fun ω =>
            otcLiquidityPayoff deficitSlope surplusSlope
              (s candidateReserves candidateDeposits ω) +
            marginal ω *
              (s reserves deposits ω -
                s candidateReserves candidateDeposits ω)) =
        payoffLiquidity candidateReserves candidateDeposits +
          (deltaBase * muMean + deltaShock * muShock) := by
      rw [finiteSupportExpectation_add, hDeltaExpected]
    rw [hRight] at hExpectedUpper
    linarith
  have hBalanceDiff :
      (loans - candidateLoans) + (reserves - candidateReserves) -
        (deposits - candidateDeposits) = 0 := by
    linarith [hAltBalance, hCandBalance]
  have hPriceCollapse :
      rL * (loans - candidateLoans) +
        rR * (reserves - candidateReserves) -
        rD * (deposits - candidateDeposits) +
        deltaBase * muMean + deltaShock * muShock = 0 := by
    rw [hLoanPrice, hDepositPrice]
    calc
      _ = (rR + muMean) *
          ((loans - candidateLoans) + (reserves - candidateReserves) -
            (deposits - candidateDeposits)) := by
          dsimp [deltaBase, deltaShock]
          ring
      _ = 0 := by rw [hBalanceDiff]; ring
  rw [hPayoff, hPayoff]
  linarith [hLiquidityBound, hPriceCollapse]


/-- A concrete source-level implementation of the marginal selector at each
supported payment atom. The weak ordering of liquidity slopes and ANY
admissible kink slope imply the needed supergradient at the candidate,
even if some settlements are exactly zero. Thus the gradient condition
in the previous theorem is CONSTRUCTED, not assumed for this corollary.
The two endogenous price identities and candidate feasibility remain
explicitly necessary premises; caps and Bellman remain outside scope. -/
theorem source_bank_static_portfolio_optimal_of_selected_marginal
    (P : Primitives S) (X : Allocation S)
    (t : ℕ) (h : History S t)
    (deficitSlope surplusSlope retainedEquity kinkSlope : ℝ)
    (candidateLoans candidateReserves candidateDeposits : ℝ)
    (horder : surplusSlope ≤ deficitSlope)
    (hkinkLower : surplusSlope ≤ kinkSlope)
    (hkinkUpper : kinkSlope ≤ deficitSlope)
    (hcandidate : BankStaticPortfolioFeasibleAt P X t h
      deficitSlope surplusSlope retainedEquity
      candidateLoans candidateReserves candidateDeposits)
    (hpricingLoans :
      X.loanRate t h = X.reserveRate t h +
        finiteSupportExpectation P.paymentSupport P.paymentProbability
          (fun ω => selectedOTCLiquidityMarginal deficitSlope surplusSlope kinkSlope
            (bankSettlementSurplus candidateReserves
              (P.reserveRequirementPath t h)
              (X.depositRate t h / X.reserveRate t h)
              candidateDeposits (P.paymentShock ω))))
    (hpricingDeposits :
      X.depositRate t h = X.reserveRate t h +
        (1 - P.reserveRequirementPath t h) *
          finiteSupportExpectation P.paymentSupport P.paymentProbability
            (fun ω => selectedOTCLiquidityMarginal deficitSlope surplusSlope kinkSlope
              (bankSettlementSurplus candidateReserves
                (P.reserveRequirementPath t h)
                (X.depositRate t h / X.reserveRate t h)
                candidateDeposits (P.paymentShock ω))) +
        (X.depositRate t h / X.reserveRate t h -
            P.reserveRequirementPath t h) *
          finiteSupportExpectation P.paymentSupport P.paymentProbability
            (fun ω =>
              selectedOTCLiquidityMarginal deficitSlope surplusSlope kinkSlope
                (bankSettlementSurplus candidateReserves
                  (P.reserveRequirementPath t h)
                  (X.depositRate t h / X.reserveRate t h)
                  candidateDeposits (P.paymentShock ω)) * P.paymentShock ω)) :
    BankStaticPortfolioOptimalAt P X t h deficitSlope surplusSlope
      retainedEquity candidateLoans candidateReserves candidateDeposits := by
  refine source_bank_static_portfolio_optimal_of_supergradients
    P X t h deficitSlope surplusSlope retainedEquity
    candidateLoans candidateReserves candidateDeposits
    (fun ω => selectedOTCLiquidityMarginal deficitSlope surplusSlope kinkSlope
      (bankSettlementSurplus candidateReserves
        (P.reserveRequirementPath t h)
        (X.depositRate t h / X.reserveRate t h)
        candidateDeposits (P.paymentShock ω)))
    hcandidate ?_ hpricingLoans hpricingDeposits
  intro ω hω
  exact selectedOTCLiquidityMarginal_isSupergradient
    horder hkinkLower hkinkUpper

#print axioms source_bank_static_portfolio_optimal_of_selected_marginal

#print axioms source_bank_static_portfolio_optimal_of_supergradients

end ProposedPaperBankStaticSupergradientSufficiency
end Ventura26LiquidityAllocation
