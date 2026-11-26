import Ventura26LiquidityAllocation.PaperBankKKTGlobalSufficiencyCandidate

/-!
# Full SOURCE static bank KKT normal-cone certificate

Add a fifth nonnegative multiplier for the reserve lower bound m>=0,
with complementarity reserveZeroDual*m*=0. This yields the additional
normal-cone term -reserveZeroDual*(m-m*)<=0 for every feasible deviation.

The five complementary duals and source OTC supergradients establish
GLOBAL expected-return dominance even if any of loans, reserves or
deposits is zero or if a bank loan/deposit cap binds. The source
robust-solvency constraints remain explicit in the feasibility set.

This is conditional static sufficiency, not infinite BankOptimal.
-/

namespace Ventura26LiquidityAllocation
namespace ProposedPaperBankKKTFullCorner

open ProposedPaperBankKKTGlobalSufficiency
variable {S : Type*} [Fintype S] [DecidableEq S]

theorem source_bank_static_optimal_with_all_bank_nonneg_corners
    (P : Primitives S) (X : Allocation S)
    (t : ℕ) (h : History S t)
    (deficitSlope surplusSlope retainedEquity : ℝ)
    (candidateLoans candidateReserves candidateDeposits : ℝ)
    (marginal : BankPayment → ℝ)
    (loanCapDual loanZeroDual reserveZeroDual depositCapDual depositZeroDual : ℝ)
    (hLoanCapDual : 0 ≤ loanCapDual)
    (hLoanZeroDual : 0 ≤ loanZeroDual)
    (hReserveZeroDual : 0 ≤ reserveZeroDual)
    (hDepositCapDual : 0 ≤ depositCapDual)
    (hDepositZeroDual : 0 ≤ depositZeroDual)
    (hLoanCapComplementarity :
      loanCapDual * (P.bankLoanCap * retainedEquity - candidateLoans) = 0)
    (hLoanZeroComplementarity : loanZeroDual * candidateLoans = 0)
    (hReserveZeroComplementarity : reserveZeroDual * candidateReserves = 0)
    (hDepositCapComplementarity :
      depositCapDual * (P.bankDepositCap * retainedEquity - candidateDeposits) = 0)
    (hDepositZeroComplementarity : depositZeroDual * candidateDeposits = 0)
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
        finiteSupportExpectation P.paymentSupport P.paymentProbability marginal +
        reserveZeroDual + (loanCapDual - loanZeroDual))
    (hpricingDeposits :
      X.depositRate t h = X.reserveRate t h +
        (1 - P.reserveRequirementPath t h) *
          finiteSupportExpectation P.paymentSupport P.paymentProbability marginal +
        (X.depositRate t h / X.reserveRate t h -
            P.reserveRequirementPath t h) *
          finiteSupportExpectation P.paymentSupport P.paymentProbability
            (fun ω => marginal ω * P.paymentShock ω) -
        (depositCapDual - depositZeroDual) + reserveZeroDual) :
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
  have hLoanPrice :
      rL = rR + muMean + reserveZeroDual + (loanCapDual - loanZeroDual) :=
    hpricingLoans
  have hDepositPrice :
      rD = rR + (1 - rho) * muMean + (xi - rho) * muShock -
        (depositCapDual - depositZeroDual) + reserveZeroDual :=
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
  obtain ⟨hLoanNonneg, _hReserveNonneg, hDepositNonneg,
    hAltBalance, hDepositCap, hLoanCap, _hRealSolvency⟩ := hfeasible
  have hLoanGlobalDirection :
      (loanCapDual - loanZeroDual) * (loans - candidateLoans) ≤ 0 := by
    exact bank_cap_corner_global_direction
      loans candidateLoans (P.bankLoanCap * retainedEquity)
      loanCapDual loanZeroDual
      hLoanCap hLoanNonneg hLoanCapDual hLoanZeroDual
      hLoanCapComplementarity hLoanZeroComplementarity
  have hReserveGlobalDirection :
      -reserveZeroDual * (reserves - candidateReserves) ≤ 0 := by
    calc
      -reserveZeroDual * (reserves - candidateReserves) =
          -(reserveZeroDual * reserves) +
            reserveZeroDual * candidateReserves := by ring
      _ = -(reserveZeroDual * reserves) := by
        rw [hReserveZeroComplementarity]
        ring
      _ ≤ 0 := neg_nonpos.mpr
        (mul_nonneg hReserveZeroDual _hReserveNonneg)
  have hDepositGlobalDirection :
      (depositCapDual - depositZeroDual) *
        (deposits - candidateDeposits) ≤ 0 := by
    exact bank_cap_corner_global_direction
      deposits candidateDeposits (P.bankDepositCap * retainedEquity)
      depositCapDual depositZeroDual
      hDepositCap hDepositNonneg hDepositCapDual hDepositZeroDual
      hDepositCapComplementarity hDepositZeroComplementarity
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
  have hPriceKKT :
      rL * (loans - candidateLoans) +
        rR * (reserves - candidateReserves) -
        rD * (deposits - candidateDeposits) +
        deltaBase * muMean + deltaShock * muShock =
        (loanCapDual - loanZeroDual) * (loans - candidateLoans) +
        (depositCapDual - depositZeroDual) * (deposits - candidateDeposits) -
        reserveZeroDual * (reserves - candidateReserves) := by
    rw [hLoanPrice, hDepositPrice]
    calc
      _ = (rR + muMean + reserveZeroDual) *
          ((loans - candidateLoans) + (reserves - candidateReserves) -
            (deposits - candidateDeposits)) +
          (loanCapDual - loanZeroDual) * (loans - candidateLoans) +
          (depositCapDual - depositZeroDual) *
            (deposits - candidateDeposits) -
          reserveZeroDual * (reserves - candidateReserves) := by
          dsimp [deltaBase, deltaShock]
          ring
      _ = _ := by rw [hBalanceDiff]; ring
  have hPriceBound :
      rL * (loans - candidateLoans) +
        rR * (reserves - candidateReserves) -
        rD * (deposits - candidateDeposits) +
        deltaBase * muMean + deltaShock * muShock ≤ 0 := by
    rw [hPriceKKT]
    linarith [hLoanGlobalDirection, hDepositGlobalDirection,
      hReserveGlobalDirection]
  rw [hPayoff, hPayoff]
  linarith [hLiquidityBound, hPriceBound]


#print axioms source_bank_static_optimal_with_all_bank_nonneg_corners

end ProposedPaperBankKKTFullCorner
end Ventura26LiquidityAllocation
