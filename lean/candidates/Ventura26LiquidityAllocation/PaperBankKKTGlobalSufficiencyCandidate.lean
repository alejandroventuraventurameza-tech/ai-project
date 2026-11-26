import Ventura26LiquidityAllocation.PaperBankStaticSupergradientSufficiencyCandidate

/-!
# Sufficient KKT certificate for the SOURCE individual-bank static portfolio

The earlier no-cap theorem requires exactly interior loan/deposit pricing.
This theorem preserves the exact SOURCE settlement and expected payoff,
but admits loan/deposit zero corners and binding bank leverage caps.

A candidate's four nonnegative duals satisfy complementary slackness.
For EVERY SOURCE-feasible alternative with identical retained equity,
the concave OTC supporting inequality plus the KKT equalities yields
expected-return dominance. No sign regime is imposed on deviations.

This theorem does NOT assume the dominance conclusion, an infinite-horizon
bank value, an endogenous branch selector, or a bank policy shock effect.
-/

namespace Ventura26LiquidityAllocation
namespace ProposedPaperBankKKTGlobalSufficiency

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- A supporting normal-cone multiplier inequality on [0, cap].
The cap may bind, x* may equal zero, or both duals may vanish. -/
theorem bank_cap_corner_global_direction
    (x candidate cap capDual zeroDual : ℝ)
    (hupper : x ≤ cap) (hlower : 0 ≤ x)
    (hcapDual : 0 ≤ capDual) (hzeroDual : 0 ≤ zeroDual)
    (hcapComplement : capDual * (cap - candidate) = 0)
    (hzeroComplement : zeroDual * candidate = 0) :
    (capDual - zeroDual) * (x - candidate) ≤ 0 := by
  have hcap : capDual * (x - candidate) ≤ 0 := by
    calc
      capDual * (x - candidate) =
          capDual * (x - cap) + capDual * (cap - candidate) := by ring
      _ = capDual * (x - cap) := by rw [hcapComplement]; ring
      _ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos
        hcapDual (sub_nonpos.mpr hupper)
  have hzero : -(zeroDual * (x - candidate)) ≤ 0 := by
    calc
      -(zeroDual * (x - candidate)) =
          -(zeroDual * x) + zeroDual * candidate := by ring
      _ = -(zeroDual * x) := by rw [hzeroComplement]; ring
      _ ≤ 0 := neg_nonpos.mpr (mul_nonneg hzeroDual hlower)
  nlinarith [hcap, hzero]

/-- Full normal-cone KKT conditions, including loan/deposit cap
multipliers and nonnegativity multipliers, are sufficient for the
source literal static portfolio problem given OTC supergradients.
This is global sufficiency, not a first-order necessary condition. -/
theorem source_bank_static_optimal_with_bank_caps_and_corners
    (P : Primitives S) (X : Allocation S)
    (t : ℕ) (h : History S t)
    (deficitSlope surplusSlope retainedEquity : ℝ)
    (candidateLoans candidateReserves candidateDeposits : ℝ)
    (marginal : BankPayment → ℝ)
    (loanCapDual loanZeroDual depositCapDual depositZeroDual : ℝ)
    (hLoanCapDual : 0 ≤ loanCapDual)
    (hLoanZeroDual : 0 ≤ loanZeroDual)
    (hDepositCapDual : 0 ≤ depositCapDual)
    (hDepositZeroDual : 0 ≤ depositZeroDual)
    (hLoanCapComplementarity :
      loanCapDual * (P.bankLoanCap * retainedEquity - candidateLoans) = 0)
    (hLoanZeroComplementarity : loanZeroDual * candidateLoans = 0)
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
        (loanCapDual - loanZeroDual))
    (hpricingDeposits :
      X.depositRate t h = X.reserveRate t h +
        (1 - P.reserveRequirementPath t h) *
          finiteSupportExpectation P.paymentSupport P.paymentProbability marginal +
        (X.depositRate t h / X.reserveRate t h -
            P.reserveRequirementPath t h) *
          finiteSupportExpectation P.paymentSupport P.paymentProbability
            (fun ω => marginal ω * P.paymentShock ω) -
        (depositCapDual - depositZeroDual)) :
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
  have hLoanPrice : rL = rR + muMean + (loanCapDual - loanZeroDual) :=
    hpricingLoans
  have hDepositPrice :
      rD = rR + (1 - rho) * muMean + (xi - rho) * muShock -
        (depositCapDual - depositZeroDual) :=
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
        (depositCapDual - depositZeroDual) * (deposits - candidateDeposits) := by
    rw [hLoanPrice, hDepositPrice]
    calc
      _ = (rR + muMean) *
          ((loans - candidateLoans) + (reserves - candidateReserves) -
            (deposits - candidateDeposits)) +
          (loanCapDual - loanZeroDual) * (loans - candidateLoans) +
          (depositCapDual - depositZeroDual) *
            (deposits - candidateDeposits) := by
          dsimp [deltaBase, deltaShock]
          ring
      _ = _ := by rw [hBalanceDiff]; ring
  have hPriceBound :
      rL * (loans - candidateLoans) +
        rR * (reserves - candidateReserves) -
        rD * (deposits - candidateDeposits) +
        deltaBase * muMean + deltaShock * muShock ≤ 0 := by
    rw [hPriceKKT]
    linarith [hLoanGlobalDirection, hDepositGlobalDirection]
  rw [hPayoff, hPayoff]
  linarith [hLiquidityBound, hPriceBound]


#print axioms bank_cap_corner_global_direction
#print axioms source_bank_static_optimal_with_bank_caps_and_corners

end ProposedPaperBankKKTGlobalSufficiency
end Ventura26LiquidityAllocation
