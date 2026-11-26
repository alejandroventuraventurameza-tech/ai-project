import Ventura26LiquidityAllocation.PaperBankZeroEquityBoundaryCandidate
import Ventura26LiquidityAllocation.PaperBankKKTFullCornerCandidate

/-!
# SOURCE unit-equity KKT certificate -> ALL-equity bank Bellman upper bound

The static bank KKT theorem is used at retained equity ONE. Scaling,
solvency, the SOURCE dynamic feasibility boundary, and the homogeneous
Bellman continuation are then inherited from proved source theorems.

The certificate is EXPLICIT: all five nonnegative corner/cap duals,
complementarity, candidate feasibility, OTC supergradient, and both
pricing equalities must hold. The unit optimizer is therefore NOT
assumed directly. The condition k>=1 is STILL an economic obligation,
not hidden inside the certificate. Neither a feasible attaining
candidate nor infinite-horizon bank optimality follows here.
-/

namespace Ventura26LiquidityAllocation
namespace ProposedBankUnitKKTAllEquityBridge

open ProposedBankGlobalDividendBoundFromNormalized
open ProposedBankZeroEquityBoundary
variable {S : Type*} [Fintype S] [DecidableEq S]

/-- Exact SOURCE five-dual static KKT certificate at ONE retained
equity. The normalized portfolio and source OTC slopes are evaluated
at the actual aggregate history. -/
structure UnitBankKKTCertificateAt
    (P : Primitives S) (X : Allocation S)
    (t : ℕ) (h : History S t)
    (unitLoans unitReserves unitDeposits : ℝ)
    (marginal : BankPayment → ℝ)
    (loanCapDual loanZeroDual reserveZeroDual depositCapDual depositZeroDual : ℝ) : Prop where
  loanCapNonneg : 0 ≤ loanCapDual
  loanZeroNonneg : 0 ≤ loanZeroDual
  reserveZeroNonneg : 0 ≤ reserveZeroDual
  depositCapNonneg : 0 ≤ depositCapDual
  depositZeroNonneg : 0 ≤ depositZeroDual
  loanCapComp : loanCapDual * (P.bankLoanCap * 1 - unitLoans) = 0
  loanZeroComp : loanZeroDual * unitLoans = 0
  reserveZeroComp : reserveZeroDual * unitReserves = 0
  depositCapComp : depositCapDual * (P.bankDepositCap * 1 - unitDeposits) = 0
  depositZeroComp : depositZeroDual * unitDeposits = 0
  unitFeasible : BankStaticPortfolioFeasibleAt P X t h
    (bankOTCDeficitSlopeAt P X t h (X.bankTightness t h))
    (bankOTCSurplusSlopeAt P X t h (X.bankTightness t h))
    1 unitLoans unitReserves unitDeposits
  otcSupergradient : ∀ ω ∈ P.paymentSupport,
    IsOTCLiquiditySupergradient
      (bankOTCDeficitSlopeAt P X t h (X.bankTightness t h))
      (bankOTCSurplusSlopeAt P X t h (X.bankTightness t h))
      (bankSettlementSurplus unitReserves
        (P.reserveRequirementPath t h)
        (X.depositRate t h / X.reserveRate t h)
        unitDeposits (P.paymentShock ω))
      (marginal ω)
  loanPricing :
    X.loanRate t h = X.reserveRate t h +
      finiteSupportExpectation P.paymentSupport P.paymentProbability marginal +
      reserveZeroDual + (loanCapDual - loanZeroDual)
  depositPricing :
    X.depositRate t h = X.reserveRate t h +
      (1 - P.reserveRequirementPath t h) *
        finiteSupportExpectation P.paymentSupport P.paymentProbability marginal +
      (X.depositRate t h / X.reserveRate t h -
          P.reserveRequirementPath t h) *
        finiteSupportExpectation P.paymentSupport P.paymentProbability
          (fun ω => marginal ω * P.paymentShock ω) -
      (depositCapDual - depositZeroDual) + reserveZeroDual

/-- SOURCE global static optimality at retained equity ONE follows
from all five normal-cone multipliers and source OTC supergradients. -/
theorem source_unit_static_optimal_of_five_dual_kkt
    (P : Primitives S) (X : Allocation S)
    (t : ℕ) (h : History S t)
    (unitLoans unitReserves unitDeposits : ℝ)
    (marginal : BankPayment → ℝ)
    (loanCapDual loanZeroDual reserveZeroDual depositCapDual depositZeroDual : ℝ)
    (hKKT : UnitBankKKTCertificateAt P X t h
      unitLoans unitReserves unitDeposits marginal
      loanCapDual loanZeroDual reserveZeroDual depositCapDual depositZeroDual) :
    BankStaticPortfolioOptimalAt P X t h
      (bankOTCDeficitSlopeAt P X t h (X.bankTightness t h))
      (bankOTCSurplusSlopeAt P X t h (X.bankTightness t h))
      1 unitLoans unitReserves unitDeposits := by
  exact ProposedPaperBankKKTFullCorner.source_bank_static_optimal_with_all_bank_nonneg_corners
    P X t h
    (bankOTCDeficitSlopeAt P X t h (X.bankTightness t h))
    (bankOTCSurplusSlopeAt P X t h (X.bankTightness t h))
    1 unitLoans unitReserves unitDeposits marginal
    loanCapDual loanZeroDual reserveZeroDual depositCapDual depositZeroDual
    hKKT.loanCapNonneg hKKT.loanZeroNonneg hKKT.reserveZeroNonneg
    hKKT.depositCapNonneg hKKT.depositZeroNonneg
    hKKT.loanCapComp hKKT.loanZeroComp hKKT.reserveZeroComp
    hKKT.depositCapComp hKKT.depositZeroComp
    hKKT.unitFeasible hKKT.otcSupergradient
    hKKT.loanPricing hKKT.depositPricing

/-- Joint dividend-and-portfolio one-step bound for every SOURCE
feasible bank continuation at any nonnegative equity. Unlike earlier
lemmas, the unit optimizer and nonnegative Bellman weight are derived
from the SOURCE KKT certificate and primitive positivity premises.
The conditional coefficient k>=1 remains explicit. -/
theorem source_all_equity_bank_bellman_bound_of_unit_kkt
    (P : Primitives S) (X : Allocation S)
    (t : ℕ) (h : History S t)
    (equity : ℝ)
    (bankValue : BankValueProcess S)
    (unitLoans unitReserves unitDeposits : ℝ)
    (marginal : BankPayment → ℝ)
    (loanCapDual loanZeroDual reserveZeroDual depositCapDual depositZeroDual : ℝ)
    (hKKT : UnitBankKKTCertificateAt P X t h
      unitLoans unitReserves unitDeposits marginal
      loanCapDual loanZeroDual reserveZeroDual depositCapDual depositZeroDual)
    (hhomogeneous : BankValueHomogeneousAt P t h bankValue)
    (hcurrent : 0 < X.workerConsumption t h)
    (hchild : ∀ s, 0 < P.tree.transition (currentState h) s →
      0 < X.workerConsumption (t + 1) (childHistory h s))
    (hinflation : ∀ s, 0 < P.tree.transition (currentState h) s →
      0 < X.inflation (t + 1) (childHistory h s))
    (hexit : 0 < P.bankExit)
    (hunitValue : ∀ s, 0 < P.tree.transition (currentState h) s →
      0 ≤ bankValue (t + 1) 1 (childHistory h s))
    (hcoefficient : 1 ≤ sourceUnitContinuationCoefficient P X t h
      bankValue unitLoans unitReserves unitDeposits) :
    ∀ q : BankContinuationPolicy S P.paymentSupport,
      BankContinuationFeasibleAt P X t h equity q →
      q.dividend 0 (fun j => Fin.elim0 j) (fun j => Fin.elim0 j) +
        sourceDateZeroBellman P X t h q (bankValue (t + 1)) ≤
      sourceUnitContinuationCoefficient P X t h
        bankValue unitLoans unitReserves unitDeposits * equity := by
  have hunitOptimal :=
    source_unit_static_optimal_of_five_dual_kkt P X t h
      unitLoans unitReserves unitDeposits marginal
      loanCapDual loanZeroDual reserveZeroDual depositCapDual depositZeroDual
      hKKT
  have hweight : 0 ≤
      bankBellmanContinuationWeightAt P X t h (bankValue (t + 1)) :=
    (bankBellmanContinuationWeightAt_pos_of_finiteValue
      P X t h bankValue hcurrent hchild hinflation hexit hunitValue).le
  exact source_all_equity_dividend_portfolio_upper_bound
    P X t h equity bankValue
      unitLoans unitReserves unitDeposits
      hhomogeneous hweight hunitOptimal hcoefficient

#print axioms source_unit_static_optimal_of_five_dual_kkt
#print axioms source_all_equity_bank_bellman_bound_of_unit_kkt

end ProposedBankUnitKKTAllEquityBridge
end Ventura26LiquidityAllocation
