import Ventura26LiquidityAllocation.PaperBankBellmanStaticSufficiencyCandidate

/-!
# Source one-history Bellman environment derived from static dominance

A global static portfolio certificate is stronger than source KKT
NECESSARY conditions. Under homogeneous future value, positivity
of supported consumption/inflation, positive exit, nonnegative unit
franchise values, and a concrete candidate Bellman VALUE IDENTITY,
the source's actual BankBellmanLocalEnvironmentAt follows.

This bridges the conditional global portfolio maximum to ALL nine
fields of the literal local Bellman environment. It does not assume
BankBellmanLocalEnvironmentAt. It DOES assume the candidate's
one-history value identity, which must eventually come from a full
continuation construction; it does not imply infinite BankOptimal.
-/

namespace Ventura26LiquidityAllocation
namespace ProposedPaperBankBellmanEnvironmentFromStatic

variable {S : Type*} [Fintype S] [DecidableEq S]

theorem source_bank_bellman_environment_of_static_optimality
    (P : Primitives S) (X : Allocation S) (p : BankPlan S)
    (t : ℕ) (h : History S t) (bankValue : BankValueProcess S)
    (hhomogeneous : BankValueHomogeneousAt P t h bankValue)
    (hcurrent : 0 < X.workerConsumption t h)
    (hchild : ∀ s, 0 < P.tree.transition (currentState h) s →
      0 < X.workerConsumption (t + 1) (childHistory h s))
    (hinflation : ∀ s, 0 < P.tree.transition (currentState h) s →
      0 < X.inflation (t + 1) (childHistory h s))
    (hexit : 0 < P.bankExit)
    (hunitValue : ∀ s, 0 < P.tree.transition (currentState h) s →
      0 ≤ bankValue (t + 1) 1 (childHistory h s))
    (hdividend : 0 ≤ p.dividend t h)
    (hretention :
      p.retainedEquity t h = p.equity t h - p.dividend t h)
    (hcandidateFeasible : BankStaticPortfolioFeasibleAt P X t h
      (bankOTCDeficitSlopeAt P X t h (X.bankTightness t h))
      (bankOTCSurplusSlopeAt P X t h (X.bankTightness t h))
      (p.retainedEquity t h) (p.loans t h) (p.reservesPre t h)
      (p.deposits t h))
    (hstaticOptimal : BankStaticPortfolioOptimalAt P X t h
      (bankOTCDeficitSlopeAt P X t h (X.bankTightness t h))
      (bankOTCSurplusSlopeAt P X t h (X.bankTightness t h))
      (p.retainedEquity t h) (p.loans t h) (p.reservesPre t h)
      (p.deposits t h))
    (hcandidateValueIdentity :
      bankValue t (p.equity t h) h =
        p.dividend t h +
        bankBellmanContinuationAt P X t h
          (bankOTCDeficitSlopeAt P X t h (X.bankTightness t h))
          (bankOTCSurplusSlopeAt P X t h (X.bankTightness t h))
          (p.loans t h) (p.reservesPre t h) (p.deposits t h)
          (bankValue (t + 1))) :
    BankBellmanLocalEnvironmentAt P X t h p
      (X.bankTightness t h) bankValue := by
  have hpositiveWeight :
      0 < bankBellmanContinuationWeightAt P X t h
        (bankValue (t + 1)) :=
    bankBellmanContinuationWeightAt_pos_of_finiteValue
      P X t h bankValue hcurrent hchild hinflation hexit hunitValue
  have hglobalBellman :=
    ProposedPaperBankBellmanStaticSufficiency.source_bellman_portfolio_ranking_with_derived_weight
        P X t h
        (bankOTCDeficitSlopeAt P X t h (X.bankTightness t h))
        (bankOTCSurplusSlopeAt P X t h (X.bankTightness t h))
        (p.retainedEquity t h)
        (p.loans t h) (p.reservesPre t h) (p.deposits t h)
        bankValue hhomogeneous hcurrent hchild hinflation hexit
        hunitValue hcandidateFeasible hstaticOptimal
  refine ⟨hcurrent, hchild, ?_, hdividend, hretention,
    hcandidateFeasible, hcandidateValueIdentity, ?_, hpositiveWeight⟩
  · intro s hs
    exact bankStochasticDiscountAt_pos_of_consumption
      P X t h s hcurrent (hchild s hs)
  · intro loans reserves deposits hfeasible
    have hdom := hglobalBellman loans reserves deposits hfeasible
    rw [hcandidateValueIdentity]
    exact add_le_add_left hdom (p.dividend t h)

#print axioms source_bank_bellman_environment_of_static_optimality

end ProposedPaperBankBellmanEnvironmentFromStatic
end Ventura26LiquidityAllocation
