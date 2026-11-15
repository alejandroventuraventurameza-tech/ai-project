import Ventura26LiquidityAllocation.SourceBankRateMultiplierCandidate

/-!
# Exact two-policy-residual bank-balance correction (abstract bridge)

This candidate composes the already checked quantity-target and
rate-target multiplier identities. It is an algebraic cross-row bridge
under explicit nonzero-domain assumptions and a quantity log-residual
identity. In particular, it does not assert that the original Python
banking equations share the same non-reserve term C, and does not
identify their OTC slopes or prove a full 33-row Jacobian parity.
-/

namespace Ventura26LiquidityAllocation

/-- The off-root difference between a balance using policy targets
and the same balance using realized reserves is the sum of the
quantity-rule exponential gap and the rate-rule multiplier gap.
The parameter v is a log-residual, with its exact meaning imposed
by the hypothesis hQuantityRule. -/
theorem sourceBankBalance_twoPolicyResiduals_exact
    (C a d c R T M N v : ℝ)
    (hR : R ≠ 0) (hT : T ≠ 0)
    (hRhoR : sourceBankRatioAtRate a d c R ≠ 0)
    (hRhoT : sourceBankRatioAtRate a d c T ≠ 0)
    (hQuantityRule : M - N = N * (Real.exp v - 1)) :
    (C - sourceBankMultiplierAtRate a d c T * N) -
      (C - sourceBankMultiplierAtRate a d c R * M) =
      sourceBankMultiplierAtRate a d c R * N *
          (Real.exp v - 1) +
        N * (d * c * (R - T) /
          (R * T * sourceBankRatioAtRate a d c R *
            sourceBankRatioAtRate a d c T)) := by
  calc
    (C - sourceBankMultiplierAtRate a d c T * N) -
        (C - sourceBankMultiplierAtRate a d c R * M) =
      sourceBankMultiplierAtRate a d c R * (M - N) +
        (sourceBankMultiplierAtRate a d c R -
          sourceBankMultiplierAtRate a d c T) * N :=
            sourceBankBalance_twoTarget_exact C
              (sourceBankMultiplierAtRate a d c R)
              (sourceBankMultiplierAtRate a d c T) M N
    _ = _ := by
      rw [hQuantityRule, sourceBankMultiplierAtRate_gap a d c R T
        hR hT hRhoR hRhoT]
      ring

#print axioms sourceBankBalance_twoPolicyResiduals_exact

/-- At a common policy-rule root, realized and target rates and
reserve quantities agree; hence the two abstract balances agree.
No existence of such a root is asserted. -/
theorem sourceBankBalance_twoPolicy_commonRoot
    (C a d c R T M N : ℝ)
    (hRate : R = T) (hQuantity : M = N) :
    C - sourceBankMultiplierAtRate a d c T * N =
      C - sourceBankMultiplierAtRate a d c R * M := by
  rw [hRate, hQuantity]

#print axioms sourceBankBalance_twoPolicy_commonRoot

end Ventura26LiquidityAllocation
