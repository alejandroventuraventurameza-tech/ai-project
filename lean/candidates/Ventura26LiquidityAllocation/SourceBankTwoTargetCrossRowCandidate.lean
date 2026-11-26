import Ventura26LiquidityAllocation.SourceReserveRuleTargetSubstitutionCandidate

/-!
# Exact bank-balance realized/target two-channel identity

A generic algebraic bridge for bank quantities whenever the same common
non-reserve term C is used in both residuals. This is not a claim that
the entire original Python auxiliary has been identified with SOURCE.
In particular, the rate-dependent reserve/deposit multiplier kT must
still be related to the exact Python formula.
-/

namespace Ventura26LiquidityAllocation

/-- If both bank residuals share the same non-reserve term C,
their difference separates into a reserve-quantity correction and
a reserve-rate-dependent multiplier correction. -/
theorem sourceBankBalance_twoTarget_exact
    (C kReal kTarget Mreal Mtarget : ℝ) :
    (C - kTarget * Mtarget) - (C - kReal * Mreal) =
      kReal * (Mreal - Mtarget) +
        (kReal - kTarget) * Mtarget := by
  ring

#print axioms sourceBankBalance_twoTarget_exact

/-- Off-root SOURCE bank quantity correction, exposing the
ORIGINAL reserve-quantity policy residual. The multiplier at
the policy target is deliberately an explicit independent argument:
its identification remains an economic source-code obligation. -/
theorem sourceBankBalance_policyTwoTarget_exact
    {S : Type*} [Fintype S] [DecidableEq S]
    (P : Primitives S) (d : LocalPrefixDateData)
    (kTarget : ℝ) (hM : 0 < d.currentReservesPre) :
    (localPrefixReducedBankLoans P d -
      d.currentBankFace / d.controls.inflation -
      kTarget * sourceQuantityRuleTarget P d) -
    (localPrefixReducedBankLoans P d -
      d.currentBankFace / d.controls.inflation -
      (1 / localPrefixReserveDepositRatio P d - 1) *
        d.currentReservesPre) =
    (1 / localPrefixReserveDepositRatio P d - 1) *
      sourceQuantityRuleTarget P d *
        (Real.exp (localReducedRemainingResidual P d (7 : Fin 11)) - 1) +
      ((1 / localPrefixReserveDepositRatio P d - 1) - kTarget) *
        sourceQuantityRuleTarget P d := by
  have hGap := sourceActualReserves_target_gap P d hM
  have hAlg := sourceBankBalance_twoTarget_exact
    (localPrefixReducedBankLoans P d -
      d.currentBankFace / d.controls.inflation)
    (1 / localPrefixReserveDepositRatio P d - 1)
    kTarget d.currentReservesPre (sourceQuantityRuleTarget P d)
  rw [hGap] at hAlg
  convert hAlg using 1 <;> ring

#print axioms sourceBankBalance_policyTwoTarget_exact

/-- At coincident realized and target reserve quantities and
multipliers, the target-substituted balance and realized balance
are equal. This by itself does not show that the original Python
auxiliary actually produces the target multiplier. -/
theorem sourceBankBalance_twoTarget_commonRoot
    (C kReal kTarget Mreal Mtarget : ℝ)
    (hM : Mreal = Mtarget) (hk : kReal = kTarget) :
    C - kTarget * Mtarget = C - kReal * Mreal := by
  rw [hM, hk]

#print axioms sourceBankBalance_twoTarget_commonRoot

end Ventura26LiquidityAllocation
