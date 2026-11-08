import Ventura26LiquidityAllocation.EconomicModel

/-!
# Exact Euler and funding-regime reconciliation for firm L

The source 33-row scalar reduction uses the BINDING form of the
capital Euler residual even while the scalar complementarity permits
a positive slack root. To claim that root represents branch S of
the ORIGINAL reduced prefix, one must reconcile the original
SLACK capital Euler with the BINDING form.

This module proves the exact date-zero algebraic relation and
the zero-dual implication. It does NOT verify which economic
coordinates have zero dual or satisfy the 33 remaining rows.

Both residuals are the literal definitions in EconomicModel.lean,
not free placeholders.
-/

namespace Ventura26LiquidityAllocation
namespace ProposedLocalScalarEulerRegimeReconciliation

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- The dual appearing in the two original capital Euler equations
for the L firm, evaluated on the actual local prefix date data. -/
noncomputable def localReducedFundingDualL
    (P : Primitives S) (d : LocalPrefixDateData) : ℝ :=
  1 / d.controls.loanRate -
    localPrefixEntrepreneurSDF P d FirmType.L /
      d.nextControls.inflation

/-- The exact algebraic difference between the source B and S
capital Euler residuals is minus the pledge-unit value times
the original funding dual. -/
theorem binding_minus_slack_euler_is_pledge_times_dual
    (P : Primitives S) (d : LocalPrefixDateData) :
    localReducedFirmCapitalEulerResidual LocalPrefixBranch.binding P d FirmType.L -
      localReducedFirmCapitalEulerResidual LocalPrefixBranch.slack P d FirmType.L =
        -(localPrefixPledgeUnit P d FirmType.L) *
          localReducedFundingDualL P d := by
  dsimp [localReducedFirmCapitalEulerResidual, localReducedFundingDualL]
  simp only [div_eq_mul_inv]
  ring

/-- When the funding dual vanishes, the source B and S Euler
capital residuals coincide exactly. No collateral slack or
optimality follows from this equality alone. -/
theorem binding_euler_eq_slack_euler_of_zero_dual
    (P : Primitives S) (d : LocalPrefixDateData)
    (hdual : localReducedFundingDualL P d = 0) :
    localReducedFirmCapitalEulerResidual LocalPrefixBranch.binding P d FirmType.L =
      localReducedFirmCapitalEulerResidual LocalPrefixBranch.slack P d FirmType.L := by
  have hdiff := binding_minus_slack_euler_is_pledge_times_dual P d
  rw [hdual, mul_zero, neg_zero, sub_eq_zero] at hdiff
  exact hdiff

/-- At a nonzero loan rate, zero funding dual also satisfies
the source S-regime's loan Euler row, which is separately
required when lifting a scalar solution to the original S system. -/
theorem slack_funding_regime_row_zero_of_zero_dual
    (P : Primitives S) (d : LocalPrefixDateData)
    (hR : d.controls.loanRate ≠ 0)
    (hdual : localReducedFundingDualL P d = 0) :
    localReducedFirmRegimeResidual LocalPrefixBranch.slack P d FirmType.L = 0 := by
  have heq : localPrefixEntrepreneurSDF P d FirmType.L /
      d.nextControls.inflation = 1 / d.controls.loanRate := by
    dsimp [localReducedFundingDualL] at hdual
    linarith only [hdual]
  dsimp [localReducedFirmRegimeResidual]
  calc
    d.controls.loanRate * localPrefixEntrepreneurSDF P d FirmType.L /
      d.nextControls.inflation - 1 =
      d.controls.loanRate *
        (localPrefixEntrepreneurSDF P d FirmType.L /
          d.nextControls.inflation) - 1 := by ring
    _ = d.controls.loanRate * (1 / d.controls.loanRate) - 1 := by rw [heq]
    _ = 0 := by field_simp [hR]

#print axioms binding_minus_slack_euler_is_pledge_times_dual
#print axioms binding_euler_eq_slack_euler_of_zero_dual
#print axioms slack_funding_regime_row_zero_of_zero_dual

end ProposedLocalScalarEulerRegimeReconciliation
end Ventura26LiquidityAllocation
