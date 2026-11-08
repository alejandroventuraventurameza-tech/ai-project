import Ventura26LiquidityAllocation.LocalScalarEulerRegimeReconciliationCandidate

/-!
# Recover BOTH original S-regime rows from the source normalized funding dual

The modified 33-row binding-prefix system replaces the L regime row
with a prescribed collateral slack, but also evaluates the original
B form of firm L's capital Euler at date zero. At an interior root,
the scalar normalized funding dual is zero. We show that, for the
literal source reduced equations, the S funding row vanishes and the
binding capital Euler implies the S capital Euler.

These statements are local source-equation implications, NOT a
global competitive-equilibrium certificate. The nonzero loan rate
is explicitly required for conversion of the funding KKT equality.
-/

namespace Ventura26LiquidityAllocation
namespace ProposedLocalScalarOriginalEulerRows

open ProposedLocalScalarEulerRegimeReconciliation

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- The source normalized funding dual is definitionally the dual
appearing in the original firm's capital Euler and regime equations. -/
theorem original_date_zero_funding_dual_eq_normalized
    (P : Primitives S) (I : InheritedState)
    (Z : LocalPrefixCoordinates) (dateOne : S) :
    localReducedFundingDualL P (localPrefixDateZeroData P I Z dateOne) =
      localNormalizedCollateralDualL P Z := by
  rfl

/-- A zero normalized dual implies the exact original S regime
funding residual is zero, when the date-zero loan rate is nonzero. -/
theorem source_original_S_funding_row_zero
    (P : Primitives S) (I : InheritedState)
    (Z : LocalPrefixCoordinates) (dateOne recurrent : S)
    (tail : LocalPrefixContinuationRule)
    (hloan : Z.controlsZero.loanRate ≠ 0)
    (hdual : localNormalizedCollateralDualL P Z = 0) :
    localReducedPrefixResidual LocalPrefixBranch.slack P I Z
      dateOne recurrent tail LocalPrefixEquation.firmRegimeZeroL = 0 := by
  have hdual' : localReducedFundingDualL P
      (localPrefixDateZeroData P I Z dateOne) = 0 := by
    rw [original_date_zero_funding_dual_eq_normalized]
    exact hdual
  have hloan' : (localPrefixDateZeroData P I Z dateOne).controls.loanRate ≠ 0 := by
    simpa only [localPrefixDateZeroData] using hloan
  change localReducedFirmRegimeResidual LocalPrefixBranch.slack P
    (localPrefixDateZeroData P I Z dateOne) FirmType.L = 0
  exact slack_funding_regime_row_zero_of_zero_dual P
    (localPrefixDateZeroData P I Z dateOne) hloan' hdual'

/-- Zero normalized dual makes the two original capital Euler residuals
identical. Thus a binding Euler residual from the source's 33 modified
rows implies the literal S-regime Euler residual. -/
theorem source_original_S_capital_euler_row_zero
    (P : Primitives S) (I : InheritedState)
    (Z : LocalPrefixCoordinates) (dateOne recurrent : S)
    (tail : LocalPrefixContinuationRule)
    (hbinding : localReducedPrefixResidual LocalPrefixBranch.binding
      P I Z dateOne recurrent tail LocalPrefixEquation.firmCapitalEulerZeroL = 0)
    (hdual : localNormalizedCollateralDualL P Z = 0) :
    localReducedPrefixResidual LocalPrefixBranch.slack P I Z
      dateOne recurrent tail LocalPrefixEquation.firmCapitalEulerZeroL = 0 := by
  have hdual' : localReducedFundingDualL P
      (localPrefixDateZeroData P I Z dateOne) = 0 := by
    rw [original_date_zero_funding_dual_eq_normalized]
    exact hdual
  have heq := binding_euler_eq_slack_euler_of_zero_dual P
    (localPrefixDateZeroData P I Z dateOne) hdual'
  change localReducedFirmCapitalEulerResidual LocalPrefixBranch.binding P
    (localPrefixDateZeroData P I Z dateOne) FirmType.L = 0 at hbinding
  change localReducedFirmCapitalEulerResidual LocalPrefixBranch.slack P
    (localPrefixDateZeroData P I Z dateOne) FirmType.L = 0
  rw [← heq]
  exact hbinding

#print axioms original_date_zero_funding_dual_eq_normalized
#print axioms source_original_S_funding_row_zero
#print axioms source_original_S_capital_euler_row_zero

end ProposedLocalScalarOriginalEulerRows
end Ventura26LiquidityAllocation
