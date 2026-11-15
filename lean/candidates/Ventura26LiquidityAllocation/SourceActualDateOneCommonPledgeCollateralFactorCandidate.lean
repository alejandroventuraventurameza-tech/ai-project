import Ventura26LiquidityAllocation.SourceActualPrefixTwoDateStateTimingCandidate

/-!
# Genuine SOURCE date-one two-firm collateral factorization

The six-dimensional terminal state shares one nominal common pledge
coordinate across H and L. Off a root, however, the original SOURCE
individual firm collateral residuals do NOT vanish identically.
Both are proportional to the discrepancy between the common pledge
coordinate and the genuine next-inflation/next-capital-price liquidation
value. A single zero common-pledge equation therefore enforces BOTH
date-one original firm binding collateral conditions simultaneously.

This repairs a false off-root inference caught by a separate Python
33-equation audit. It uses actual original EconomicModel definitions,
not a toy matrix or an invented SOURCE residual.
-/

namespace Ventura26LiquidityAllocation

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- In the genuine SOURCE date-one state, both firm collateral
residuals factor through the same common terminal pledge gap,
with firm-specific pledgeability and capital multipliers. -/
theorem sourceActualDateOne_collateralRegime_commonPledgeFactor
    (P : Primitives S) (Z : LocalPrefixCoordinates)
    (dateOne recurrent : S) (tail : LocalPrefixContinuationRule)
    (i : FirmType) :
    localReducedFirmRegimeResidual LocalPrefixBranch.binding P
      (localPrefixDateOneData P Z dateOne recurrent tail) i =
      P.pledgeability i * (localPrefixStateSixCapital Z.stateTwo i) *
        (Z.stateTwo.commonPledgeValue -
          (1 - P.depreciation) *
            (tail Z.stateTwo).inflation * (tail Z.stateTwo).capitalPrice) := by
  cases i <;>
    simp only [localReducedFirmRegimeResidual,
      localPrefixDateOneData, localPrefixStateSixFace,
      localPrefixStateSixCapital, localPrefixPledgeUnit] <;>
    ring

#print axioms sourceActualDateOne_collateralRegime_commonPledgeFactor

/-- Conditional zero of BOTH genuine SOURCE date-one collateral
residuals from ONE consistent common terminal pledge value. -/
theorem sourceActualDateOne_twoCollateralRows_zero_of_commonPledge
    (P : Primitives S) (Z : LocalPrefixCoordinates)
    (dateOne recurrent : S) (tail : LocalPrefixContinuationRule)
    (hPledge : Z.stateTwo.commonPledgeValue =
      (1 - P.depreciation) * (tail Z.stateTwo).inflation *
        (tail Z.stateTwo).capitalPrice) :
    (∀ i : FirmType,
      localReducedFirmRegimeResidual LocalPrefixBranch.binding P
        (localPrefixDateOneData P Z dateOne recurrent tail) i = 0) := by
  intro i
  rw [sourceActualDateOne_collateralRegime_commonPledgeFactor]
  rw [hPledge]
  ring

#print axioms sourceActualDateOne_twoCollateralRows_zero_of_commonPledge

/-- Python-coordinate variant of SOURCE's genuine constrained date-one
Euler equation: it uses the independent common terminal pledge coordinate
in place of the next-inflation/next-capital-price valuation. -/
noncomputable def sourceDateOneEulerAtCommonPledgeCoordinate
    (P : Primitives S) (Z : LocalPrefixCoordinates)
    (dateOne recurrent : S) (tail : LocalPrefixContinuationRule)
    (i : FirmType) : ℝ :=
  let d := localPrefixDateOneData P Z dateOne recurrent tail
  let sdf := localPrefixEntrepreneurSDF P d i
  let pledge := P.pledgeability i * Z.stateTwo.commonPledgeValue
  d.controls.capitalPrice - pledge / d.controls.loanRate -
    sdf * (localPrefixNextMarginalProduct P d i +
      (1 - P.depreciation) * d.nextControls.capitalPrice -
      pledge / d.nextControls.inflation)

/-- The exact off-root date-one Euler correction factors through
the SAME common pledge gap as BOTH original firm collateral rows.
At an actual common-pledge root the correction is zero. -/
theorem sourceActualDateOne_EulerCommonPledge_correction
    (P : Primitives S) (Z : LocalPrefixCoordinates)
    (dateOne recurrent : S) (tail : LocalPrefixContinuationRule)
    (i : FirmType) :
    sourceDateOneEulerAtCommonPledgeCoordinate
      P Z dateOne recurrent tail i -
      localReducedFirmCapitalEulerResidual LocalPrefixBranch.binding P
        (localPrefixDateOneData P Z dateOne recurrent tail) i =
      P.pledgeability i *
        (Z.stateTwo.commonPledgeValue -
          (1 - P.depreciation) *
            (tail Z.stateTwo).inflation * (tail Z.stateTwo).capitalPrice) *
        (-(1 / (localPrefixDateOneData P Z dateOne recurrent tail).controls.loanRate) +
          localPrefixEntrepreneurSDF P
            (localPrefixDateOneData P Z dateOne recurrent tail) i /
            (tail Z.stateTwo).inflation) := by
  simp only [sourceDateOneEulerAtCommonPledgeCoordinate,
    localReducedFirmCapitalEulerResidual, localPrefixPledgeUnit,
    localPrefixDateOneData]
  ring

#print axioms sourceActualDateOne_EulerCommonPledge_correction

end Ventura26LiquidityAllocation
