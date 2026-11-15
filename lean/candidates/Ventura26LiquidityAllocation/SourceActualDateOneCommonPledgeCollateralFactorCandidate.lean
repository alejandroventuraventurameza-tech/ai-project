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

end Ventura26LiquidityAllocation
