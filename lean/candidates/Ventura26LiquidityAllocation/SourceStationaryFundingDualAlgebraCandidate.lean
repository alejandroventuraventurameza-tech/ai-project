import Ventura26LiquidityAllocation.EconomicModel

/-!
# Genuine SOURCE stationary funding-dual algebra

For the original SOURCE normalized L funding dual, identical firm-L
consumption across the two dates and date-one unit inflation reduce
the expression to 1 / Rloan - betaE, provided marginal utility is
nonzero. A loan rate below 25/24 with betaE = 24/25 then implies
a strictly positive dual.

These results are conditional on the SAME SOURCE coordinates and
primitives satisfying the stated equations. The frozen Python
stationary values do not supply those SOURCE equalities automatically.
-/

namespace Ventura26LiquidityAllocation

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- Exact SOURCE stationary simplification of the L funding-dual row. -/
theorem sourceStationaryFundingDual_eq_inverseRate_sub_discount
    (P : Primitives S) (Z : LocalPrefixCoordinates)
    (hsame : Z.controlsOne.consumptionL = Z.controlsZero.consumptionL)
    (hpi : Z.controlsOne.inflation = 1)
    (hmu : crraMarginal P.entrepreneurRiskAversion
      Z.controlsZero.consumptionL ≠ 0) :
    localNormalizedCollateralDualL P Z =
      1 / Z.controlsZero.loanRate - P.entrepreneurDiscount := by
  simp [localNormalizedCollateralDualL, hsame, hpi, hmu]

/-- The general SOURCE stationary sign criterion. The spread is an
explicit hypothesis, not inferred from an unverified numerical root. -/
theorem sourceStationaryFundingDual_pos_of_rate_discount_spread
    (P : Primitives S) (Z : LocalPrefixCoordinates)
    (hsame : Z.controlsOne.consumptionL = Z.controlsZero.consumptionL)
    (hpi : Z.controlsOne.inflation = 1)
    (hmu : crraMarginal P.entrepreneurRiskAversion
      Z.controlsZero.consumptionL ≠ 0)
    (hspread : P.entrepreneurDiscount <
      1 / Z.controlsZero.loanRate) :
    0 < localNormalizedCollateralDualL P Z := by
  rw [sourceStationaryFundingDual_eq_inverseRate_sub_discount
    P Z hsame hpi hmu]
  linarith

/-- Rational rate and discount bounds obtained independently for the
illustrative frozen Python parameters imply a positive SOURCE dual
ONLY IF those same rate and discount equalities hold in SOURCE. -/
theorem sourceStationaryFundingDual_pos_of_rate_lt_25_div_24
    (P : Primitives S) (Z : LocalPrefixCoordinates)
    (hsame : Z.controlsOne.consumptionL = Z.controlsZero.consumptionL)
    (hpi : Z.controlsOne.inflation = 1)
    (hmu : crraMarginal P.entrepreneurRiskAversion
      Z.controlsZero.consumptionL ≠ 0)
    (hbeta : P.entrepreneurDiscount = (24 : ℝ) / 25)
    (hloan : 0 < Z.controlsZero.loanRate)
    (hloan_bound : Z.controlsZero.loanRate < (25 : ℝ) / 24) :
    0 < localNormalizedCollateralDualL P Z := by
  have hprod :
      (24 : ℝ) / 25 * Z.controlsZero.loanRate < 1 := by
    nlinarith [hloan_bound]
  have hspread : P.entrepreneurDiscount <
      1 / Z.controlsZero.loanRate := by
    rw [hbeta]
    exact (lt_div_iff₀ hloan).2 hprod
  exact sourceStationaryFundingDual_pos_of_rate_discount_spread
    P Z hsame hpi hmu hspread

#print axioms sourceStationaryFundingDual_eq_inverseRate_sub_discount
#print axioms sourceStationaryFundingDual_pos_of_rate_discount_spread
#print axioms sourceStationaryFundingDual_pos_of_rate_lt_25_div_24

end Ventura26LiquidityAllocation
