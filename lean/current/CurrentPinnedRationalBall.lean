import Ventura26LiquidityAllocation.CurrentPinnedJointQuantitativeBall
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# An exact rational SOURCE exclusion radius

The previous SOURCE result gives the positive but irrational
  min(log(2)/2, log(25/(24*R_L))/4).
Here we sharpen the *genuine stationary-bank loan-rate* upper bound
using the previously proved OTC slope and deposit-pricing identities,
then lower bound the logarithms by 1 - 1/x to certify

  1/200 < pinnedJointRadius.

Thus any 33-log-coordinate ball of radius 1/200 is inside the joint
banking/strict-binding region, with no floating-point or Python
approximation. This gives a rational input for a FUTURE interval
Jacobian certificate; it does not itself produce such an enclosure,
a Jacobian inverse, or an economic IRF.
-/

namespace Ventura26LiquidityAllocation
namespace CurrentPinnedRationalBall

open ProposedStationaryBank
open CurrentPinnedJointQuantitativeBall
open CurrentSourceFullFDeriv

/-- An upper bound sharper than 25/24 derived from the exact bank
pricing identity, log-two matching slopes, and stationary rate ratio. -/
theorem pinned_stationary_loanRate_lt_81_80 :
    ProposedStationaryBank.loanRate < (81 / 80 : ℝ) := by
  rcases bank_margins_and_pricing with
    ⟨_hxi0, hxiUpper, _hrho0, _hrho1, hpricing, _hloan0, _hloan1⟩
  rcases slope_bounds with
    ⟨hmean0, hmeanUpper, hgap0, hgapUpper, _hmargin⟩
  have hxi : depositRate / reserveRate - (1 / 10 : ℝ) < 1 := by
    linarith
  have hproduct :
      (depositRate / reserveRate - (1 / 10 : ℝ)) * slopeGap <
        (1 / 80 : ℝ) := by
    calc
      _ < 1 * slopeGap := mul_lt_mul_of_pos_right hxi hgap0
      _ = slopeGap := one_mul _
      _ < (1 / 80 : ℝ) := hgapUpper
  have hloan_gap : loanRate - depositRate =
      (1 / 10 : ℝ) * meanSlope +
        (depositRate / reserveRate - 1 / 10) * slopeGap / 10 := by
    unfold depositPricingResidual at hpricing
    unfold loanRate
    linarith
  change loanRate - (100 / 99 : ℝ) =
    (1 / 10 : ℝ) * meanSlope +
      (depositRate / reserveRate - 1 / 10) * slopeGap / 10 at hloan_gap
  nlinarith [hloan_gap, hproduct, hmeanUpper]

#print axioms pinned_stationary_loanRate_lt_81_80

/-- A rational lower bound on the original, exact joint SOURCE
banking/strict-binding radius, uniform in G and policy shock h. -/
theorem pinned_rational_radius_lt_joint :
    (1 / 200 : ℝ) < pinnedJointRadius := by
  have hloan : ProposedStationaryBank.loanRate < (81 / 80 : ℝ) :=
    pinned_stationary_loanRate_lt_81_80
  have hloanpos : 0 < ProposedStationaryBank.loanRate :=
    ProposedStationaryRealScale.loanRate_pos
  have hden : 0 < 24 * ProposedStationaryBank.loanRate := by
    positivity
  have hratio :
      (250 / 243 : ℝ) <
        25 / (24 * ProposedStationaryBank.loanRate) := by
    apply (lt_div_iff₀ hden).2
    nlinarith [hloan]
  have hlogRatio :
      Real.log (250 / 243 : ℝ) <
        Real.log (25 / (24 * ProposedStationaryBank.loanRate)) :=
    Real.log_lt_log (by norm_num) hratio
  have hlog250 : (7 / 250 : ℝ) ≤ Real.log (250 / 243 : ℝ) := by
    have h := Real.one_sub_inv_le_log_of_pos
      (show (0 : ℝ) < 250 / 243 by norm_num)
    convert h using 1 <;> norm_num
  have hlogTwo : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have h := Real.one_sub_inv_le_log_of_pos
      (show (0 : ℝ) < 2 by norm_num)
    convert h using 1 <;> norm_num
  unfold pinnedJointRadius
  apply lt_min
  · nlinarith [hlogTwo]
  · nlinarith [hlogRatio, hlog250]

#print axioms pinned_rational_radius_lt_joint

/-- The common SOURCE banking and normalized L dual certificate covers
every 33-log-displacement of sup norm strictly below 1/200. -/
theorem pinned_rational_ball_binding (G : ℝ) (z : Row33)
    (hz : ‖z‖ < (1 / 200 : ℝ)) :
    0 < localNormalizedCollateralDualL
      (ProposedStationaryPrimitives.primitives G)
      (localPrefixLogChart fullyPinnedStationarySOURCEZ0 z) := by
  apply pinned_funding_dual_pos_in_joint_ball G z
  exact lt_trans hz pinned_rational_radius_lt_joint

#print axioms pinned_rational_ball_binding

/-- No original SOURCE 34-row dual-zero switching boundary is possible
inside the rational 1/200 log-ball, for any stationary G or innovation h.
This DOES NOT bound the monetary shock itself. -/
theorem pinned_rational_ball_not_SOURCE34_root (G : ℝ)
    (z : Row33) (h : ℝ)
    (hz : ‖z‖ < (1 / 200 : ℝ)) :
    fullyPinnedStationaryP0SOURCE34 G z h ≠ (0, 0) := by
  exact pinned_SOURCE34_not_root_in_joint_ball G z
    (lt_trans hz pinned_rational_radius_lt_joint) h

#print axioms pinned_rational_ball_not_SOURCE34_root

end CurrentPinnedRationalBall
end Ventura26LiquidityAllocation
