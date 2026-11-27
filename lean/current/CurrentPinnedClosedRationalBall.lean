import Ventura26LiquidityAllocation.CurrentPinnedRationalBall

/-!
# Stronger exact rational closed ball in the SOURCE log chart

The previous proof establishes r_joint > 1/200. Its exact bank rate
and logarithmic estimates permit the stronger r_joint > 7/1000.

Crucially, EVERY point in the CLOSED sup-norm ball ||z|| <= 7/1000
still lies STRICTLY inside the open SOURCE banking and positive-dual
neighborhood. A closed ball is the natural input to later quantitative
Banach/Krawczyk tests, but these tests still require actual 33-by-33
economic Jacobian interval enclosures and inverse preconditioners.

This theorem is neither a proof of those enclosures nor an equilibrium.
-/

namespace Ventura26LiquidityAllocation
namespace CurrentPinnedClosedRationalBall

open CurrentPinnedRationalBall
open CurrentPinnedJointQuantitativeBall
open CurrentPinnedQuantitativeBank
open CurrentPinnedOpenBankDomain
open CurrentPinnedBankDomain
open CurrentSourceFullFDeriv
open CurrentSourceTwoDateBank
open scoped Topology

/-- Exact stationary SOURCE joint domain radius exceeds 0.007. -/
theorem pinned_seven_per_mille_lt_joint_radius :
    (7 / 1000 : ℝ) < pinnedJointRadius := by
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

#print axioms pinned_seven_per_mille_lt_joint_radius

/-- The full CLOSED rational SOURCE sup-ball lies inside the
original joint open admissibility/strict-binding neighborhood. -/
theorem pinned_closed_rational_ball_inside_joint
    (z : Row33) (hz : ‖z‖ ≤ (7 / 1000 : ℝ)) :
    ‖z‖ < pinnedJointRadius :=
  lt_of_le_of_lt hz pinned_seven_per_mille_lt_joint_radius

#print axioms pinned_closed_rational_ball_inside_joint

/-- Both actual SOURCE dates are banking-admissible on the full
closed rational ball. No monetary shock h appears in this domain. -/
theorem pinned_closed_rational_ball_bank_domain
    (G : ℝ) (z : Row33)
    (hz : ‖z‖ ≤ (7 / 1000 : ℝ)) :
    TargetBankAdmissible
      (ProposedStationaryPrimitives.primitives G)
      (pinnedDateZero G z) ∧
    TargetBankAdmissible
      (ProposedStationaryPrimitives.primitives G)
      (pinnedDateOne G z) := by
  have hhalf : ‖z‖ < Real.log 2 / 2 :=
    lt_of_lt_of_le
      (pinned_closed_rational_ball_inside_joint z hz)
      (min_le_left _ _)
  have hreg : z ∈ pinnedBankLogRegion :=
    pinned_half_log_ball_subset_bank_region z hhalf
  exact pinned_both_dates_bank_admissible G z hreg.1 hreg.2

#print axioms pinned_closed_rational_ball_bank_domain

/-- The original normalized SOURCE L funding multiplier remains
strictly positive on the CLOSED rational sup-ball. -/
theorem pinned_closed_rational_ball_dual_positive
    (G : ℝ) (z : Row33)
    (hz : ‖z‖ ≤ (7 / 1000 : ℝ)) :
    0 < localNormalizedCollateralDualL
      (ProposedStationaryPrimitives.primitives G)
      (localPrefixLogChart fullyPinnedStationarySOURCEZ0 z) :=
  pinned_funding_dual_pos_in_joint_ball G z
    (pinned_closed_rational_ball_inside_joint z hz)

#print axioms pinned_closed_rational_ball_dual_positive

/-- For ANY fiscal G and monetary innovation h, no 34-row SOURCE
dual-zero boundary exists inside or on this CLOSED 0.007 state ball. -/
theorem pinned_closed_rational_ball_not_boundary34
    (G : ℝ) (z : Row33) (h : ℝ)
    (hz : ‖z‖ ≤ (7 / 1000 : ℝ)) :
    fullyPinnedStationaryP0SOURCE34 G z h ≠ (0, 0) :=
  pinned_SOURCE34_not_root_in_joint_ball G z
    (pinned_closed_rational_ball_inside_joint z hz) h

#print axioms pinned_closed_rational_ball_not_boundary34

end CurrentPinnedClosedRationalBall
end Ventura26LiquidityAllocation
