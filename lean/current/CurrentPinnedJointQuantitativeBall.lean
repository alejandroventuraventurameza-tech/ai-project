import Ventura26LiquidityAllocation.CurrentPinnedQuantitativeBankMargins
import Ventura26LiquidityAllocation.CurrentPinnedStrictBindingNeighborhood

/-!
# An explicit common banking and strict-binding radius around the pinned SOURCE root

This is a finite-dimensional, exact SOURCE certificate. It combines
the already-proved quantitative reserve/deposit margins with the literal
firm-L normalized funding-dual identity on the SAME 33-dimensional
log chart and stationary P0 reference.

Nothing here supplies a bound on the inverse SOURCE Jacobian, a
34-equation switching-boundary root, fiscal admissibility for G,
a global optimum, an IRF, or an infinite-horizon equilibrium.
-/

namespace Ventura26LiquidityAllocation
namespace CurrentPinnedJointQuantitativeBall

open CurrentPinnedQuantitativeBank
open CurrentPinnedBankDomain
open CurrentPinnedOpenBankDomain
open CurrentPinnedStationaryDual
open CurrentSourceFullFDeriv
open ProposedLocalScalarAugmented34Source
open scoped Topology

/-- A positive common radius: the banking log-ball and a strict
firm-L funding-dual log-ball share the same exact SOURCE origin. -/
noncomputable def pinnedJointRadius : ℝ :=
  min (Real.log 2 / 2)
    (Real.log (25 / (24 * ProposedStationaryBank.loanRate)) / 4)

theorem pinnedJointRadius_pos : 0 < pinnedJointRadius := by
  have hloanPos : 0 < ProposedStationaryBank.loanRate :=
    ProposedStationaryRealScale.loanRate_pos
  have hloanUpper : ProposedStationaryBank.loanRate < 25 / 24 := by
    rcases ProposedStationaryBank.bank_margins_and_pricing with
      ⟨_, _, _, _, _, _, hu⟩
    exact hu
  have hden : 0 < 24 * ProposedStationaryBank.loanRate := by
    positivity
  have hratio : (1 : ℝ) <
      25 / (24 * ProposedStationaryBank.loanRate) := by
    apply (lt_div_iff₀ hden).2
    nlinarith [hloanUpper]
  have hlogtwo : 0 < Real.log (2 : ℝ) :=
    Real.log_pos (by norm_num)
  have hlogratio : 0 <
      Real.log (25 / (24 * ProposedStationaryBank.loanRate)) :=
    Real.log_pos hratio
  unfold pinnedJointRadius
  exact lt_min (div_pos hlogtwo (by norm_num))
    (div_pos hlogratio (by norm_num))

#print axioms pinnedJointRadius_pos

/-- The four SOURCE log coordinates appearing in the normalized
funding dual obey their jointly relevant threshold in the common ball. -/
theorem pinned_fourLog_sum_lt_threshold (z : Row33)
    (hz : ‖z‖ < pinnedJointRadius) :
    z (15 : Fin 33) + z (8 : Fin 33) -
      z (24 : Fin 33) - z (28 : Fin 33) <
    Real.log (25 / (24 * ProposedStationaryBank.loanRate)) := by
  have hsmall : ‖z‖ <
      Real.log (25 / (24 * ProposedStationaryBank.loanRate)) / 4 := by
    exact lt_of_lt_of_le hz (min_le_right _ _)
  have hcoord (i : Fin 33) : |z i| ≤ ‖z‖ := by
    simpa only [Real.norm_eq_abs] using (norm_le_pi_norm z i)
  have h15 := (abs_le.mp (hcoord (15 : Fin 33))).2
  have h8 := (abs_le.mp (hcoord (8 : Fin 33))).2
  have h24 := (abs_le.mp (hcoord (24 : Fin 33))).1
  have h28 := (abs_le.mp (hcoord (28 : Fin 33))).1
  linarith

#print axioms pinned_fourLog_sum_lt_threshold

/-- Positive four-exponential expression, with no float approximations.
Its proof clears only strictly positive exponential denominators. -/
theorem positive_fourLog_funding_dual
    (R a b c d : ℝ)
    (hR : 0 < R)
    (hlog : a + b - c - d < Real.log (25 / (24 * R))) :
    0 < 1 / (R * Real.exp a) -
      (24 / 25 : ℝ) * Real.exp b /
        (Real.exp c * Real.exp d) := by
  have hR24 : 0 < 24 * R := mul_pos (by norm_num) hR
  have hratio : 0 < (25 : ℝ) / (24 * R) :=
    div_pos (by norm_num) hR24
  have hExp : Real.exp (a + b - c - d) <
      (25 : ℝ) / (24 * R) := by
    rw [← Real.exp_log hratio]
    exact Real.exp_lt_exp.mpr hlog
  have hExpRatio :
      Real.exp (a + b - c - d) =
        (Real.exp a * Real.exp b) /
          (Real.exp c * Real.exp d) := by
    rw [Real.exp_sub, Real.exp_sub, Real.exp_add]
    field_simp [Real.exp_ne_zero] <;> ring
  have hCD : 0 < Real.exp c * Real.exp d :=
    mul_pos (Real.exp_pos _) (Real.exp_pos _)
  have hRA : 0 < R * Real.exp a :=
    mul_pos hR (Real.exp_pos _)
  have hExpDiv :
      (Real.exp a * Real.exp b) /
        (Real.exp c * Real.exp d) <
          (25 : ℝ) / (24 * R) := by
    rw [← hExpRatio]
    exact hExp
  have hprod :
      (Real.exp a * Real.exp b) * (24 * R) <
        (25 : ℝ) * (Real.exp c * Real.exp d) :=
    (div_lt_div_iff₀ hCD hR24).mp hExpDiv
  have hfund :
      ((24 / 25 : ℝ) * Real.exp b) /
          (Real.exp c * Real.exp d) <
        1 / (R * Real.exp a) := by
    apply (div_lt_div_iff₀ hCD hRA).2
    nlinarith [hprod]
  exact sub_pos.mpr hfund

#print axioms positive_fourLog_funding_dual

/-- The literal, economic SOURCE funding dual at the pinned
stationary chart is the four-log expression, for every G and z. -/
theorem pinned_stationary_source_fourLog (G : ℝ) (z : Row33) :
    localNormalizedCollateralDualL
      (ProposedStationaryPrimitives.primitives G)
      (localPrefixLogChart fullyPinnedStationarySOURCEZ0 z) =
    1 / (ProposedStationaryBank.loanRate *
        Real.exp (z (15 : Fin 33))) -
      (24 / 25 : ℝ) * Real.exp (z (8 : Fin 33)) /
        (Real.exp (z (24 : Fin 33)) *
          Real.exp (z (28 : Fin 33))) := by
  let P := ProposedStationaryPrimitives.primitives G
  let Z := fullyPinnedStationarySOURCEZ0
  have hdiscount : P.entrepreneurRiskAversion = 1 := by rfl
  have hc_same :
      Z.controlsZero.consumptionL = Z.controlsOne.consumptionL := by rfl
  have hc_pos : 0 < Z.controlsZero.consumptionL := by
    change 0 < ProposedStationaryRealScale.firmConsumption .L
    exact ProposedStationaryRealScale.firmConsumption_pos .L
  have hpi : Z.controlsOne.inflation = 1 := by rfl
  have hsource := sourceFundingDual_sigmaOne_stationary_fourLog
    P Z z hdiscount hc_same hc_pos hpi
  have hloan : Z.controlsZero.loanRate =
      ProposedStationaryBank.loanRate := by rfl
  have hbeta : P.entrepreneurDiscount = (24 / 25 : ℝ) := by rfl
  simpa only [hloan, hbeta] using hsource

#print axioms pinned_stationary_source_fourLog

/-- Strictly positive ORIGINAL firm-L funding multiplier on the
entire explicitly sized ball, not merely an unspecified neighborhood. -/
theorem pinned_funding_dual_pos_in_joint_ball (G : ℝ) (z : Row33)
    (hz : ‖z‖ < pinnedJointRadius) :
    0 < localNormalizedCollateralDualL
      (ProposedStationaryPrimitives.primitives G)
      (localPrefixLogChart fullyPinnedStationarySOURCEZ0 z) := by
  rw [pinned_stationary_source_fourLog G z]
  exact positive_fourLog_funding_dual
    ProposedStationaryBank.loanRate
    (z (15 : Fin 33)) (z (8 : Fin 33))
    (z (24 : Fin 33)) (z (28 : Fin 33))
    ProposedStationaryRealScale.loanRate_pos
    (pinned_fourLog_sum_lt_threshold z hz)

#print axioms pinned_funding_dual_pos_in_joint_ball

/-- Within this very same positive ball, all four genuine SOURCE
banking ratios exceed 2/25 by the existing two-date theorem. -/
theorem pinned_joint_ball_bank_margins (G : ℝ) (z : Row33)
    (hz : ‖z‖ < pinnedJointRadius) :
    (2 / 25 : ℝ) <
      localPrefixReserveDepositRatio
        (ProposedStationaryPrimitives.primitives G)
        (pinnedDateZero G z) := by
  have hhalf : ‖z‖ < Real.log 2 / 2 :=
    lt_of_lt_of_le hz (min_le_left _ _)
  exact (pinned_bank_ratios_gt_in_half_log_ball G z hhalf).1.1

#print axioms pinned_joint_ball_bank_margins

/-- The augmented 34-row boundary residual is nonzero for ANY
policy innovation h inside the explicit common positive radius.
This is a local obstruction, never a claim about distant roots. -/
theorem pinned_SOURCE34_not_root_in_joint_ball (G : ℝ) (z : Row33)
    (hz : ‖z‖ < pinnedJointRadius) (h : ℝ) :
    fullyPinnedStationaryP0SOURCE34 G z h ≠ (0, 0) := by
  change augmentedBoundaryZeroResidual
    (ProposedStationaryPrimitives.primitives G)
    (ProposedStationaryInheritedState.inheritedState G)
    fullyPinnedStationarySOURCEZ0
    .dateOne .recurrent
    (sourceLogLinearContinuation
      ProposedStationaryRealScale.stateSix
      ProposedStationaryRealScale.controls
      sourceFrozenP0TenControls)
    z h ≠ (0, 0)
  exact augmentedBoundary_not_root_of_source_funding_dual_pos
    (ProposedStationaryPrimitives.primitives G)
    (ProposedStationaryInheritedState.inheritedState G)
    fullyPinnedStationarySOURCEZ0 .dateOne .recurrent
    (sourceLogLinearContinuation
      ProposedStationaryRealScale.stateSix
      ProposedStationaryRealScale.controls
      sourceFrozenP0TenControls)
    z h (pinned_funding_dual_pos_in_joint_ball G z hz)

#print axioms pinned_SOURCE34_not_root_in_joint_ball

end CurrentPinnedJointQuantitativeBall
end Ventura26LiquidityAllocation
