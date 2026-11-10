import Ventura26LiquidityAllocation.BoundaryNarrowRightCoreCandidate

/-!
# Original SOURCE: unconditional narrow-right resource sign

SOURCE-wide stationary worker consumption is bounded using the original
bank credit and heterogeneous capital scales. The date-zero worker
consumption, both firm consumptions, and investment installation cost
then receive narrow right-endpoint rational upper enclosures.

Combining them with the SOURCE production lower enclosure proves the
strict resource sign on ORIGINAL economic expressions, and consequently
localizes the unique reduced-prefix SOURCE rate in the six-decimal
interval. No Python interval certificate is introduced as a Lean axiom.

The formal result is not a complete infinite-horizon competitive
equilibrium: inherited nominal-face consistency remains separate.
-/

namespace Ventura26LiquidityAllocation
namespace ProposedBoundaryNarrowRightResidualSign

open ProposedStationaryBank
open ProposedStationaryRealScale
open ProposedBoundaryBridge
open ProposedBoundaryResourceRoot
open ProposedBoundaryEndpointBoxes
open ProposedBoundaryNormalizationBridge
open ProposedBoundaryNarrowSourceResidualBridge
open ProposedBoundaryNarrowRightCore
open ProposedBoundaryNarrowLeftResidualSign
open ProposedBoundaryInheritedFaceIntervalBridge

/-- Sharpen the SOURCE stationary worker-consumption coefficient using
source-derived loan, heterogeneous capital and output micro-boxes.
The credit balance is explicitly multiplied by the ORIGINAL loan rate. -/
theorem source_stationary_worker_scale_sharp_upper :
    workerConsumptionScale < (8038071 / 1000000 : ℝ) := by
  rcases boundary_source_loan_rate_sharp_box with ⟨hrlo, hrhi⟩
  rcases boundary_source_capital_scales_sharp_boxes with
    ⟨⟨_, hkHhi⟩, ⟨_, hkLhi⟩⟩
  have hYhi := boundary_source_output_scale_sharp_box.2
  have hKhi :
      ProposedStationaryRealScale.average
          ProposedStationaryRealScale.capitalScale <
        (75542965 / 1000000 : ℝ) := by
    unfold ProposedStationaryRealScale.average
    linarith only [hkHhi, hkLhi]
  have hrpos : 0 < ProposedStationaryBank.loanRate :=
    ProposedStationaryRealScale.loanRate_pos
  have hcreditScaled :
      ProposedStationaryRealScale.creditScale *
          ProposedStationaryBank.loanRate =
        ((3 / 20 : ℝ) * (3159 / 3200 : ℝ) *
            ProposedStationaryRealScale.capitalScale .H +
          (2 / 5 : ℝ) * (3159 / 3200 : ℝ) *
            ProposedStationaryRealScale.capitalScale .L) / 2 := by
    unfold ProposedStationaryRealScale.creditScale
      ProposedStationaryRealScale.average
      ProposedStationaryRealScale.pledgeability
      ProposedStationaryRealScale.liquidationValue
      ProposedStationaryRealScale.capitalPrice
    field_simp [ne_of_gt hrpos] <;> ring
  have hcreditScaledUpper :
      ((3 / 20 : ℝ) * (3159 / 3200 : ℝ) *
          ProposedStationaryRealScale.capitalScale .H +
        (2 / 5 : ℝ) * (3159 / 3200 : ℝ) *
          ProposedStationaryRealScale.capitalScale .L) / 2 <
        (2255294 / 100000 : ℝ) *
          (101204823607 / 100000000000 : ℝ) := by
    linarith only [hkHhi, hkLhi]
  have hcreditUpper :
      ProposedStationaryRealScale.creditScale <
        (2255294 / 100000 : ℝ) := by
    by_contra hn
    have hge :
        (2255294 / 100000 : ℝ) ≤
          ProposedStationaryRealScale.creditScale :=
      le_of_not_gt hn
    have hm := mul_le_mul_of_nonneg_right hge hrpos.le
    rw [hcreditScaled] at hm
    linarith only [hcreditScaledUpper, hm, hrlo]
  have hloanAboveOne : 0 < ProposedStationaryBank.loanRate - 1 :=
    sub_pos.mpr ProposedStationaryRealScale.loanRate_gt_one
  have hcreditPayoff :
      (ProposedStationaryBank.loanRate - 1) *
          ProposedStationaryRealScale.creditScale <
        ((101204823808 / 100000000000 : ℝ) - 1) *
          (2255294 / 100000 : ℝ) := by
    calc
      _ < (ProposedStationaryBank.loanRate - 1) *
          (2255294 / 100000 : ℝ) :=
        mul_lt_mul_of_pos_left hcreditUpper hloanAboveOne
      _ < _ :=
        mul_lt_mul_of_pos_right (by linarith only [hrhi])
          (by norm_num)
  have hrat :
      (7 / 12 : ℝ) * (13293504 / 1000000 : ℝ) +
        (75542965 / 1000000 : ℝ) / 6400 +
        ((101204823808 / 100000000000 : ℝ) - 1) *
          (2255294 / 100000 : ℝ) <
        (8038071 / 1000000 : ℝ) := by norm_num
  unfold ProposedStationaryRealScale.workerConsumptionScale
  linarith only [hYhi, hKhi, hcreditPayoff, hrat]

/-- The ORIGINAL SOURCE worker consumption is smaller than 7.904353 at
R=1.029136. Stationary and contemporaneous policy prices are not merged. -/
theorem source_narrow_right_worker_consumption_upper :
    normalizedWorkerConsumption (1029136 / 1000000 : ℝ) <
      (7904353 / 1000000 : ℝ) := by
  have hw := source_stationary_worker_scale_sharp_upper
  have hrd := source_narrow_right_deposit_rate_box.1
  have hden :
      0 < (99 / 100 : ℝ) *
        boundaryDepositRate (1029136 / 1000000 : ℝ) :=
    mul_pos (by norm_num)
      (lt_trans (by norm_num : (0 : ℝ) < 10271889 / 10000000) hrd)
  unfold normalizedWorkerConsumption
  apply (div_lt_iff₀ hden).2
  have hrate :
      (99 / 100 : ℝ) * (10271889 / 10000000 : ℝ) <
        (99 / 100 : ℝ) *
          boundaryDepositRate (1029136 / 1000000 : ℝ) :=
    mul_lt_mul_of_pos_left hrd (by norm_num)
  calc
    workerConsumptionScale < (8038071 / 1000000 : ℝ) := hw
    _ < (7904353 / 1000000 : ℝ) *
          ((99 / 100 : ℝ) * (10271889 / 10000000 : ℝ)) := by
      norm_num
    _ < (7904353 / 1000000 : ℝ) *
          ((99 / 100 : ℝ) *
            boundaryDepositRate (1029136 / 1000000 : ℝ)) :=
      mul_lt_mul_of_pos_left hrate (by norm_num)

/-- Narrow-right SOURCE installation cost: strictly below 2.064043. -/
theorem source_narrow_right_capital_cost_upper :
    normalizedCapitalCost (1029136 / 1000000 : ℝ) <
      (2064043 / 1000000 : ℝ) := by
  let R : ℝ := 1029136 / 1000000
  have hslo :
      (99780694 / 100000000 : ℝ) < boundaryCapitalScale R :=
    source_narrow_right_capital_scale_box.1
  have hmul :
      4 * (99780694 / 100000000 : ℝ) <
        4 * boundaryCapitalScale R := by
    nlinarith only [hslo]
  have hrecip :
      (1 : ℝ) / (4 * boundaryCapitalScale R) <
        1 / (4 * (99780694 / 100000000 : ℝ)) :=
    one_div_lt_one_div_of_lt (by norm_num) hmul
  have hfactor :
      (41 / 80 : ℝ) + 1 / (4 * boundaryCapitalScale R) -
          (4719 / 6400 : ℝ) * boundaryCapitalScale R <
        (2732276 / 100000000 : ℝ) := by
    have hrat :
        (41 / 80 : ℝ) +
          1 / (4 * (99780694 / 100000000 : ℝ)) -
          (4719 / 6400 : ℝ) * (99780694 / 100000000 : ℝ) <
        (2732276 / 100000000 : ℝ) := by
      norm_num
    linarith only [hrecip, hslo, hrat]
  have hKhi :
      ProposedStationaryRealScale.average
          ProposedStationaryRealScale.capitalScale <
        (75542965 / 1000000 : ℝ) := by
    rcases boundary_source_capital_scales_sharp_boxes with
      ⟨⟨_, hkHhi⟩, ⟨_, hkLhi⟩⟩
    unfold ProposedStationaryRealScale.average
    linarith only [hkHhi, hkLhi]
  have hKpos : 0 <
      ProposedStationaryRealScale.average
        ProposedStationaryRealScale.capitalScale :=
    ProposedStationaryRealScale.aggregate_scales_pos.1
  change normalizedCapitalCost R < (2064043 / 1000000 : ℝ)
  unfold normalizedCapitalCost
  calc
    _ < ProposedStationaryRealScale.average
          ProposedStationaryRealScale.capitalScale *
            (2732276 / 100000000 : ℝ) :=
      mul_lt_mul_of_pos_left hfactor hKpos
    _ < (75542965 / 1000000 : ℝ) *
          (2732276 / 100000000 : ℝ) :=
      mul_lt_mul_of_pos_right hKhi (by norm_num)
    _ < (2064043 / 1000000 : ℝ) := by norm_num

/-- SOURCE H-firm consumption sharp box. The parent capital promise
coefficient, stationary pledgeability and current interest rate are
retained in the exact expression. -/
theorem source_narrow_right_firm_H_upper :
    normalizedFirmConsumption (1029136 / 1000000 : ℝ) .H <
      (2957400 / 1000000 : ℝ) := by
  let R : ℝ := 1029136 / 1000000
  let fH : ℝ := (81 / 80 : ℝ) *
    ((911 / 9600 : ℝ) -
      (1131 / 25600 : ℝ) / ProposedStationaryBank.loanRate)
  have hloanpos : 0 < ProposedStationaryBank.loanRate :=
    ProposedStationaryRealScale.loanRate_pos
  have hloanhi := boundary_source_loan_rate_sharp_box.2
  have hfHscaled :
      fH * ProposedStationaryBank.loanRate =
        (81 / 80 : ℝ) *
          ((911 / 9600 : ℝ) * ProposedStationaryBank.loanRate -
            (1131 / 25600 : ℝ)) := by
    dsimp [fH]
    field_simp [ne_of_gt hloanpos] <;> ring
  have hfHhi : fH < (5188263 / 100000000 : ℝ) := by
    by_contra hn
    have hge : (5188263 / 100000000 : ℝ) ≤ fH :=
      le_of_not_gt hn
    have hm := mul_le_mul_of_nonneg_right hge hloanpos.le
    rw [hfHscaled] at hm
    linarith only [hm, hloanhi]
  have hcoefFormula :
      firmCoefficient .H = capitalScale .H * fH := by
    dsimp [fH, firmCoefficient,
      ProposedStationaryRealScale.userCost,
      ProposedStationaryRealScale.pledgeability,
      ProposedStationaryRealScale.capitalPrice,
      ProposedStationaryRealScale.liquidationValue]
    field_simp [ne_of_gt hloanpos] <;> ring
  have hkHhi := (boundary_source_capital_scales_sharp_boxes).1.2
  have hkHpos := ProposedStationaryRealScale.capitalScale_pos .H
  have hcoefHi :
      firmCoefficient .H <
        (5677037 / 100000 : ℝ) *
          (5188263 / 100000000 : ℝ) := by
    rw [hcoefFormula]
    calc
      capitalScale .H * fH <
          capitalScale .H * (5188263 / 100000000 : ℝ) :=
        mul_lt_mul_of_pos_left hfHhi hkHpos
      _ < (5677037 / 100000 : ℝ) *
          (5188263 / 100000000 : ℝ) :=
        mul_lt_mul_of_pos_right hkHhi (by norm_num)
  have huLhi := (boundary_source_user_cost_sharp_boxes).2.2
  have hnumHi :
      continuationReturn .L -
          pledgeability .H * liquidationValue <
        (8950531 / 10000000 : ℝ) := by
    dsimp [continuationReturn,
      ProposedStationaryRealScale.pledgeability,
      ProposedStationaryRealScale.liquidationValue,
      ProposedStationaryRealScale.capitalPrice]
    linarith only [huLhi]
  have hnumPos :
      0 < continuationReturn .L -
        pledgeability .H * liquidationValue := by
    have huLpos := ProposedStationaryRealScale.userCost_pos .L
    dsimp [continuationReturn,
      ProposedStationaryRealScale.pledgeability,
      ProposedStationaryRealScale.liquidationValue,
      ProposedStationaryRealScale.capitalPrice]
    linarith only [huLpos]
  have hpriceFormula :
      parentEffectivePrice .H =
        (24 / 25 : ℝ) *
          (userCost .H + (17 / 20 : ℝ) * liquidationValue) := by
    rw [parentEffectivePrice_identity .H]
    dsimp [continuationReturn, ProposedStationaryRealScale.pledgeability]
    ring
  have huHlo := (boundary_source_user_cost_sharp_boxes).1.1
  have hpriceLo :
      (8661847 / 10000000 : ℝ) < parentEffectivePrice .H := by
    rw [hpriceFormula]
    dsimp [ProposedStationaryRealScale.liquidationValue,
      ProposedStationaryRealScale.capitalPrice]
    linarith only [huHlo]
  have hcoefPosConst :
      (0 : ℝ) <
        (5677037 / 100000 : ℝ) *
          (5188263 / 100000000 : ℝ) := by norm_num
  have hprodUpper :
      firmCoefficient .H *
          (continuationReturn .L -
            pledgeability .H * liquidationValue) <
        ((5677037 / 100000 : ℝ) *
          (5188263 / 100000000 : ℝ)) *
            (8950531 / 10000000 : ℝ) := by
    calc
      _ < ((5677037 / 100000 : ℝ) *
            (5188263 / 100000000 : ℝ)) *
          (continuationReturn .L -
            pledgeability .H * liquidationValue) :=
        mul_lt_mul_of_pos_right hcoefHi hnumPos
      _ < _ := mul_lt_mul_of_pos_left hnumHi hcoefPosConst
  have hRpos : 0 < R := by norm_num [R]
  have hdenpos : 0 < R * parentEffectivePrice .H :=
    mul_pos hRpos (parentEffectivePrice_pos .H)
  have hdenlower :
      R * (8661847 / 10000000 : ℝ) <
        R * parentEffectivePrice .H :=
    mul_lt_mul_of_pos_left hpriceLo hRpos
  change (firmCoefficient .H *
      (continuationReturn .L -
        pledgeability .H * liquidationValue)) /
        (R * parentEffectivePrice .H) <
      (2957400 / 1000000 : ℝ)
  apply (div_lt_iff₀ hdenpos).2
  calc
    firmCoefficient .H *
        (continuationReturn .L -
          pledgeability .H * liquidationValue) <
      ((5677037 / 100000 : ℝ) *
          (5188263 / 100000000 : ℝ)) *
            (8950531 / 10000000 : ℝ) := hprodUpper
    _ < (2957400 / 1000000 : ℝ) *
        (R * (8661847 / 10000000 : ℝ)) := by
      norm_num [R]
    _ < (2957400 / 1000000 : ℝ) *
        (R * parentEffectivePrice .H) :=
      mul_lt_mul_of_pos_left hdenlower (by norm_num)

/-- SOURCE L-firm consumption sharp box, using SOURCE loan-price
correlations and the original stationary capital promise. -/
theorem source_narrow_right_firm_L_upper :
    normalizedFirmConsumption (1029136 / 1000000 : ℝ) .L <
      (3810560 / 1000000 : ℝ) := by
  let R : ℝ := 1029136 / 1000000
  let fL : ℝ := (81 / 80 : ℝ) *
    ((187 / 1200 : ℝ) -
      (377 / 3200 : ℝ) / ProposedStationaryBank.loanRate)
  have hloanpos : 0 < ProposedStationaryBank.loanRate :=
    ProposedStationaryRealScale.loanRate_pos
  have hloanhi := boundary_source_loan_rate_sharp_box.2
  have hfLscaled :
      fL * ProposedStationaryBank.loanRate =
        (81 / 80 : ℝ) *
          ((187 / 1200 : ℝ) * ProposedStationaryBank.loanRate -
            (377 / 3200 : ℝ)) := by
    dsimp [fL]
    field_simp [ne_of_gt hloanpos] <;> ring
  have hfLhi : fL < (3991617 / 100000000 : ℝ) := by
    by_contra hn
    have hge : (3991617 / 100000000 : ℝ) ≤ fL :=
      le_of_not_gt hn
    have hm := mul_le_mul_of_nonneg_right hge hloanpos.le
    rw [hfLscaled] at hm
    linarith only [hm, hloanhi]
  have hcoefFormula :
      firmCoefficient .L = capitalScale .L * fL := by
    dsimp [fL, firmCoefficient,
      ProposedStationaryRealScale.userCost,
      ProposedStationaryRealScale.pledgeability,
      ProposedStationaryRealScale.capitalPrice,
      ProposedStationaryRealScale.liquidationValue]
    field_simp [ne_of_gt hloanpos] <;> ring
  have hkLhi := (boundary_source_capital_scales_sharp_boxes).2.2
  have hkLpos := ProposedStationaryRealScale.capitalScale_pos .L
  have hcoefHi :
      firmCoefficient .L <
        (9431556 / 100000 : ℝ) *
          (3991617 / 100000000 : ℝ) := by
    rw [hcoefFormula]
    calc
      capitalScale .L * fL <
          capitalScale .L * (3991617 / 100000000 : ℝ) :=
        mul_lt_mul_of_pos_left hfLhi hkLpos
      _ < (9431556 / 100000 : ℝ) *
          (3991617 / 100000000 : ℝ) :=
        mul_lt_mul_of_pos_right hkLhi (by norm_num)
  have hRpos : 0 < R := by norm_num [R]
  have hdenpos : 0 < (24 / 25 : ℝ) * R :=
    mul_pos (by norm_num) hRpos
  change firmCoefficient .L / ((24 / 25 : ℝ) * R) <
    (3810560 / 1000000 : ℝ)
  apply (div_lt_iff₀ hdenpos).2
  calc
    firmCoefficient .L <
        (9431556 / 100000 : ℝ) *
          (3991617 / 100000000 : ℝ) := hcoefHi
    _ < (3810560 / 1000000 : ℝ) *
          ((24 / 25 : ℝ) * R) := by
      norm_num [R]

/-- The right narrow endpoint of the ORIGINAL SOURCE resource equation
has a strictly positive residual. Every sign used in the final
linear inequality is supplied by independently certified SOURCE
economic component boxes; no endpoint sign is a hypothesis. -/
theorem source_narrow_right_resource_residual_positive :
    0 < boundaryResourceResidual (1029136 / 1000000 : ℝ) := by
  have hY := source_narrow_right_normalized_output_lower
  have hW := source_narrow_right_worker_consumption_upper
  have hH := source_narrow_right_firm_H_upper
  have hL := source_narrow_right_firm_L_upper
  have hGamma := source_narrow_right_capital_cost_upper
  have hnorm :
      0 < normalizedResourceResidual (1029136 / 1000000 : ℝ) := by
    unfold normalizedResourceResidual
    linarith only [hY, hW, hH, hL, hGamma]
  exact narrow_right_positive_iff_normalized_positive.mpr hnorm

/-- Both narrow resource signs localize the one ROOT of the exact SOURCE
33-row reduced-prefix system in the one-micro-unit gross-rate bracket.
This is not a constructed full competitive equilibrium. -/
theorem source_reduced_prefix_rate_in_narrow_interval :
    (1029135 / 1000000 : ℝ) < boundarySourceRate ∧
      boundarySourceRate < (1029136 / 1000000 : ℝ) := by
  exact sourceBoundaryRate_in_narrow_rational_interval
    source_narrow_left_resource_residual_negative
    source_narrow_right_resource_residual_positive

#print axioms source_stationary_worker_scale_sharp_upper
#print axioms source_narrow_right_worker_consumption_upper
#print axioms source_narrow_right_capital_cost_upper
#print axioms source_narrow_right_firm_H_upper
#print axioms source_narrow_right_firm_L_upper
#print axioms source_narrow_right_resource_residual_positive
#print axioms source_reduced_prefix_rate_in_narrow_interval

end ProposedBoundaryNarrowRightResidualSign
end Ventura26LiquidityAllocation
