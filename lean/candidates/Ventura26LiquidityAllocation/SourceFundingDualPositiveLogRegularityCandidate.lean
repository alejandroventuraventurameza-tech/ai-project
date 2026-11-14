import Ventura26LiquidityAllocation.SourceFundingDualFourLogCoordinatesCandidate
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# Actual SOURCE funding-dual regularity on the positive 33-log chart

Unlike the first 33 binding residual rows, the last SOURCE augmented
residual is an explicit function of four economic coordinates:
L consumption at dates 0 and 1, the date-zero loan rate, and the
date-one inflation rate. The positive log chart allows the last
SOURCE row to be differentiated without assuming regularity of
the entire economic equilibrium or its continuation operator.

This result proves no derivative sign, root or Jacobian inverse.
-/

namespace Ventura26LiquidityAllocation

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- The genuine SOURCE normalized L funding dual is Frechet
differentiable at every log-coordinate vector if the real 33-coordinate
base chart is strictly positive. No C1 assumption is imported here. -/
theorem sourceFundingDual_differentiableAt_positive_log
    (P : Primitives S) (Z0 : LocalPrefixCoordinates)
    (hZ0 : LocalPrefixCoordinatesPositive Z0)
    (z : Fin 33 → ℝ) :
    DifferentiableAt ℝ
      (fun w : Fin 33 → ℝ =>
        localNormalizedCollateralDualL P (localPrefixLogChart Z0 w)) z := by
  let r0 : (Fin 33 → ℝ) → ℝ :=
    fun w => Z0.controlsZero.loanRate * Real.exp (w 15)
  let c0 : (Fin 33 → ℝ) → ℝ :=
    fun w => Z0.controlsZero.consumptionL * Real.exp (w 8)
  let c1 : (Fin 33 → ℝ) → ℝ :=
    fun w => Z0.controlsOne.consumptionL * Real.exp (w 24)
  let pi1 : (Fin 33 → ℝ) → ℝ :=
    fun w => Z0.controlsOne.inflation * Real.exp (w 28)
  have hr0_base : 0 < Z0.controlsZero.loanRate := by
    simpa [localPrefixCoordinatesVector] using hZ0 (15 : Fin 33)
  have hc0_base : 0 < Z0.controlsZero.consumptionL := by
    simpa [localPrefixCoordinatesVector] using hZ0 (8 : Fin 33)
  have hc1_base : 0 < Z0.controlsOne.consumptionL := by
    simpa [localPrefixCoordinatesVector] using hZ0 (24 : Fin 33)
  have hpi1_base : 0 < Z0.controlsOne.inflation := by
    simpa [localPrefixCoordinatesVector] using hZ0 (28 : Fin 33)
  have hr0_pos : 0 < r0 z :=
    mul_pos hr0_base (Real.exp_pos (z 15))
  have hc0_pos : 0 < c0 z :=
    mul_pos hc0_base (Real.exp_pos (z 8))
  have hc1_pos : 0 < c1 z :=
    mul_pos hc1_base (Real.exp_pos (z 24))
  have hpi1_pos : 0 < pi1 z :=
    mul_pos hpi1_base (Real.exp_pos (z 28))
  have hdr0 : DifferentiableAt ℝ r0 z := by
    dsimp [r0]
    fun_prop
  have hdc0 : DifferentiableAt ℝ c0 z := by
    dsimp [c0]
    fun_prop
  have hdc1 : DifferentiableAt ℝ c1 z := by
    dsimp [c1]
    fun_prop
  have hdpi1 : DifferentiableAt ℝ pi1 z := by
    dsimp [pi1]
    fun_prop
  have hpow0 : DifferentiableAt ℝ
      (fun w => (c0 w) ^ (-P.entrepreneurRiskAversion)) z :=
    hdc0.rpow_const (Or.inl (ne_of_gt hc0_pos))
  have hpow1 : DifferentiableAt ℝ
      (fun w => (c1 w) ^ (-P.entrepreneurRiskAversion)) z :=
    hdc1.rpow_const (Or.inl (ne_of_gt hc1_pos))
  have hpow0_pos : 0 < (c0 z) ^ (-P.entrepreneurRiskAversion) :=
    Real.rpow_pos_of_pos hc0_pos _
  have hone : DifferentiableAt ℝ
      (fun _w : Fin 33 → ℝ => (1 : ℝ)) z :=
    differentiableAt_const (1 : ℝ)
  have hfirst : DifferentiableAt ℝ
      (fun w => (1 : ℝ) / r0 w) z :=
    hone.div hdr0 (ne_of_gt hr0_pos)
  have hmiddle : DifferentiableAt ℝ
      (fun w => P.entrepreneurDiscount *
        (c1 w) ^ (-P.entrepreneurRiskAversion) /
        (c0 w) ^ (-P.entrepreneurRiskAversion)) z :=
    ((differentiableAt_const P.entrepreneurDiscount).mul hpow1).div
      hpow0 (ne_of_gt hpow0_pos)
  have hlast : DifferentiableAt ℝ
      (fun w => (P.entrepreneurDiscount *
        (c1 w) ^ (-P.entrepreneurRiskAversion) /
        (c0 w) ^ (-P.entrepreneurRiskAversion)) / pi1 w) z :=
    hmiddle.div hdpi1 (ne_of_gt hpi1_pos)
  have hformula :
      (fun w : Fin 33 → ℝ =>
        localNormalizedCollateralDualL P (localPrefixLogChart Z0 w)) =
      (fun w => (1 : ℝ) / r0 w -
        (P.entrepreneurDiscount *
          (c1 w) ^ (-P.entrepreneurRiskAversion) /
          (c0 w) ^ (-P.entrepreneurRiskAversion)) / pi1 w) := by
    funext w
    exact sourceFundingDual_four_log_coordinate_formula P Z0 w
  rw [hformula]
  exact hfirst.sub hlast

#print axioms sourceFundingDual_differentiableAt_positive_log

end Ventura26LiquidityAllocation
