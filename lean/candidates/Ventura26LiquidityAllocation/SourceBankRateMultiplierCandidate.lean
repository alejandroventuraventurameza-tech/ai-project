import Ventura26LiquidityAllocation.SourceBankTwoTargetCrossRowCandidate

/-!
# Banking reserve/deposit multiplier: realized versus policy-target rate

An algebraic bridge for the reciprocal reserve/deposit ratio as a
function of the reserve-rate argument. This file does not identify the
original Python auxiliary or certify the full SOURCE/Python residual
transformation.

Keep reserve rates and both reserve/deposit ratios nonzero when
clearing denominators. The exact zero-rate limits are not asserted.
-/

namespace Ventura26LiquidityAllocation

/-- Abstract reserve/deposit ratio when the deposit rate, reserve
requirement and payment/tightness factor are held fixed. -/
noncomputable def sourceBankRatioAtRate
    (a depositRate paymentFactor reserveRate : ℝ) : ℝ :=
  a + (depositRate / reserveRate - a) * paymentFactor

/-- Exact realized-rate versus target-rate difference in the
reserve/deposit ratio. Only reserve rates must be nonzero. -/
theorem sourceBankRatioAtRate_gap
    (a d c R T : ℝ) (hR : R ≠ 0) (hT : T ≠ 0) :
    sourceBankRatioAtRate a d c R -
      sourceBankRatioAtRate a d c T =
      d * c * (T - R) / (R * T) := by
  unfold sourceBankRatioAtRate
  field_simp [hR, hT]
  ring

#print axioms sourceBankRatioAtRate_gap

/-- The bank multiplier k(r) = 1/rho(r) - 1. -/
noncomputable def sourceBankMultiplierAtRate
    (a d c r : ℝ) : ℝ :=
  1 / sourceBankRatioAtRate a d c r - 1

/-- Exact multiplier gap: it vanishes at a common realized/target
reserve rate, assuming the required positive-domain or nonzero
denominator conditions have been checked separately. -/
theorem sourceBankMultiplierAtRate_gap
    (a d c R T : ℝ)
    (hR : R ≠ 0) (hT : T ≠ 0)
    (hRhoR : sourceBankRatioAtRate a d c R ≠ 0)
    (hRhoT : sourceBankRatioAtRate a d c T ≠ 0) :
    sourceBankMultiplierAtRate a d c R -
      sourceBankMultiplierAtRate a d c T =
      d * c * (R - T) /
        (R * T * sourceBankRatioAtRate a d c R *
          sourceBankRatioAtRate a d c T) := by
  unfold sourceBankMultiplierAtRate
  have hgap := sourceBankRatioAtRate_gap a d c R T hR hT
  field_simp [hR, hT, hRhoR, hRhoT] at hgap ⊢
  linear_combination -hgap

#print axioms sourceBankMultiplierAtRate_gap

/-- At the same rate, the target and realized multipliers agree;
this does not establish that Python's auxiliary uses this multiplier. -/
theorem sourceBankMultiplierAtRate_same
    (a d c R : ℝ) :
    sourceBankMultiplierAtRate a d c R -
      sourceBankMultiplierAtRate a d c R = 0 := by
  ring

#print axioms sourceBankMultiplierAtRate_same

end Ventura26LiquidityAllocation
