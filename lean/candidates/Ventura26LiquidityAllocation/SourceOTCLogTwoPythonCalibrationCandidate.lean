import Ventura26LiquidityAllocation.SourceOTCReserveRateTranslationInvariantCandidate

/-!
# OTC SOURCE / frozen-Python calibration bridge on the low-tightness branch

In frozen finite_irf.py, aa=.5, match_value = 1/(1+sqrt(2-tightness)),
cm = width*(1-aa+aa*match_value),
cp = width*tightness*aa*match_value.
SOURCE uses lambda with 1-exp(-lambda) as a match share and a piecewise
corridor weight. At lambda=log 2 and tightness <= 1 the definitions agree.

This module proves matching-component and slope equality, NOT an
unrestricted SOURCE/Python identification for tightness>1 and NOT
equilibrium regularity.
-/

namespace Ventura26LiquidityAllocation

/-- The calibrated SOURCE match share equals the frozen Python aa=.5. -/
theorem sourceOTC_logTwo_matchShare :
    otcMatchIntensityShare (Real.log 2) = (1 / 2 : ℝ) := by
  unfold otcMatchIntensityShare
  rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  norm_num

#print axioms sourceOTC_logTwo_matchShare

/-- SOURCE's low-tightness corridor weight equals the explicit
Python match_value when the matching intensity is log 2. -/
theorem sourceOTC_logTwo_corridorWeight
    (tightness : ℝ) (ht : tightness ≤ 1) :
    otcCorridorWeight (Real.log 2) tightness =
      1 / (1 + Real.sqrt (2 - tightness)) := by
  simp only [otcCorridorWeight, if_pos ht,
    Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  congr 1
  ring

#print axioms sourceOTC_logTwo_corridorWeight

/-- Deficit OTC slope agrees with the frozen Python chi_minus formula
on tightness <= 1 at the explicitly calibrated matching intensity. -/
theorem sourceOTC_logTwo_deficitSlope_pythonFormula
    (R width tightness : ℝ) (ht : tightness ≤ 1) :
    otcDeficitSlope R
      (otcNegotiatedRate R (R + width) (Real.log 2) tightness)
      (R + width) (Real.log 2) tightness =
    width * (1 - (1 / 2 : ℝ) +
      (1 / 2 : ℝ) / (1 + Real.sqrt (2 - tightness))) := by
  unfold otcDeficitSlope otcNegotiatedRate otcDeficitMatchFraction
  rw [if_pos ht, sourceOTC_logTwo_matchShare,
    sourceOTC_logTwo_corridorWeight tightness ht]
  ring

#print axioms sourceOTC_logTwo_deficitSlope_pythonFormula

/-- Surplus OTC slope agrees with the frozen Python chi_plus formula,
under the same low-tightness and log-two calibration contract. -/
theorem sourceOTC_logTwo_surplusSlope_pythonFormula
    (R width tightness : ℝ) (ht : tightness ≤ 1) :
    otcSurplusSlope R
      (otcNegotiatedRate R (R + width) (Real.log 2) tightness)
      (Real.log 2) tightness =
    width * tightness * (1 / 2 : ℝ) /
      (1 + Real.sqrt (2 - tightness)) := by
  unfold otcSurplusSlope otcNegotiatedRate otcSurplusMatchFraction
  rw [if_pos ht, sourceOTC_logTwo_matchShare,
    sourceOTC_logTwo_corridorWeight tightness ht]
  ring

#print axioms sourceOTC_logTwo_surplusSlope_pythonFormula

end Ventura26LiquidityAllocation
