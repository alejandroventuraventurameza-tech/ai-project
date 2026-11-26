import Ventura26LiquidityAllocation.SourceTwoDateBankShearBijectionCandidate

/-!
# SOURCE OTC slope invariance under reserve-rate translations

Unlike the reserve/deposit ratio, the SOURCE OTC deficit and
surplus slopes are unchanged when the realized reserve rate is
replaced with a monetary target, provided the corridor width,
matching intensity, and tightness are held fixed.

This is an exact algebraic fact about the ORIGINAL EconomicModel
otcNegotiatedRate, otcDeficitSlope and otcSurplusSlope definitions.
It does NOT prove these functions coincide with frozen Python's
specific matching-probability formulas. That is a separate task.
-/

namespace Ventura26LiquidityAllocation

/-- The SOURCE OTC deficit slope only depends on corridor width
and matching variables, not on the reserve-rate level. -/
theorem sourceOTCDeficitSlope_reserveRate_invariant
    (R T width intensity tightness : ℝ) :
    otcDeficitSlope R
      (otcNegotiatedRate R (R + width) intensity tightness)
      (R + width) intensity tightness =
    otcDeficitSlope T
      (otcNegotiatedRate T (T + width) intensity tightness)
      (T + width) intensity tightness := by
  unfold otcDeficitSlope otcNegotiatedRate
  ring

#print axioms sourceOTCDeficitSlope_reserveRate_invariant

/-- The SOURCE OTC surplus slope also depends only on corridor
width, matching intensity and tightness. -/
theorem sourceOTCSurplusSlope_reserveRate_invariant
    (R T width intensity tightness : ℝ) :
    otcSurplusSlope R
      (otcNegotiatedRate R (R + width) intensity tightness)
      intensity tightness =
    otcSurplusSlope T
      (otcNegotiatedRate T (T + width) intensity tightness)
      intensity tightness := by
  unfold otcSurplusSlope otcNegotiatedRate
  ring

#print axioms sourceOTCSurplusSlope_reserveRate_invariant

end Ventura26LiquidityAllocation
