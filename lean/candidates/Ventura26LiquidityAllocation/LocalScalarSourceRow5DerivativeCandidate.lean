import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Ventura26LiquidityAllocation.EconomicModel

/-!
# Exact first-order source/legacy collateral row orientation

The legacy finite_bridge.py binding row uses log(coverage), where
coverage = faceL / (pledgeable capital value).
The current source EconomicModel.lean uses 1-coverage-s in row 5.
For any differentiable coverage path with coverage = 1 at the
boundary, the two state derivatives are NEGATIVES.

This is an analytic first-order bridge only, not an identification of
the complete legacy and source Jacobians on a neighborhood. It also
does not claim the 33-row Jacobian or inverse has been certified.
-/

namespace Ventura26LiquidityAllocation
namespace ProposedLocalScalarSourceRow5Derivative

/-- At the exact collateral frontier, the derivative of normalized
slack `1-u` is minus that of the legacy logarithmic coverage row. -/
theorem log_coverage_and_normalized_slack_opposite_derivatives
    (u : ℝ → ℝ) (t d : ℝ)
    (hu : u t = 1)
    (hdu : HasDerivAt u d t) :
    HasDerivAt (fun x => 1 - u x) (-d) t ∧
    HasDerivAt (fun x => Real.log (u x)) d t := by
  constructor
  · exact hdu.const_sub 1
  · have hlog : HasDerivAt (fun x => Real.log (u x)) (d / u t) t :=
      hdu.log (by simp [hu])
    simpa only [hu, div_one] using hlog

/-- The independent prescribed normalized slack parameter s enters
the exact source row as `-s` with derivative -1. -/
theorem normalized_slack_direct_parameter_derivative
    (coverage : ℝ) :
    HasDerivAt (fun s : ℝ => 1 - coverage - s) (-1) 0 := by
  simpa using (hasDerivAt_id (0 : ℝ)).const_sub (1 - coverage)

#print axioms log_coverage_and_normalized_slack_opposite_derivatives
#print axioms normalized_slack_direct_parameter_derivative

end ProposedLocalScalarSourceRow5Derivative
end Ventura26LiquidityAllocation
