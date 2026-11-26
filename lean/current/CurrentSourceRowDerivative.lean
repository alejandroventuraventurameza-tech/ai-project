import Mathlib

/-!
# Scalar derivative of a state-dependent SOURCE row shear

This preliminary lemma isolates the derivative contribution of a single
state-dependent cross-row coefficient. It does NOT identify a 33x33
SOURCE Jacobian or establish existence of a SOURCE root.
-/

namespace Ventura26LiquidityAllocation
namespace CurrentSourceRowDerivative

/-- At a zero of the cross-row residual, the derivative of a
state-dependent triangular row shear has no derivative-of-coefficient
contribution. This is a one-dimensional lemma, not the full 33x33
economic Jacobian transport. -/
theorem scalar_row_shear_hasDerivAt_at_cross_root
    (a f g : ℝ → ℝ) (x da df dg : ℝ)
    (ha : HasDerivAt a da x)
    (hf : HasDerivAt f df x)
    (hg : HasDerivAt g dg x)
    (hroot : f x = 0) :
    HasDerivAt (fun y => g y + a y * f y) (dg + a x * df) x := by
  have h := hg.add (ha.mul hf)
  simpa only [hroot, mul_zero, zero_add] using h

#print axioms scalar_row_shear_hasDerivAt_at_cross_root

end CurrentSourceRowDerivative
end Ventura26LiquidityAllocation
