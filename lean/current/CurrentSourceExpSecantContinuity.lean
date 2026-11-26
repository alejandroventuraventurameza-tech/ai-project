import Ventura26LiquidityAllocation.CurrentSourceFiveBankTargetization
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.NhdsWithin

/-!
# SOURCE exponential secant: continuity at the monetary-policy root

The SOURCE targetization uses the exact continuous extension
    expSecant u = (exp u - 1) / u when u != 0,
    expSecant 0 = 1.

The point u=0 occurs at the certified stationary SOURCE root,
so merely unfolding this piecewise formula does NOT justify
differentiation of the banking shear there.

Here we formally derive continuity from the ordinary derivative of
the exponential at zero and the punctured-neighborhood slope limit.
This is a first step towards replacing the unnecessarily strong
differentiability assumption on the entire bank-row coefficient map
by continuity at the SOURCE root.

No statement about full SOURCE differentiability, Jacobian
invertibility, Python equality or an economic IRF is made.
-/

namespace Ventura26LiquidityAllocation
namespace CurrentSourceFiveBankBridge

open Filter
open scoped Topology

/-- The exact SOURCE divided exponential difference is continuous at
zero; its special value is correctly chosen as the derivative exp'(0)=1. -/
theorem expSecant_continuousAt_zero :
    ContinuousAt expSecant (0 : ℝ) := by
  have hderiv : HasDerivAt Real.exp 1 (0 : ℝ) := by
    simpa using Real.hasDerivAt_exp (0 : ℝ)
  have hslope :
      Tendsto
        (fun t : ℝ => t⁻¹ * (Real.exp t - 1))
        (𝓝[≠] (0 : ℝ)) (𝓝 (1 : ℝ)) := by
    simpa [zero_add, Real.exp_zero, smul_eq_mul]
      using hderiv.tendsto_slope_zero
  have heq :
      (fun t : ℝ => t⁻¹ * (Real.exp t - 1)) =ᶠ[𝓝[≠] (0 : ℝ)]
        expSecant := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    have ht0 : t ≠ 0 := by
      simpa using ht
    simp [expSecant, ht0, div_eq_mul_inv, mul_comm]
  have hlim :
      Tendsto expSecant (𝓝[≠] (0 : ℝ)) (𝓝 (1 : ℝ)) :=
    Filter.Tendsto.congr' heq hslope
  have hzero : expSecant (0 : ℝ) = 1 := by
    simp [expSecant]
  apply (continuousAt_iff_punctured_nhds).2
  simpa only [hzero] using hlim

#print axioms expSecant_continuousAt_zero

/-- Composition with a continuous monetary-rule residual that
vanishes at a SOURCE root preserves continuity of the divided
exponential difference; no derivative of the secant is required. -/
theorem expSecant_comp_continuousAt_at_zero
    {X : Type*} [TopologicalSpace X]
    (u : X → ℝ) (x : X)
    (hu : ContinuousAt u x)
    (hroot : u x = 0) :
    ContinuousAt (fun y => expSecant (u y)) x := by
  have he : ContinuousAt expSecant (u x) := by
    simpa [hroot] using expSecant_continuousAt_zero
  exact he.comp hu

#print axioms expSecant_comp_continuousAt_at_zero

end CurrentSourceFiveBankBridge
end Ventura26LiquidityAllocation
