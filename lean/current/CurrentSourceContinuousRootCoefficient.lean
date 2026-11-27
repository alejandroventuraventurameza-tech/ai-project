import Ventura26LiquidityAllocation.CurrentSourceFiveBankTargetization
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Asymptotics.Lemmas

/-!
# Root-only Fréchet regularity with continuous scalar bank coefficients

This general calculus lemma explains why a continuous, not necessarily
differentiable, scalar coefficient is sufficient to transport the
derivative of a residual that vanishes at the basepoint.

The economic SOURCE six-row targetization uses cross-coefficient times
monetary residuals. This theorem is an ANALYTIC BRIDGE; it does NOT
establish continuity of the eight specific economic cross-coefficients,
differentiability of the 33 original SOURCE rows, or an inverse Jacobian.
-/

namespace Ventura26LiquidityAllocation
namespace CurrentSourceContinuousRootCoefficient

open Filter
open Asymptotics
open scoped Topology

/-- If f(x)=0, the derivative of a(y)*f(y) at x only requires
CONTINUITY of a, not the existence of a derivative of a.
The derivative is the frozen coefficient a(x) times Df(x). -/
theorem continuous_scalar_mul_hasFDerivAt_at_zero
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (a f : X → ℝ) (x : X) (J : X →L[ℝ] ℝ)
    (ha : ContinuousAt a x)
    (hf : HasFDerivAt f J x)
    (hzero : f x = 0) :
    HasFDerivAt (fun y => a y * f y) ((a x) • J) x := by
  have hc : ContinuousAt (fun _y : X => a x) x :=
    continuousAt_const
  have ha0 :
      Tendsto (fun y : X => a y - a x) (𝓝 x) (𝓝 (0 : ℝ)) := by
    simpa only [sub_self] using (ha.sub hc).tendsto
  have hsmall :
      (fun y : X => a y - a x) =o[𝓝 x]
        (fun _y : X => (1 : ℝ)) :=
    (isLittleO_one_iff ℝ).2 ha0
  have hbig :
      (fun y : X => f y - f x) =O[𝓝 x]
        (fun y : X => y - x) := hf.isBigO_sub
  have hcross :
      (fun y : X => (a y - a x) * (f y - f x)) =o[𝓝 x]
        (fun y : X => y - x) := by
    simpa only [smul_eq_mul, one_smul] using
      hsmall.smul_isBigO hbig
  have herror :
      (fun y : X => f y - f x - J (y - x)) =o[𝓝 x]
        (fun y : X => y - x) := hf.isLittleO
  have hconst :
      (fun y : X => (a x) * (f y - f x - J (y - x))) =o[𝓝 x]
        (fun y : X => y - x) := by
    simpa only [smul_eq_mul] using
      herror.const_smul_left (a x)
  have hsum := hcross.add hconst
  apply HasFDerivAt.of_isLittleO
  convert hsum using 1
  funext y
  change a y * f y - a x * f x - a x * J (y - x) =
    (a y - a x) * (f y - f x) +
      a x * (f y - f x - J (y - x))
  simp only [hzero, mul_zero, sub_zero]
  ring

#print axioms continuous_scalar_mul_hasFDerivAt_at_zero

end CurrentSourceContinuousRootCoefficient
end Ventura26LiquidityAllocation
