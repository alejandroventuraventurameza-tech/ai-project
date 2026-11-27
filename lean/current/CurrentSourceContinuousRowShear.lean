import Ventura26LiquidityAllocation.CurrentSourceContinuousRootCoefficient
import Mathlib.Analysis.Calculus.FDeriv.Add

/-!
# Continuous-coefficient Fréchet transport for SOURCE monetary-bank rows

The genuine SOURCE six-row two-date shear has four bank-pricing rows
with ONE policy-rate donor and two bank-balance rows with TWO policy
donors (reserve-rate and reserve-quantity). Both types are covered.

At a common root, derivatives of all donor residuals exist by
hypothesis. The cross coefficients need ONLY be continuous; we do
NOT assume or derive their derivatives.

This is a generic calculus module specialized to the exact algebraic
shape of the SOURCE rows. It does not yet prove that all eight
economic SOURCE cross-coefficients are continuous on the chosen chart,
that the full original economic 33 residual is differentiable, or
that the original Jacobian is invertible.
-/

namespace Ventura26LiquidityAllocation
namespace CurrentSourceContinuousRowShear

open CurrentSourceContinuousRootCoefficient

/-- A genuine SOURCE pricing row is a residual plus a
state-dependent coefficient times the monetary-rate residual.
At a common root, continuity of this coefficient is sufficient. -/
theorem continuous_one_donor_row_hasFDerivAt
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (a f g : X → ℝ) (x : X)
    (Jf Jg : X →L[ℝ] ℝ)
    (ha : ContinuousAt a x)
    (hf : HasFDerivAt f Jf x)
    (hg : HasFDerivAt g Jg x)
    (hroot : f x = 0) :
    HasFDerivAt (fun y => g y + a y * f y)
      (Jg + (a x) • Jf) x := by
  exact hg.add
    (continuous_scalar_mul_hasFDerivAt_at_zero a f x Jf ha hf hroot)

#print axioms continuous_one_donor_row_hasFDerivAt

/-- The two genuine SOURCE balance rows each use TWO distinct
donors (rate and quantity). Neither coefficient needs a derivative
when both donor residuals vanish at the common SOURCE root. -/
theorem continuous_two_donor_row_hasFDerivAt
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (a b f k g : X → ℝ) (x : X)
    (Jf Jk Jg : X →L[ℝ] ℝ)
    (ha : ContinuousAt a x)
    (hb : ContinuousAt b x)
    (hf : HasFDerivAt f Jf x)
    (hk : HasFDerivAt k Jk x)
    (hg : HasFDerivAt g Jg x)
    (hrootF : f x = 0)
    (hrootK : k x = 0) :
    HasFDerivAt
      (fun y => (g y + a y * f y) + b y * k y)
      ((Jg + (a x) • Jf) + (b x) • Jk) x := by
  exact
    (continuous_one_donor_row_hasFDerivAt
      a f g x Jf Jg ha hf hg hrootF).add
    (continuous_scalar_mul_hasFDerivAt_at_zero
      b k x Jk hb hk hrootK)

#print axioms continuous_two_donor_row_hasFDerivAt

end CurrentSourceContinuousRowShear
end Ventura26LiquidityAllocation
