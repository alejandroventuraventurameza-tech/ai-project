import Ventura26LiquidityAllocation.SourceThreeBankRowsPythonOTCRootParityCandidate

/-!
# First-order off-root monetary correction at a common policy root

For a state-dependent policy target T(y) and a SOURCE monetary-rule
residual u(y), the correction T(y) * (exp(u(y))-1) has derivative
T(x) * du at any common root u(x)=0. The derivative of T cancels
because exp(0)-1=0.

For an additional state-dependent bank coefficient C(y), the
derivative of C(y)*T(y)*(exp(u(y))-1) equals C(x)*T(x)*du.

This establishes the analytic product-rule mechanism needed for
SOURCE loan/deposit row shears. It is not yet an identification of
the full economic SOURCE/Python Jacobian, which additionally needs
a common chart and differentiability of the actual source primitives.
-/

namespace Ventura26LiquidityAllocation

/-- The target rate's own derivative does not enter the
first-order correction at the common monetary-rule root. -/
theorem sourceMonetaryExponentialGap_hasDerivAt_at_root
    (T u : ℝ → ℝ) (x dT du : ℝ)
    (hT : HasDerivAt T dT x)
    (hu : HasDerivAt u du x)
    (hroot : u x = 0) :
    HasDerivAt (fun y => T y * (Real.exp (u y) - 1))
      (T x * du) x := by
  have hexp := hu.exp
  have hgap : HasDerivAt
      (fun y => Real.exp (u y) - 1)
      (Real.exp (u x) * du) x := hexp.sub_const 1
  have hprod := hT.mul hgap
  convert hprod using 1 <;> simp [hroot] <;> ring

#print axioms sourceMonetaryExponentialGap_hasDerivAt_at_root

/-- With an additional state-dependent coefficient C, both its
derivative and the derivative of the rate target vanish from the
first-order product rule at a monetary-rule root. -/
theorem sourceMonetaryWeightedGap_hasDerivAt_at_root
    (C T u : ℝ → ℝ) (x dC dT du : ℝ)
    (hC : HasDerivAt C dC x)
    (hT : HasDerivAt T dT x)
    (hu : HasDerivAt u du x)
    (hroot : u x = 0) :
    HasDerivAt (fun y =>
        C y * (T y * (Real.exp (u y) - 1)))
      (C x * T x * du) x := by
  have hgap := sourceMonetaryExponentialGap_hasDerivAt_at_root
    T u x dT du hT hu hroot
  have hprod := hC.mul hgap
  convert hprod using 1 <;> simp [hroot] <;> ring

#print axioms sourceMonetaryWeightedGap_hasDerivAt_at_root

end Ventura26LiquidityAllocation
