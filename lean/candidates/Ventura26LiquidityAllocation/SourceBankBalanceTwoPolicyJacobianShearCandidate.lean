import Ventura26LiquidityAllocation.SourceBankPricingTargetJacobianShearCandidate

/-!
# SOURCE banking balance: two monetary-rule derivatives at a common root

The exact original SOURCE bank-balance realized/target decomposition
(sourceEconomicBankBalance_twoPolicyTarget_gap) has TWO channels:
- quantity policy rule: k(realized R) * N * (exp(v)-1)
- rate policy rule: (N*d*c / (realized R * rhoR * rhoT)) * (exp(u)-1)
where u,v are rate and quantity rule residuals, respectively.

This theorem takes the two coefficients A(y), B(y) as arbitrary
differentiable paths; that makes the product-rule calculation
correct even if rate, deposits, OTC tightness, or target ratio vary.
At a common root u(x)=v(x)=0, derivatives of A and B vanish.

CAUTION: This is a directional derivative lemma for the algebraic
correction, not a 33-dimensional SOURCE/Python Jacobian equality.
-/

namespace Ventura26LiquidityAllocation

/-- Exact first-order balance correction under simultaneous
rate and quantity monetary-rule residuals, including variable
coefficients and derivatives. -/
theorem sourceBankBalance_twoPolicyShear_hasDerivAt_at_root
    (bankSource A B u v : ℝ → ℝ)
    (x dBank dA dB du dv : ℝ)
    (hBank : HasDerivAt bankSource dBank x)
    (hA : HasDerivAt A dA x)
    (hB : HasDerivAt B dB x)
    (hu : HasDerivAt u du x)
    (hv : HasDerivAt v dv x)
    (hrootU : u x = 0)
    (hrootV : v x = 0) :
    HasDerivAt
      (fun y => bankSource y +
        A y * (Real.exp (v y) - 1) +
        B y * (Real.exp (u y) - 1))
      (dBank + A x * dv + B x * du) x := by
  have hQty := sourceMonetaryExponentialGap_hasDerivAt_at_root
    A v x dA dv hA hv hrootV
  have hRate := sourceMonetaryExponentialGap_hasDerivAt_at_root
    B u x dB du hB hu hrootU
  exact (hBank.add hQty).add hRate

#print axioms sourceBankBalance_twoPolicyShear_hasDerivAt_at_root

end Ventura26LiquidityAllocation
