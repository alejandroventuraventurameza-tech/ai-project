import Ventura26LiquidityAllocation.Source33BankEconomicRowDispatchCandidate
import Ventura26LiquidityAllocation.SourceBankBalanceTwoPolicyJacobianShearCandidate

/-!
# Joint SOURCE banking derivative: three rows, two monetary policy channels

A single directional-derivative theorem combines certified SOURCE-style
loan, deposit and balance correction mechanisms at a COMMON zero of
the original reserve-rate and reserve-quantity policy residuals.

For one economic date the coefficients are:
  loan   +T*du
  deposit -C*T*du
  balance +B*du+A*dv.

The three source rows, monetary residual paths and four coefficient
paths are arbitrary differentiable real trajectories. Thus this proves
the product-rule shape in one dimension, not actual differentiability
of EconomicModel.localReducedPrefixResidual in all 33 coordinates.
Exact SOURCE off-root identities and 33-row dispatch are in imports;
their composition with a common economic chart is still open.
-/

namespace Ventura26LiquidityAllocation

/-- At a common monetary-rule root, the three banking rows have
the anticipated joint directional shear, with all economic
coefficients allowed to vary along the perturbation. -/
theorem sourceThreeBankRows_jointPolicyDirectionalDerivatives
    (loanSource depositSource bankSource C T A B u v : ℝ → ℝ)
    (x dLoan dDeposit dBank dC dT dA dB du dv : ℝ)
    (hLoan : HasDerivAt loanSource dLoan x)
    (hDeposit : HasDerivAt depositSource dDeposit x)
    (hBank : HasDerivAt bankSource dBank x)
    (hC : HasDerivAt C dC x)
    (hT : HasDerivAt T dT x)
    (hA : HasDerivAt A dA x)
    (hB : HasDerivAt B dB x)
    (hu : HasDerivAt u du x)
    (hv : HasDerivAt v dv x)
    (hrootU : u x = 0) (hrootV : v x = 0) :
    HasDerivAt
      (fun y => loanSource y + T y * (Real.exp (u y) - 1))
      (dLoan + T x * du) x ∧
    HasDerivAt
      (fun y => depositSource y -
        C y * (T y * (Real.exp (u y) - 1)))
      (dDeposit - C x * T x * du) x ∧
    HasDerivAt
      (fun y => bankSource y +
        A y * (Real.exp (v y) - 1) +
        B y * (Real.exp (u y) - 1))
      (dBank + A x * dv + B x * du) x := by
  rcases sourceBankPricingTarget_pair_hasDerivAt_at_policyRoot
    loanSource depositSource C T u
    x dLoan dDeposit dC dT du
    hLoan hDeposit hC hT hu hrootU with ⟨hL, hD⟩
  exact ⟨hL, hD, sourceBankBalance_twoPolicyShear_hasDerivAt_at_root
    bankSource A B u v x dBank dA dB du dv
    hBank hA hB hu hv hrootU hrootV⟩

#print axioms sourceThreeBankRows_jointPolicyDirectionalDerivatives

end Ventura26LiquidityAllocation
