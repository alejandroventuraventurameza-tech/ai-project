import Ventura26LiquidityAllocation.SourceMonetaryExponentialGapDerivativeCandidate

/-!
# Root derivative shear for SOURCE loan and deposit policy-target rows

The ORIGINAL SOURCE to frozen-Python bank pricing cross-row identities
have the functional shape

  loanTarget(y) = loanSOURCE(y) + T(y)*(exp(u(y))-1)
  depositTarget(y) = depositSOURCE(y)
      - C(y)*T(y)*(exp(u(y))-1),

where u is the original SOURCE reserve-rate policy residual and
C includes deposit-rate, OTC spread, payment shock and both rate
denominators. This module gives the exact directional derivative
result with all state-dependent factors differentiated, evaluated at
u(x)=0. The economic SOURCE-to-Python functional identities and
differentiability assumptions on the actual 33-coordinate chart
are NOT established by the generic theorem.
-/

namespace Ventura26LiquidityAllocation

/-- The first-order loan-pricing target substitution adds the
SOURCE monetary rate-rule derivative with coefficient T(x). -/
theorem sourceLoanTargetRow_hasDerivAt_at_policyRoot
    (loanSource T u : ℝ → ℝ)
    (x dLoan dT du : ℝ)
    (hLoan : HasDerivAt loanSource dLoan x)
    (hT : HasDerivAt T dT x)
    (hu : HasDerivAt u du x)
    (hroot : u x = 0) :
    HasDerivAt
      (fun y => loanSource y + T y * (Real.exp (u y) - 1))
      (dLoan + T x * du) x := by
  exact hLoan.add
    (sourceMonetaryExponentialGap_hasDerivAt_at_root
      T u x dT du hT hu hroot)

#print axioms sourceLoanTargetRow_hasDerivAt_at_policyRoot

/-- The first-order deposit-pricing target substitution subtracts
the policy rate-rule derivative with state-dependent coefficient
C(x)*T(x). Product-rule terms in dC and dT vanish at the root. -/
theorem sourceDepositTargetRow_hasDerivAt_at_policyRoot
    (depositSource C T u : ℝ → ℝ)
    (x dDeposit dC dT du : ℝ)
    (hDeposit : HasDerivAt depositSource dDeposit x)
    (hC : HasDerivAt C dC x)
    (hT : HasDerivAt T dT x)
    (hu : HasDerivAt u du x)
    (hroot : u x = 0) :
    HasDerivAt
      (fun y => depositSource y -
        C y * (T y * (Real.exp (u y) - 1)))
      (dDeposit - C x * T x * du) x := by
  exact hDeposit.sub
    (sourceMonetaryWeightedGap_hasDerivAt_at_root
      C T u x dC dT du hC hT hu hroot)

#print axioms sourceDepositTargetRow_hasDerivAt_at_policyRoot

/-- Joint directional derivative of the loan and deposit targets,
sharing the SAME economic policy-rate rule residual. -/
theorem sourceBankPricingTarget_pair_hasDerivAt_at_policyRoot
    (loanSource depositSource C T u : ℝ → ℝ)
    (x dLoan dDeposit dC dT du : ℝ)
    (hLoan : HasDerivAt loanSource dLoan x)
    (hDeposit : HasDerivAt depositSource dDeposit x)
    (hC : HasDerivAt C dC x)
    (hT : HasDerivAt T dT x)
    (hu : HasDerivAt u du x)
    (hroot : u x = 0) :
    HasDerivAt
      (fun y => loanSource y + T y * (Real.exp (u y) - 1))
      (dLoan + T x * du) x ∧
    HasDerivAt
      (fun y => depositSource y -
        C y * (T y * (Real.exp (u y) - 1)))
      (dDeposit - C x * T x * du) x := by
  exact ⟨sourceLoanTargetRow_hasDerivAt_at_policyRoot
    loanSource T u x dLoan dT du hLoan hT hu hroot,
    sourceDepositTargetRow_hasDerivAt_at_policyRoot
      depositSource C T u x dDeposit dC dT du
      hDeposit hC hT hu hroot⟩

#print axioms sourceBankPricingTarget_pair_hasDerivAt_at_policyRoot

end Ventura26LiquidityAllocation
