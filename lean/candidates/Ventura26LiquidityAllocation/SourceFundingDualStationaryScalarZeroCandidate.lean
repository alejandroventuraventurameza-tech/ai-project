import Ventura26LiquidityAllocation.SourceFundingDualSigmaOneStationaryFrontierCandidate

/-!
# Exact scalar binding of the SOURCE L funding dual by log loan rate

Under an explicit positive steady SOURCE chart, entrepreneur sigma=1,
and equal stationary L consumption, ONE funding-dual equation can be
set to zero by changing ONLY the log loan-rate coordinate 15.

This is NOT the existence of a 34-equation SOURCE equilibrium:
the other 33 equations generally change with that coordinate. It is
also not a numerical scalar interval certificate or a proof of
cross-language SOURCE/Python semantic equality.
-/
namespace Ventura26LiquidityAllocation

variable {S : Type*} [Fintype S] [DecidableEq S]

theorem sourceFundingDual_scalar_zero_by_adjusting_log_loan_rate
    (P : Primitives S) (Z0 : LocalPrefixCoordinates)
    (z : Fin 33 → ℝ)
    (hsigma : P.entrepreneurRiskAversion = 1)
    (hc_same : Z0.controlsZero.consumptionL = Z0.controlsOne.consumptionL)
    (hc_positive : 0 < Z0.controlsZero.consumptionL)
    (hpi : Z0.controlsOne.inflation = 1)
    (hr : 0 < Z0.controlsZero.loanRate)
    (hbeta : 0 < P.entrepreneurDiscount) :
    ∃ z' : Fin 33 → ℝ,
      (∀ i : Fin 33, i ≠ (15 : Fin 33) → z' i = z i) ∧
      localNormalizedCollateralDualL P (localPrefixLogChart Z0 z') = 0 := by
  let R : ℝ := Z0.controlsZero.loanRate
  let rhs : ℝ := P.entrepreneurDiscount * Real.exp (z (8 : Fin 33)) /
      (Real.exp (z (24 : Fin 33)) * Real.exp (z (28 : Fin 33)))
  have hrhs : 0 < rhs := by
    dsimp [rhs]
    positivity
  have hchoose : 0 < 1 / (R * rhs) :=
    one_div_pos.mpr (mul_pos hr hrhs)
  let z' : Fin 33 → ℝ :=
    Function.update z (15 : Fin 33) (Real.log (1 / (R * rhs)))
  refine ⟨z', ?_, ?_⟩
  · intro i hi
    exact Function.update_of_ne hi _ _
  · rw [sourceFundingDual_sigmaOne_stationary_fourLog
        P Z0 z' hsigma hc_same hc_positive hpi]
    have h8 : z' (8 : Fin 33) = z (8 : Fin 33) := by
      simp [z']
    have h24 : z' (24 : Fin 33) = z (24 : Fin 33) := by
      simp [z']
    have h28 : z' (28 : Fin 33) = z (28 : Fin 33) := by
      simp [z']
    have h15 : z' (15 : Fin 33) = Real.log (1 / (R * rhs)) := by
      simp [z']
    rw [h8, h24, h28, h15, Real.exp_log hchoose]
    change 1 / (R * (1 / (R * rhs))) - rhs = 0
    have hrne : R ≠ 0 := ne_of_gt hr
    have hrsne : rhs ≠ 0 := ne_of_gt hrhs
    field_simp [hrne, hrsne] <;> ring

#print axioms sourceFundingDual_scalar_zero_by_adjusting_log_loan_rate

end Ventura26LiquidityAllocation
