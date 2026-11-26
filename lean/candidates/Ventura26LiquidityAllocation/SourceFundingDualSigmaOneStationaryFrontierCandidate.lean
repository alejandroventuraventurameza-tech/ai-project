import Ventura26LiquidityAllocation.SourceFundingDualFourLogCoordinatesCandidate
import Ventura26LiquidityAllocation.LocalScalarDualSigmaOneBridgeCandidate

/-!
# Genuine SOURCE 34th funding dual: sigma=1 stationary four-log simplification

At a common positive stationary baseline consumption (C0L=C1L),
unit baseline inflation, and unit entrepreneur CRRA curvature,
the genuine SOURCE normalized L funding dual simplifies to a
two-exponential expression. This is the analytic scalar FORMULA
whose value is enclosed rationally in the Python-frontier diagnostic.

It is conditional on the explicitly displayed SOURCE primitives,
not a proof that Python steady_case populates an exact Lean Primitives
and LocalPrefixCoordinates instance, and not a full 34-root theorem.
-/

namespace Ventura26LiquidityAllocation

variable {S : Type*} [Fintype S] [DecidableEq S]

theorem sourceFundingDual_sigmaOne_stationary_fourLog
    (P : Primitives S) (Z0 : LocalPrefixCoordinates)
    (z : Fin 33 → ℝ)
    (hsigma : P.entrepreneurRiskAversion = 1)
    (hc_same : Z0.controlsZero.consumptionL = Z0.controlsOne.consumptionL)
    (hc_positive : 0 < Z0.controlsZero.consumptionL)
    (hpi : Z0.controlsOne.inflation = 1) :
    localNormalizedCollateralDualL P (localPrefixLogChart Z0 z) =
      1 / (Z0.controlsZero.loanRate * Real.exp (z (15 : Fin 33))) -
        P.entrepreneurDiscount * Real.exp (z (8 : Fin 33)) /
          (Real.exp (z (24 : Fin 33)) * Real.exp (z (28 : Fin 33))) := by
  rw [sourceFundingDual_four_log_coordinate_formula, hsigma]
  simp only [Real.rpow_neg_one]
  rw [← hc_same, hpi]
  have hc : Z0.controlsZero.consumptionL ≠ 0 :=
    ne_of_gt hc_positive
  have he8 : Real.exp (z (8 : Fin 33)) ≠ 0 :=
    Real.exp_ne_zero _
  have he24 : Real.exp (z (24 : Fin 33)) ≠ 0 :=
    Real.exp_ne_zero _
  have he28 : Real.exp (z (28 : Fin 33)) ≠ 0 :=
    Real.exp_ne_zero _
  field_simp [hc, he8, he24, he28]

#print axioms sourceFundingDual_sigmaOne_stationary_fourLog

end Ventura26LiquidityAllocation
