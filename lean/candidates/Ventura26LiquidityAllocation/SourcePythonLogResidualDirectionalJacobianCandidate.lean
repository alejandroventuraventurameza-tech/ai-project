import Ventura26LiquidityAllocation.SourcePythonLogResidualZeroSetBridgeCandidate

/-!
# Directional Jacobian transport for original SOURCE level and Python log rows

SOURCE `localReducedRemainingResidual` uses a level difference A-B for
bank-face rollover and labor supply, and 1-A/B for the household deposit
Euler row. Original Python `remaining_residuals` uses log(A/B) for all three.

The previous module established equality of their ZERO SETS on the
strictly positive chart. This module establishes the precise FIRST-ORDER
row transformations at every common positive root along any one-dimensional
differentiable economic perturbation.

For bank/labor:
  derivative(log(A/B)) = derivative(A-B) / B
at A=B>0.

For deposit Euler:
  derivative(log(A/B)) = - derivative(1-A/B)
at A=B>0.

Proofs use ACTUAL Mathlib HasDerivAt.div, HasDerivAt.log,
HasDerivAt.sub and HasDerivAt.const_sub with no derivative
identities inserted as premises. We do assume differentiability
of the two economic numerator/denominator paths and the positive
root relation; those are NOT independently verified for all 33
SOURCE rows or for the Python double precision interpreter here.

No theorem in this file establishes a complete SOURCE/Python 33x33
Jacobian identity, numerical invertibility, root existence, fixed
policy IRF, or infinite-horizon competitive equilibrium.
-/

namespace Ventura26LiquidityAllocation

/-- Derivative of a Python-shaped logarithmic normalization at a
common positive SOURCE level root. This exact result remains valid
even when the endogenous denominator B varies with the perturbation. -/
theorem sourceLogRatio_hasDerivAt_of_common_positive_root
    (A B : ℝ → ℝ) (x a' b' : ℝ)
    (hA : HasDerivAt A a' x)
    (hB : HasDerivAt B b' x)
    (hroot : A x = B x)
    (hBpos : 0 < B x) :
    HasDerivAt (fun y => Real.log (A y / B y))
      ((a' - b') / B x) x := by
  have hBne : B x ≠ 0 := ne_of_gt hBpos
  have hquot : HasDerivAt (fun y => A y / B y)
      ((a' * B x - A x * b') / B x ^ 2) x :=
    hA.div hB hBne
  have hratio : A x / B x = 1 := by
    rw [hroot]
    exact div_self hBne
  have hratio_ne : A x / B x ≠ 0 := by
    rw [hratio]
    exact one_ne_zero
  have hlog := hquot.log hratio_ne
  have hscale :
      ((a' * B x - A x * b') / B x ^ 2) / (A x / B x) =
        (a' - b') / B x := by
    rw [hroot]
    field_simp [hBne]
    ring
  simpa only [hscale] using hlog

#print axioms sourceLogRatio_hasDerivAt_of_common_positive_root

/-- The economic SOURCE level residual and the Python log ratio
have derivatives related by a strictly positive nonzero scale. -/
theorem sourceLevelAndLog_hasDerivAt_at_common_root
    (A B : ℝ → ℝ) (x a' b' : ℝ)
    (hA : HasDerivAt A a' x)
    (hB : HasDerivAt B b' x)
    (hroot : A x = B x)
    (hBpos : 0 < B x) :
    HasDerivAt (fun y => A y - B y) (a' - b') x ∧
    HasDerivAt (fun y => Real.log (A y / B y))
      ((a' - b') / B x) x := by
  exact ⟨hA.sub hB,
    sourceLogRatio_hasDerivAt_of_common_positive_root
      A B x a' b' hA hB hroot hBpos⟩

#print axioms sourceLevelAndLog_hasDerivAt_at_common_root

/-- For the actual SOURCE deposit-Euler normalization 1-A/B,
the derivative of the Python-shaped log ratio is its negative at
any positive common root: there is NO additional unknown row scale. -/
theorem sourceEulerOneMinusRatioAndLog_hasDerivAt_at_common_root
    (A B : ℝ → ℝ) (x a' b' : ℝ)
    (hA : HasDerivAt A a' x)
    (hB : HasDerivAt B b' x)
    (hroot : A x = B x)
    (hBpos : 0 < B x) :
    HasDerivAt (fun y => 1 - A y / B y)
      (-(a' - b') / B x) x ∧
    HasDerivAt (fun y => Real.log (A y / B y))
      ((a' - b') / B x) x := by
  have hBne : B x ≠ 0 := ne_of_gt hBpos
  have hquot : HasDerivAt (fun y => A y / B y)
      ((a' * B x - A x * b') / B x ^ 2) x :=
    hA.div hB hBne
  have hsource := hquot.const_sub (1 : ℝ)
  have hscale :
      -((a' * B x - A x * b') / B x ^ 2) =
        -(a' - b') / B x := by
    rw [hroot]
    field_simp [hBne]
    ring
  constructor
  · simpa only [hscale] using hsource
  · exact sourceLogRatio_hasDerivAt_of_common_positive_root
      A B x a' b' hA hB hroot hBpos

#print axioms sourceEulerOneMinusRatioAndLog_hasDerivAt_at_common_root

/-- The positive bank/labor scale never creates or destroys a
zero directional derivative at the common economic root. -/
theorem sourceLevelAndLog_derivative_zero_iff
    (B x delta : ℝ) (hBpos : 0 < B) :
    (delta / B = 0) ↔ (delta = 0) := by
  simp [ne_of_gt hBpos]

#print axioms sourceLevelAndLog_derivative_zero_iff

end Ventura26LiquidityAllocation
