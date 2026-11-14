import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Ventura26LiquidityAllocation.LocalScalarComplementarityCandidate

/-!
# Derivative-level criterion for LOCAL complementarity multiplicity

The reduced marginal's negative derivative on the open interval (0, eps)
implies strict antitonicity on the CLOSED interval [0, eps], provided
the marginal is continuous on that closed interval. Combined with
opposite signs at the endpoints, this gives two and only two LOCAL
complementary scalar solutions.

The sign of the Schur-complement derivative is a premise here. The
independent numerical estimate of its value does not constitute a
Lean proof of this premise for the actual economic residual.
-/

namespace Ventura26LiquidityAllocation
namespace ProposedLocalScalarDerivativeBridge

open ProposedScalarComplementarityMultiplicity
open ProposedLocalScalarComplementarity

/-- A derivative-based sufficient condition for the local, two-branch
scalar conclusion. Unlike the original global candidate, only
derivative signs on (0, eps) are required. -/
theorem local_complementarity_two_of_negative_derivative
    (M : ℝ → ℝ) (eps : ℝ)
    (heps : 0 < eps)
    (hcont : ContinuousOn M (Set.Icc (0 : ℝ) eps))
    (hderiv : ∀ s ∈ Set.Ioo (0 : ℝ) eps, deriv M s < 0)
    (hM0 : 0 < M 0) (hMeps : M eps < 0) :
    ∃ r : ℝ, 0 < r ∧ r < eps ∧ M r = 0 ∧
      (∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) eps →
        (ScalarComplementarity M s ↔ s = 0 ∨ s = r)) := by
  have hanti : StrictAntiOn M (Set.Icc (0 : ℝ) eps) := by
    apply strictAntiOn_of_deriv_neg (convex_Icc (0 : ℝ) eps) hcont
    intro s hs
    exact hderiv s (by simpa only [interior_Icc] using hs)
  exact local_scalar_complementarity_exactly_two_of_crossing
    M eps heps hcont hanti hM0 hMeps

/-- Negative derivative and negative marginal at zero exclude LOCAL
complementary solutions. Global nonexistence is not asserted. -/
theorem local_complementarity_none_of_negative_derivative
    (M : ℝ → ℝ) (eps : ℝ)
    (hcont : ContinuousOn M (Set.Icc (0 : ℝ) eps))
    (hderiv : ∀ s ∈ Set.Ioo (0 : ℝ) eps, deriv M s < 0)
    (hM0 : M 0 < 0) :
    ¬ ∃ s : ℝ, s ∈ Set.Icc (0 : ℝ) eps ∧
      ScalarComplementarity M s := by
  have hanti : StrictAntiOn M (Set.Icc (0 : ℝ) eps) := by
    apply strictAntiOn_of_deriv_neg (convex_Icc (0 : ℝ) eps) hcont
    intro s hs
    exact hderiv s (by simpa only [interior_Icc] using hs)
  exact no_local_scalar_complementarity_of_negative_boundary
    M eps hanti hM0

#print axioms local_complementarity_two_of_negative_derivative
#print axioms local_complementarity_none_of_negative_derivative

end ProposedLocalScalarDerivativeBridge
end Ventura26LiquidityAllocation
