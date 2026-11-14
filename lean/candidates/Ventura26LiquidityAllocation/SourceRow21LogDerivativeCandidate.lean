import Ventura26LiquidityAllocation.SourceCanonicalTwoPledgeLogBoundaryCandidate
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# SOURCE row 21: Frechet derivative of positive log-quotient at a root

First generic chain-rule gate. Unlike zero-set equivalence, this assertion
concerns the derivative of the log-quotient. The derivative of the
underlying ratio is an EXPLICIT hypothesis in this first candidate;
the next SOURCE-specific gate must establish it from J and V.
No economic root or inverse is supplied by this module.
-/

namespace Ventura26LiquidityAllocation
namespace ProposedLocalScalarAugmented34Source

theorem source_row21_log_ratio_fderiv_of_ratio_derivative
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (J V : E → ℝ) (x : E)
    (hpositive : 0 < V x)
    (hroot : J x = V x)
    (hratio : DifferentiableAt ℝ (fun y => J y / V y) x)
    (hratio_deriv :
      fderiv ℝ (fun y => J y / V y) x =
        (V x)⁻¹ • (fderiv ℝ J x - fderiv ℝ V x)) :
    fderiv ℝ (fun y => Real.log (J y / V y)) x =
      (V x)⁻¹ • (fderiv ℝ J x - fderiv ℝ V x) := by
  have hne : J x / V x ≠ 0 := by
    rw [hroot]
    exact ne_of_gt (by simpa using (div_self (ne_of_gt hpositive) : V x / V x = 1))
  rw [fderiv.log hratio hne, hratio_deriv]
  have hratio_one : J x / V x = 1 := by
    rw [hroot]
    exact div_self (ne_of_gt hpositive)
  rw [hratio_one]
  simp

#print axioms source_row21_log_ratio_fderiv_of_ratio_derivative

end ProposedLocalScalarAugmented34Source
end Ventura26LiquidityAllocation
