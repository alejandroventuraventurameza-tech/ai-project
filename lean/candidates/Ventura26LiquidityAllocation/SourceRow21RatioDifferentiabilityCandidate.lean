import Ventura26LiquidityAllocation.SourceRow21LogDerivativeCandidate

/-!
# SOURCE row 21: remove the quotient-differentiability premise

This first strengthening replaces an ASSUMED differentiability of J/V
with the standard quotient rule under differentiability of J and V
and the positivity of V at the point. The explicit quotient derivative
formula is still an independent premise, and will be discharged next.
-/

namespace Ventura26LiquidityAllocation
namespace ProposedLocalScalarAugmented34Source

theorem source_row21_log_ratio_fderiv_of_constituent_regularities
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (J V : E → ℝ) (x : E)
    (hJ : DifferentiableAt ℝ J x)
    (hV : DifferentiableAt ℝ V x)
    (hpositive : 0 < V x)
    (hroot : J x = V x)
    (hratio_deriv :
      fderiv ℝ (fun y => J y / V y) x =
        (V x)⁻¹ • (fderiv ℝ J x - fderiv ℝ V x)) :
    fderiv ℝ (fun y => Real.log (J y / V y)) x =
      (V x)⁻¹ • (fderiv ℝ J x - fderiv ℝ V x) := by
  have hratio : DifferentiableAt ℝ (fun y => J y / V y) x :=
    hJ.div hV (ne_of_gt hpositive)
  exact source_row21_log_ratio_fderiv_of_ratio_derivative
    J V x hpositive hroot hratio hratio_deriv

#print axioms source_row21_log_ratio_fderiv_of_constituent_regularities

end ProposedLocalScalarAugmented34Source
end Ventura26LiquidityAllocation
