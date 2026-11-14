import Ventura26LiquidityAllocation.SourceRow21EconomicFrechetBridgeCandidate

/-!
# Positive-root log quotient: Frechet identity without quotient-derivative hypothesis

The previous candidates assumed the quotient derivative formula. Here
the proof instead uses the *actual* Mathlib derivatives of log J and
log V, and a neighborhood identity Real.log (J/V) = log J - log V.
The only hypotheses are differentiability of the two real-valued
functions, strict positivity of the denominator at the root, and the
root identity J = V. No quotient derivative is assumed.

This abstract lemma is not a SOURCE equilibrium existence theorem.
-/

namespace Ventura26LiquidityAllocation
namespace ProposedLocalScalarAugmented34Source

theorem source_row21_log_ratio_fderiv_at_positive_root
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (J V : E → ℝ) (x : E)
    (hJ : DifferentiableAt ℝ J x)
    (hV : DifferentiableAt ℝ V x)
    (hpositive : 0 < V x)
    (hroot : J x = V x) :
    fderiv ℝ (fun y => Real.log (J y / V y)) x =
      (V x)⁻¹ • (fderiv ℝ J x - fderiv ℝ V x) := by
  have hJne : J x ≠ 0 := by
    rw [hroot]
    exact ne_of_gt hpositive
  have hVne : V x ≠ 0 := ne_of_gt hpositive
  have hJevent : ∀ᶠ y in 𝓝 x, J y ≠ 0 :=
    hJ.continuousAt.eventually (isOpen_ne.mem_nhds hJne)
  have hVevent : ∀ᶠ y in 𝓝 x, V y ≠ 0 :=
    hV.continuousAt.eventually (isOpen_ne.mem_nhds hVne)
  have hlocal :
      (fun y => Real.log (J y / V y)) =ᶠ[𝓝 x]
        (fun y => Real.log (J y) - Real.log (V y)) := by
    filter_upwards [hJevent, hVevent] with y hj hv
    exact Real.log_div hj hv
  calc
    fderiv ℝ (fun y => Real.log (J y / V y)) x =
        fderiv ℝ (fun y => Real.log (J y) - Real.log (V y)) x :=
      hlocal.fderiv_eq
    _ = (J x)⁻¹ • fderiv ℝ J x - (V x)⁻¹ • fderiv ℝ V x := by
      rw [fderiv_fun_sub (hJ.log hJne) (hV.log hVne),
          fderiv.log hJ hJne, fderiv.log hV hVne]
    _ = (V x)⁻¹ • (fderiv ℝ J x - fderiv ℝ V x) := by
      rw [hroot, smul_sub]

#print axioms source_row21_log_ratio_fderiv_at_positive_root

end ProposedLocalScalarAugmented34Source
end Ventura26LiquidityAllocation
