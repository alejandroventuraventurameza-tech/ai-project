import Mathlib.Analysis.Calculus.Deriv.Slope
import Ventura26LiquidityAllocation.LocalScalarDerivativeBridgeCandidate

/-!
# First-order transversality: signs on either side of zero

A strictly negative derivative at a zero of a real function forces
positive function values immediately to the left and negative values
immediately to the right. This is a local consequence of the
definition of derivative, not an assumption about an entire interval.

The lemma will be reused for the policy axis h |-> M(0,h) and for
transversal rays h |-> M(-K*h,h) of the actual scalar reduced map.
-/

namespace Ventura26LiquidityAllocation
namespace ProposedLocalScalarShockSign

/-- A negative first derivative at a zero gives the correct sign on
BOTH sides of the origin, with a *single* positive radius.
No monotonicity away from the origin is required. -/
theorem negative_derivative_gives_opposite_local_signs
    (f : ℝ → ℝ) (a : ℝ)
    (hf0 : f 0 = 0)
    (hder : HasDerivAt f a 0) (ha : a < 0) :
    ∃ delta : ℝ, 0 < delta ∧
      (∀ h : ℝ, -delta < h → h < 0 → 0 < f h) ∧
      (∀ h : ℝ, 0 < h → h < delta → f h < 0) := by
  have hslope : Filter.Tendsto
      (fun h : ℝ => (f h - f 0) / (h - 0))
      (𝓝[≠] (0 : ℝ)) (𝓝 a) := by
    simpa only [slope_fun_def_field] using hder.tendsto_slope
  have hneg : ∀ᶠ h in 𝓝[≠] (0 : ℝ),
      (f h - f 0) / (h - 0) < 0 :=
    hslope.eventually_lt_const ha
  have hneighborhood : ∀ᶠ h in 𝓝 (0 : ℝ),
      h ≠ 0 → (f h - f 0) / (h - 0) < 0 := by
    simpa using (eventually_nhdsWithin_iff.mp hneg)
  rcases Metric.eventually_nhds_iff.mp hneighborhood with
    ⟨delta, hdelta, hsign⟩
  refine ⟨delta, hdelta, ?_, ?_⟩
  · intro h hlow hhigh
    have hd : dist h (0 : ℝ) < delta := by
      rw [Real.dist_eq, sub_zero, abs_of_neg hhigh]
      linarith
    have hratio : f h / h < 0 := by
      simpa only [hf0, sub_zero] using hsign h hd (ne_of_lt hhigh)
    rcases div_neg_iff.mp hratio with ⟨hpositive, _⟩ | ⟨_, hpositive⟩
    · exact hpositive
    · exact False.elim ((not_lt_of_ge hhigh.le) hpositive)
  · intro h hlow hhigh
    have hd : dist h (0 : ℝ) < delta := by
      rw [Real.dist_eq, sub_zero, abs_of_pos hlow]
      exact hhigh
    have hratio : f h / h < 0 := by
      simpa only [hf0, sub_zero] using hsign h hd (ne_of_gt hlow)
    rcases div_neg_iff.mp hratio with ⟨_, hnegative⟩ | ⟨hnegative, _⟩
    · exact False.elim ((not_lt_of_ge hlow.le) hnegative)
    · exact hnegative

/-- A positive derivative at a zero gives a negative response to
a sufficiently small negative shock. -/
theorem positive_derivative_gives_negative_left_sign
    (f : ℝ → ℝ) (c : ℝ)
    (hf0 : f 0 = 0)
    (hder : HasDerivAt f c 0) (hc : 0 < c) :
    ∃ delta : ℝ, 0 < delta ∧
      ∀ h : ℝ, -delta < h → h < 0 → f h < 0 := by
  have hnegder : HasDerivAt (fun x => -f x) (-c) 0 := hder.neg
  have hzero : (fun x : ℝ => -f x) 0 = 0 := by simp [hf0]
  obtain ⟨delta, hdelta, hleft, _hright⟩ :=
    negative_derivative_gives_opposite_local_signs (fun x => -f x)
      (-c) hzero hnegder (neg_neg_of_pos hc)
  refine ⟨delta, hdelta, ?_⟩
  intro h hlow hhigh
  have hvalue : 0 < -f h := hleft h hlow hhigh
  linarith

#print axioms negative_derivative_gives_opposite_local_signs
#print axioms positive_derivative_gives_negative_left_sign

end ProposedLocalScalarShockSign
end Ventura26LiquidityAllocation
