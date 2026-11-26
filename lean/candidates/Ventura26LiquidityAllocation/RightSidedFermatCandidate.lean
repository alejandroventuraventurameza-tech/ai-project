import Ventura26LiquidityAllocation.DateZeroCapitalEulerDerivativeCandidate
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Convex.Segment

/-!
# A right-sided Fermat inequality on the nonnegative real ray

At a local maximum restricted to nonnegative deviations, the ordinary
(two-sided) derivative is nonpositive, not necessarily zero. This is the
calculus ingredient for a binding-collateral entrepreneur's capital choice.
-/

namespace Ventura26LiquidityAllocation
namespace ProposedRightSidedFermat

open Filter Topology Set

/-- A maximizer among sufficiently small nonnegative deviations has
    a nonpositive right directional derivative at zero. -/
theorem hasDerivAt_nonpos_of_local_right_max
    (f : ℝ → ℝ) (d : ℝ)
    (hderiv : HasDerivAt f d 0)
    (hright : ∃ r : ℝ, 0 < r ∧
      ∀ x : ℝ, 0 ≤ x → x < r → f x ≤ f 0) :
    d ≤ 0 := by
  obtain ⟨r, hr, hbound⟩ := hright
  have hmax : IsLocalMaxOn f (Set.Ici (0 : ℝ)) 0 := by
    change ∀ᶠ x : ℝ in 𝓝[Set.Ici (0 : ℝ)] 0, f x ≤ f 0
    have hmem : Set.Iio r ∈ 𝓝 (0 : ℝ) :=
      isOpen_Iio.mem_nhds hr
    filter_upwards [mem_nhdsWithin_of_mem_nhds hmem,
      self_mem_nhdsWithin] with x hx hnonneg
    exact hbound x hnonneg hx
  have hy : (1 : ℝ) ∈ posTangentConeAt (Set.Ici (0 : ℝ)) 0 := by
    apply mem_posTangentConeAt_of_segment_subset
    intro x hx
    have hx' : x ∈ Set.Icc (0 : ℝ) 1 := by
      simpa [segment_eq_Icc (show (0 : ℝ) ≤ 1 by norm_num)] using hx
    exact hx'.1
  have hnegative := hmax.hasFDerivWithinAt_nonpos
    (hderiv.hasFDerivAt.hasFDerivWithinAt) hy
  simpa using hnegative

end ProposedRightSidedFermat
end Ventura26LiquidityAllocation
