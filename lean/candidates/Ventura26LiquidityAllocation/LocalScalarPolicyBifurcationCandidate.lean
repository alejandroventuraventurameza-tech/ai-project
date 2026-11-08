import Ventura26LiquidityAllocation.LocalScalarShockSignCandidate

/-!
# Policy-rate perturbations: a genuinely parameterized two-root theorem

For the reduced complementarity M(s,h), a negative policy perturbation h<0
creates two LOCAL complementary roots, provided that:
* the policy-axis marginal M(0,h) has negative derivative at h=0;
* a ray s=-K*h has positive directional derivative at h=0;
* M(.,h) remains continuous and strictly decreasing on the local wedge.

The endpoint signs and positive interior root are DERIVED, not assumed.
No full equilibrium, root selection, global uniqueness, or continuous
equilibrium transition is asserted. The directional-ray premise must
ultimately be derived from the model's joint C^1 reduced map and the
Schur-complement derivatives.
-/

namespace Ventura26LiquidityAllocation
namespace ProposedLocalScalarPolicyBifurcation

open ProposedLocalScalarShockSign
open ProposedLocalScalarComplementarity
open ProposedScalarComplementarityMultiplicity

/-- An arbitrarily small negative policy innovation produces exactly two
complementary solutions in a *shrinking local wedge*. This is nonvacuous:
its assumptions imply existence of the positive interior root. -/
theorem negative_shock_creates_exactly_two_local_scalar_roots
    (M : ℝ → ℝ → ℝ) (a c K rho : ℝ)
    (hK : 0 < K) (hrho : 0 < rho)
    (hzero : M 0 0 = 0)
    (haxis : HasDerivAt (fun h => M 0 h) a 0)
    (ha : a < 0)
    (hray : HasDerivAt (fun h => M (-K * h) h) c 0)
    (hc : 0 < c)
    (hcont : ∀ h : ℝ, -rho < h → h < 0 →
      ContinuousOn (fun s => M s h) (Set.Icc (0 : ℝ) (-K * h)))
    (hanti : ∀ h : ℝ, -rho < h → h < 0 →
      StrictAntiOn (fun s => M s h) (Set.Icc (0 : ℝ) (-K * h))) :
    ∃ delta : ℝ, 0 < delta ∧ delta ≤ rho ∧
      ∀ h : ℝ, -delta < h → h < 0 →
        ∃ r : ℝ, 0 < r ∧ r < -K * h ∧ M r h = 0 ∧
          (∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) (-K * h) →
            (ScalarComplementarity (fun s => M s h) s ↔
              s = 0 ∨ s = r)) := by
  obtain ⟨d0, hd0, hleft, _hright⟩ :=
    negative_derivative_gives_opposite_local_signs
      (fun h => M 0 h) a hzero haxis ha
  have hrayzero : (fun h : ℝ => M (-K * h) h) 0 = 0 := by
    simpa using hzero
  obtain ⟨d1, hd1, hrayleft⟩ :=
    positive_derivative_gives_negative_left_sign
      (fun h => M (-K * h) h) c hrayzero hray hc
  let delta : ℝ := min rho (min d0 d1)
  have hdelta : 0 < delta := by
    dsimp [delta]
    exact lt_min hrho (lt_min hd0 hd1)
  refine ⟨delta, hdelta, by exact min_le_left .., ?_⟩
  intro h hlow hhigh
  have hlimrho : -rho < h := by
    have hbound : delta ≤ rho := min_le_left ..
    linarith
  have hlimd0 : -d0 < h := by
    have hbound : delta ≤ d0 :=
      (min_le_right rho (min d0 d1)).trans (min_le_left d0 d1)
    linarith
  have hlimd1 : -d1 < h := by
    have hbound : delta ≤ d1 :=
      (min_le_right rho (min d0 d1)).trans (min_le_right d0 d1)
    linarith
  have heps : 0 < -K * h := by
    have hh : 0 < -h := neg_pos.mpr hhigh
    have hp : 0 < K * (-h) := mul_pos hK hh
    nlinarith only [hp]
  exact local_scalar_complementarity_exactly_two_of_crossing
    (fun s => M s h) (-K * h) heps
    (hcont h hlimrho hhigh) (hanti h hlimrho hhigh)
    (hleft h hlimd0 hhigh) (hrayleft h hlimd1 hhigh)

/-- A positive policy perturbation has no complementary scalar solution
on the indicated local interval, if the same reduced marginal is strictly
decreasing there. Neither statement excludes remote solutions. -/
theorem positive_shock_has_no_local_scalar_root
    (M : ℝ → ℝ → ℝ) (a rho eps : ℝ)
    (hrho : 0 < rho) (heps : 0 < eps)
    (hzero : M 0 0 = 0)
    (haxis : HasDerivAt (fun h => M 0 h) a 0)
    (ha : a < 0)
    (hanti : ∀ h : ℝ, 0 < h → h < rho →
      StrictAntiOn (fun s => M s h) (Set.Icc (0 : ℝ) eps)) :
    ∃ delta : ℝ, 0 < delta ∧ delta ≤ rho ∧
      ∀ h : ℝ, 0 < h → h < delta →
        ¬ ∃ s : ℝ, s ∈ Set.Icc (0 : ℝ) eps ∧
          ScalarComplementarity (fun s => M s h) s := by
  obtain ⟨d0, hd0, _hleft, hright⟩ :=
    negative_derivative_gives_opposite_local_signs
      (fun h => M 0 h) a hzero haxis ha
  let delta : ℝ := min rho d0
  have hdelta : 0 < delta := lt_min hrho hd0
  refine ⟨delta, hdelta, by exact min_le_left .., ?_⟩
  intro h hpos hsmall
  have hrhoh : h < rho := lt_of_lt_of_le hsmall (min_le_left ..)
  have hd0h : h < d0 := lt_of_lt_of_le hsmall (min_le_right ..)
  exact no_local_scalar_complementarity_of_negative_boundary
    (fun s => M s h) eps
    (hanti h hpos hrhoh) (hright h hpos hd0h)

#print axioms negative_shock_creates_exactly_two_local_scalar_roots
#print axioms positive_shock_has_no_local_scalar_root

end ProposedLocalScalarPolicyBifurcation
end Ventura26LiquidityAllocation
