import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Prod
import Ventura26LiquidityAllocation.LocalScalarPolicyBifurcationCandidate

/-!
# Joint differentiability -> policy-axis and transverse-ray derivatives

Unlike the preceding parametric theorem, this bridge does not treat
the two directional derivatives as independent primitives. They are
the evaluations of ONE joint Frechet derivative of M(s,h) at (0,0)
on the policy and ray directions, respectively.

The source model still needs C^1 regularity plus an interval where
the s-slice is strictly decreasing. HasFDerivAt at one point alone
does not establish that interval or solve the 33 economic equations.
-/

namespace Ventura26LiquidityAllocation
namespace ProposedLocalScalarJointDerivativeBridge

open ProposedLocalScalarPolicyBifurcation
open ProposedScalarComplementarityMultiplicity

/-- The actual one-dimensional derivatives used for the two sign changes
are both restrictions of the same joint Frechet derivative. -/
theorem joint_fderiv_gives_policy_and_ray_derivatives
    (M : ℝ → ℝ → ℝ)
    (L : (ℝ × ℝ) →L[ℝ] ℝ) (K : ℝ)
    (hjoint : HasFDerivAt (fun z : ℝ × ℝ => M z.1 z.2) L
      ((0 : ℝ), (0 : ℝ))) :
    HasDerivAt (fun h : ℝ => M 0 h) (L ((0 : ℝ), (1 : ℝ))) 0 ∧
    HasDerivAt (fun h : ℝ => M (-K * h) h)
      (L (-K, (1 : ℝ))) 0 := by
  have haxisPath : HasDerivAt
      (fun h : ℝ => ((0 : ℝ), h))
      ((0 : ℝ), (1 : ℝ)) 0 :=
    (hasDerivAt_const (0 : ℝ) (0 : ℝ)).prodMk (hasDerivAt_id (0 : ℝ))
  have hleft : HasDerivAt
      (fun h : ℝ => -K * h) (-K) 0 := by
    simpa only [mul_one, id_eq] using
      ((hasDerivAt_id (0 : ℝ)).const_mul (-K))
  have hrayPath : HasDerivAt
      (fun h : ℝ => (-K * h, h))
      (-K, (1 : ℝ)) 0 :=
    hleft.prodMk (hasDerivAt_id (0 : ℝ))
  constructor
  · simpa only [Function.comp_def] using
      hjoint.comp_hasDerivAt_of_eq (0 : ℝ) haxisPath (by simp)
  · simpa only [Function.comp_def] using
      hjoint.comp_hasDerivAt_of_eq (0 : ℝ) hrayPath (by simp)

/-- Joint differentiability and signed directional evaluations imply
existence of the interior root, provided the s-slices satisfy the
explicit local continuity and antitonicity conditions. -/
theorem negative_shock_two_roots_from_joint_derivative
    (M : ℝ → ℝ → ℝ) (L : (ℝ × ℝ) →L[ℝ] ℝ)
    (K rho : ℝ)
    (hK : 0 < K) (hrho : 0 < rho)
    (hzero : M 0 0 = 0)
    (hjoint : HasFDerivAt (fun z : ℝ × ℝ => M z.1 z.2) L
      ((0 : ℝ), (0 : ℝ)))
    (ha : L ((0 : ℝ), (1 : ℝ)) < 0)
    (hc : 0 < L (-K, (1 : ℝ)))
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
  obtain ⟨haxis, hray⟩ :=
    joint_fderiv_gives_policy_and_ray_derivatives M L K hjoint
  exact negative_shock_creates_exactly_two_local_scalar_roots
    M (L ((0 : ℝ), (1 : ℝ))) (L (-K, (1 : ℝ))) K rho
    hK hrho hzero haxis ha hray hc hcont hanti

/-- The same joint derivative excludes local complementary roots for
a positive shock whenever the s-slice is strictly decreasing there. -/
theorem positive_shock_no_root_from_joint_derivative
    (M : ℝ → ℝ → ℝ) (L : (ℝ × ℝ) →L[ℝ] ℝ)
    (rho eps : ℝ)
    (hrho : 0 < rho) (heps : 0 < eps)
    (hzero : M 0 0 = 0)
    (hjoint : HasFDerivAt (fun z : ℝ × ℝ => M z.1 z.2) L
      ((0 : ℝ), (0 : ℝ)))
    (ha : L ((0 : ℝ), (1 : ℝ)) < 0)
    (hanti : ∀ h : ℝ, 0 < h → h < rho →
      StrictAntiOn (fun s => M s h) (Set.Icc (0 : ℝ) eps)) :
    ∃ delta : ℝ, 0 < delta ∧ delta ≤ rho ∧
      ∀ h : ℝ, 0 < h → h < delta →
        ¬ ∃ s : ℝ, s ∈ Set.Icc (0 : ℝ) eps ∧
          ScalarComplementarity (fun s => M s h) s := by
  obtain ⟨haxis, _hray⟩ :=
    joint_fderiv_gives_policy_and_ray_derivatives M L 1 hjoint
  exact positive_shock_has_no_local_scalar_root
    M (L ((0 : ℝ), (1 : ℝ))) rho eps
    hrho heps hzero haxis ha hanti

#print axioms joint_fderiv_gives_policy_and_ray_derivatives
#print axioms negative_shock_two_roots_from_joint_derivative
#print axioms positive_shock_no_root_from_joint_derivative

end ProposedLocalScalarJointDerivativeBridge
end Ventura26LiquidityAllocation
