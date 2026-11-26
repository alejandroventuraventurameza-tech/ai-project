import Ventura26LiquidityAllocation.EconomicModel

/-!
# Constructing a transverse ray from the two Schur derivatives

This is a pure continuous-linear-map result on R x R. If the joint
derivative has negative values on both the policy axis and the
positive-slack axis, a POSITIVE transverse slope K can be constructed
such that the derivative on (-K,1) is strictly positive.

No arbitrary ray-existence assumption is needed. The certificate is
K=(1-a)/(-b) for a=L(0,1)<0 and b=L(1,0)<0; the ray derivative is
exactly one. Connecting L to the pinned economic Schur complement
remains the separate semantic/numerical validation obligation.
-/

namespace Ventura26LiquidityAllocation
namespace ProposedLocalScalarTransverseRayCertificate

/-- Continuous linearity identifies the mixed ray derivative with
the two source coefficients a_R and b. -/
theorem transverse_ray_value_eq
    (L : (ℝ × ℝ) →L[ℝ] ℝ) (K : ℝ) :
    L (-K, (1 : ℝ)) =
      L ((0 : ℝ), (1 : ℝ)) - K * L ((1 : ℝ), (0 : ℝ)) := by
  have hp :
      ((-K : ℝ), (1 : ℝ)) =
        (-K) • ((1 : ℝ), (0 : ℝ)) + ((0 : ℝ), (1 : ℝ)) := by
    ext <;> simp
  calc
    L (-K, (1 : ℝ)) =
        L ((-K) • ((1 : ℝ), (0 : ℝ)) + ((0 : ℝ), (1 : ℝ))) := by
      exact congrArg L hp
    _ = (-K) * L ((1 : ℝ), (0 : ℝ)) +
        L ((0 : ℝ), (1 : ℝ)) := by
      simp only [map_add, map_smul, smul_eq_mul]
    _ = L ((0 : ℝ), (1 : ℝ)) -
        K * L ((1 : ℝ), (0 : ℝ)) := by ring

/-- If both partials are negative, the exact ray K=(1-a)/(-b)
is positive and has a strictly positive directional derivative.
This constructs the scalar ray needed in the policy bifurcation proof. -/
theorem exists_positive_transverse_ray
    (L : (ℝ × ℝ) →L[ℝ] ℝ)
    (ha : L ((0 : ℝ), (1 : ℝ)) < 0)
    (hb : L ((1 : ℝ), (0 : ℝ)) < 0) :
    ∃ K : ℝ, 0 < K ∧ 0 < L (-K, (1 : ℝ)) := by
  let a : ℝ := L ((0 : ℝ), (1 : ℝ))
  let b : ℝ := L ((1 : ℝ), (0 : ℝ))
  let K : ℝ := (1 - a) / (-b)
  have hbpos : 0 < -b := neg_pos.mpr hb
  have hK : 0 < K := by
    dsimp [K]
    exact div_pos (by linarith only [ha]) hbpos
  have hKmul : K * (-b) = 1 - a := by
    dsimp [K]
    exact div_mul_cancel₀ (1 - a) (ne_of_gt hbpos)
  have hray := transverse_ray_value_eq L K
  refine ⟨K, hK, ?_⟩
  rw [hray]
  dsimp [a, b] at *
  nlinarith only [hKmul]

#print axioms transverse_ray_value_eq
#print axioms exists_positive_transverse_ray

end ProposedLocalScalarTransverseRayCertificate
end Ventura26LiquidityAllocation
