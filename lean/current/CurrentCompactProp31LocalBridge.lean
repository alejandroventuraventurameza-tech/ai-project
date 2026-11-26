import Ventura26LiquidityAllocation.LocalScalarJointDerivativeBridgeCandidate
import Ventura26LiquidityAllocation.LocalScalarTransverseRayCertificateCandidate

/-!
# Current compact paper, Proposition 3.1: unified two-sign scalar bridge

The paper assumes M is C^1 near (0,0), M(0,0)=0, and strictly
negative partial derivatives in both scalar slack and reserve-rate shock.
This theorem discharges a substantial part of the proposed proof:
joint derivative signs give a transverse ray, a positive interior root
is *constructed* by the intermediate value theorem for small negative
shocks, exactly two complementary roots remain locally, and small
positive shocks admit no local complementary root.

HONEST LIMIT: uniform local antitonicity/continuity of the s-slices
is still an explicit premise here. The paper's C^1 hypothesis should
supply this premise; that remaining C^1 -> local-slice bridge must be
formalized and kernel-checked before declaring Proposition 3.1
fully proved. No economic equilibrium is claimed.
-/

namespace Ventura26LiquidityAllocation
namespace CurrentCompactProp31

open ProposedLocalScalarJointDerivativeBridge
open ProposedLocalScalarTransverseRayCertificate
open ProposedScalarComplementarityMultiplicity

/-- Signed derivatives and uniformly regular local slack slices yield
both shock-sign conclusions with one common shock radius. The interior
root is an OUTPUT of the theorem, not an input. -/
theorem prop31_local_two_signs_of_joint_derivative_and_slices
    (M : ℝ → ℝ → ℝ)
    (L : (ℝ × ℝ) →L[ℝ] ℝ)
    (rho eps : ℝ)
    (hrho : 0 < rho)
    (heps : 0 < eps)
    (hzero : M 0 0 = 0)
    (hjoint : HasFDerivAt
      (fun z : ℝ × ℝ => M z.1 z.2) L ((0 : ℝ), (0 : ℝ)))
    (hb : L ((1 : ℝ), (0 : ℝ)) < 0)
    (ha : L ((0 : ℝ), (1 : ℝ)) < 0)
    (hregular : ∀ h : ℝ, -rho < h → h < rho →
       ContinuousOn (fun s => M s h) (Set.Icc (0 : ℝ) eps) ∧
       StrictAntiOn (fun s => M s h) (Set.Icc (0 : ℝ) eps)) :
    ∃ K : ℝ, 0 < K ∧
      ∃ delta : ℝ, 0 < delta ∧
        (∀ h : ℝ, -delta < h → h < 0 →
          ∃ r : ℝ, 0 < r ∧ r < -K * h ∧ M r h = 0 ∧
            (∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) (-K * h) →
              (ScalarComplementarity (fun x => M x h) s ↔
                s = 0 ∨ s = r))) ∧
        (∀ h : ℝ, 0 < h → h < delta →
          ¬ ∃ s : ℝ, s ∈ Set.Icc (0 : ℝ) eps ∧
            ScalarComplementarity (fun x => M x h) s) := by
  obtain ⟨K, hK, hc⟩ := exists_positive_transverse_ray L ha hb
  let rhoK : ℝ := min rho (eps / (K + 1))
  have hden : 0 < K + 1 := by linarith
  have hrhoK : 0 < rhoK := lt_min hrho (div_pos heps hden)
  have hregion : ∀ h : ℝ, -rhoK < h → h < 0 →
      -rho < h ∧ h < rho ∧ -K * h ≤ eps := by
    intro h hlow hneg
    have hlowrho : -rho < h := by
      have hle : rhoK ≤ rho := min_le_left ..
      linarith
    have hhighrho : h < rho := lt_trans hneg hrho
    have hbound : -h < eps / (K + 1) := by
      have hle : rhoK ≤ eps / (K + 1) := min_le_right ..
      linarith
    have hprod : (-h) * (K + 1) < eps :=
      (lt_div_iff₀ hden).mp hbound
    refine ⟨hlowrho, hhighrho, ?_⟩
    nlinarith only [hprod, hneg]
  have hcontK : ∀ h : ℝ, -rhoK < h → h < 0 →
      ContinuousOn (fun s => M s h) (Set.Icc (0 : ℝ) (-K * h)) := by
    intro h hlow hneg
    obtain ⟨hlowrho, hhighrho, hcap⟩ := hregion h hlow hneg
    exact (hregular h hlowrho hhighrho).1.mono (by
      intro s hs
      exact ⟨hs.1, hs.2.trans hcap⟩)
  have hantiK : ∀ h : ℝ, -rhoK < h → h < 0 →
      StrictAntiOn (fun s => M s h) (Set.Icc (0 : ℝ) (-K * h)) := by
    intro h hlow hneg
    obtain ⟨hlowrho, hhighrho, hcap⟩ := hregion h hlow hneg
    exact (hregular h hlowrho hhighrho).2.mono (by
      intro s hs
      exact ⟨hs.1, hs.2.trans hcap⟩)
  obtain ⟨deltaNeg, hdeltaNeg, _hnegBound, hroots⟩ :=
    negative_shock_two_roots_from_joint_derivative
      M L K rhoK hK hrhoK hzero hjoint ha hc hcontK hantiK
  have hantiPos : ∀ h : ℝ, 0 < h → h < rho →
      StrictAntiOn (fun s => M s h) (Set.Icc (0 : ℝ) eps) := by
    intro h hpos hsmall
    exact (hregular h (by linarith [hrho]) hsmall).2
  obtain ⟨deltaPos, hdeltaPos, _hposBound, hnone⟩ :=
    positive_shock_no_root_from_joint_derivative
      M L rho eps hrho heps hzero hjoint ha hantiPos
  let delta : ℝ := min deltaNeg deltaPos
  have hdelta : 0 < delta := lt_min hdeltaNeg hdeltaPos
  refine ⟨K, hK, delta, hdelta, ?_, ?_⟩
  · intro h hlow hneg
    have hlowNeg : -deltaNeg < h := by
      have hle : delta ≤ deltaNeg := min_le_left ..
      linarith
    exact hroots h hlowNeg hneg
  · intro h hpos hhigh
    have hhighPos : h < deltaPos :=
      lt_of_lt_of_le hhigh (min_le_right ..)
    exact hnone h hpos hhighPos

#print axioms prop31_local_two_signs_of_joint_derivative_and_slices

end CurrentCompactProp31
end Ventura26LiquidityAllocation
