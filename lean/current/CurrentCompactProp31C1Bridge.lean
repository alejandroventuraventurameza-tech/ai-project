import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Ventura26LiquidityAllocation.CurrentCompactProp31LocalBridge

/-!
# Proposition 3.1: remove the extra monotonicity hypothesis using C^1

This is a SCALAR theorem for the paper's reduced marginal M(s,h).
The hypotheses are precisely local C^1, zero baseline, and the two
strictly negative partial derivatives at the origin. We obtain a
common local rectangle where the s-slices are continuous and strictly
decreasing, then apply the separately audited two-shock bridge.

No conclusion about 33 recovered controls, the original funding FOC,
same-predecessor branch compatibility, or competitive equilibrium is made.
The economic claim requires an independently established SOURCE implicit
reduction with this actual M and the sign conditions.
-/

namespace Ventura26LiquidityAllocation
namespace CurrentCompactProp31C1

open scoped Topology
open CurrentCompactProp31

/-- Joint C^1 at the origin and negative slack derivative produce a
small rectangle on which every slack section is strictly decreasing.
No interval monotonicity is an independent premise. -/
theorem c1_at_origin_implies_uniform_local_slack_antitonicity
    (M : ℝ → ℝ → ℝ)
    (L : (ℝ × ℝ) →L[ℝ] ℝ)
    (hC1 : ContDiffAt ℝ 1
      (fun z : ℝ × ℝ => M z.1 z.2) ((0 : ℝ), (0 : ℝ)))
    (hjoint : HasFDerivAt
      (fun z : ℝ × ℝ => M z.1 z.2) L ((0 : ℝ), (0 : ℝ)))
    (hb : L ((1 : ℝ), (0 : ℝ)) < 0) :
    ∃ rho eps : ℝ, 0 < rho ∧ 0 < eps ∧
      ∀ h : ℝ, -rho < h → h < rho →
        ContinuousOn (fun s => M s h) (Set.Icc (0 : ℝ) eps) ∧
        StrictAntiOn (fun s => M s h) (Set.Icc (0 : ℝ) eps) := by
  let f : (ℝ × ℝ) → ℝ := fun z => M z.1 z.2
  have hC1f : ContDiffAt ℝ 1 f ((0 : ℝ), (0 : ℝ)) := hC1
  obtain ⟨u, hu, hCu⟩ :=
    hC1f.contDiffOn (m := 1) (by norm_num) (by simp)
  obtain ⟨rSrc, hrSrc, hsub⟩ := Metric.mem_nhds_iff.mp hu
  have hCball : ContDiffOn ℝ 1 f
      (Metric.ball ((0 : ℝ), (0 : ℝ)) rSrc) := hCu.mono hsub
  have hDf0 : fderiv ℝ f ((0 : ℝ), (0 : ℝ)) = L :=
    hjoint.fderiv
  have hdirection : ContinuousAt
      (fun z : ℝ × ℝ =>
        fderiv ℝ f z ((1 : ℝ), (0 : ℝ)))
      ((0 : ℝ), (0 : ℝ)) :=
    (hC1f.continuousAt_fderiv (by norm_num)).clm_apply continuousAt_const
  have hneg0 : fderiv ℝ f ((0 : ℝ), (0 : ℝ))
      ((1 : ℝ), (0 : ℝ)) < 0 := by rw [hDf0]; exact hb
  have hnear : ∀ᶠ z in 𝓝 ((0 : ℝ), (0 : ℝ)),
      fderiv ℝ f z ((1 : ℝ), (0 : ℝ)) < 0 :=
    hdirection.tendsto.eventually_lt_const hneg0
  obtain ⟨rNeg, hrNeg, hneg⟩ := Metric.eventually_nhds_iff.mp hnear
  let r : ℝ := min rSrc rNeg
  have hr : 0 < r := lt_min hrSrc hrNeg
  let rho : ℝ := r / 2
  let eps : ℝ := r / 2
  have hrho : 0 < rho := div_pos hr (by norm_num)
  have heps : 0 < eps := div_pos hr (by norm_num)
  have hhalf : rho < r := by dsimp [rho]; linarith
  have hinside : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) eps →
      ∀ h : ℝ, -rho < h → h < rho →
        (s,h) ∈ Metric.ball ((0 : ℝ), (0 : ℝ)) r := by
    intro s hs h hlow hhigh
    have hsabs : |s| < r := by
      rw [abs_of_nonneg hs.1]
      have hepslt : eps < r := by dsimp [eps]; linarith
      exact lt_of_le_of_lt hs.2 hepslt
    have hhabs : |h| < r := by
      have hbound : |h| < rho := abs_lt.mpr ⟨hlow,hhigh⟩
      exact lt_trans hbound hhalf
    change dist (s,h) ((0 : ℝ), (0 : ℝ)) < r
    simpa only [dist_zero_right, Prod.norm_def, Real.norm_eq_abs,
      max_lt_iff] using And.intro hsabs hhabs
  refine ⟨rho, eps, hrho, heps, ?_⟩
  intro h hlow hhigh
  let I : Set ℝ := Set.Icc (0 : ℝ) eps
  have hinsideSrc : ∀ s ∈ I,
      (s,h) ∈ Metric.ball ((0 : ℝ), (0 : ℝ)) rSrc := by
    intro s hs
    have hpt := hinside s hs h hlow hhigh
    exact Metric.mem_ball.mpr
      (lt_of_lt_of_le (Metric.mem_ball.mp hpt) (min_le_left ..))
  have hinsideNeg : ∀ s ∈ I,
      (s,h) ∈ Metric.ball ((0 : ℝ), (0 : ℝ)) rNeg := by
    intro s hs
    have hpt := hinside s hs h hlow hhigh
    exact Metric.mem_ball.mpr
      (lt_of_lt_of_le (Metric.mem_ball.mp hpt) (min_le_right ..))
  have hpath : Continuous (fun s : ℝ => (s,h)) :=
    continuous_id.prodMk continuous_const
  have hcont : ContinuousOn (fun s : ℝ => M s h) I := by
    have hc : ContinuousOn (fun s : ℝ => f (s,h)) I :=
      hCball.continuousOn.comp hpath.continuousOn hinsideSrc
    exact hc
  refine ⟨hcont, ?_⟩
  apply strictAntiOn_of_deriv_neg (convex_Icc (0 : ℝ) eps) hcont
  intro s hs
  have hsI : s ∈ I := interior_subset hs
  have hpt : (s,h) ∈ Metric.ball ((0 : ℝ), (0 : ℝ)) rSrc :=
    hinsideSrc s hsI
  have hdiff : HasFDerivAt f (fderiv ℝ f (s,h)) (s,h) :=
    ((hCball.differentiableOn_one).differentiableAt
      (Metric.isOpen_ball.mem_nhds hpt)).hasFDerivAt
  have hpathder : HasDerivAt (fun x : ℝ => (x,h))
      ((1 : ℝ), (0 : ℝ)) s := by
    simpa using (hasDerivAt_id s).prodMk
      (hasDerivAt_const s h)
  have hcomp : HasDerivAt (fun x : ℝ => M x h)
      (fderiv ℝ f (s,h) ((1 : ℝ), (0 : ℝ))) s := by
    simpa only [Function.comp_def] using
      hdiff.comp_hasDerivAt_of_eq s hpathder rfl
  have hderiveq : deriv (fun x : ℝ => M x h) s =
      fderiv ℝ f (s,h) ((1 : ℝ), (0 : ℝ)) := hcomp.deriv
  rw [hderiveq]
  exact hneg _ (hinsideNeg s hsI)

/-- Both statements in the compact paper's scalar Proposition 3.1
from its stated C^1 assumptions: negative shocks yield precisely two
LOCAL complementary roots, positive shocks yield none locally.
Does not assert two economic equilibria or a global uniqueness theorem. -/
theorem prop31_scalar_current_C1_exact
    (M : ℝ → ℝ → ℝ)
    (L : (ℝ × ℝ) →L[ℝ] ℝ)
    (hzero : M 0 0 = 0)
    (hC1 : ContDiffAt ℝ 1
      (fun z : ℝ × ℝ => M z.1 z.2) ((0 : ℝ), (0 : ℝ)))
    (hjoint : HasFDerivAt
      (fun z : ℝ × ℝ => M z.1 z.2) L ((0 : ℝ), (0 : ℝ)))
    (hb : L ((1 : ℝ), (0 : ℝ)) < 0)
    (ha : L ((0 : ℝ), (1 : ℝ)) < 0) :
    ∃ K : ℝ, 0 < K ∧
      ∃ delta : ℝ, 0 < delta ∧
        (∀ h : ℝ, -delta < h → h < 0 →
          ∃ r : ℝ, 0 < r ∧ r < -K * h ∧ M r h = 0 ∧
            (∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) (-K * h) →
              (ProposedScalarComplementarityMultiplicity.ScalarComplementarity
                (fun x => M x h) s ↔ s = 0 ∨ s = r))) ∧
        (∃ eps : ℝ, 0 < eps ∧
          ∀ h : ℝ, 0 < h → h < delta →
            ¬ ∃ s : ℝ, s ∈ Set.Icc (0 : ℝ) eps ∧
              ProposedScalarComplementarityMultiplicity.ScalarComplementarity
                (fun x => M x h) s) := by
  obtain ⟨rho, eps, hrho, heps, hreg⟩ :=
    c1_at_origin_implies_uniform_local_slack_antitonicity M L hC1 hjoint hb
  obtain ⟨K, hK, delta, hdelta, hroots, hnone⟩ :=
    prop31_local_two_signs_of_joint_derivative_and_slices
      M L rho eps hrho heps hzero hjoint hb ha hreg
  exact ⟨K, hK, delta, hdelta, hroots, eps, heps, hnone⟩

#print axioms c1_at_origin_implies_uniform_local_slack_antitonicity
#print axioms prop31_scalar_current_C1_exact

end CurrentCompactProp31C1
end Ventura26LiquidityAllocation
