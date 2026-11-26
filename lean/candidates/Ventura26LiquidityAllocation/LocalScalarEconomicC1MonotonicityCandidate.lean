import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Ventura26LiquidityAllocation.LocalScalarEconomicConeRowsCandidate

/-!
# Local strict monotonicity from continuity of the economic Schur derivative

The previous source-specific bifurcation theorem assumed, separately for
each transverse slope K, continuity and strict antitonicity of the scalar
marginal in s. We now construct those properties from:

* the SOURCE LocalScalarImplicitReduction, which already gives
  differentiability on an open five-dimensional parameter ball;
* continuity at zero of the directional derivative
  y |-> fderiv M y localScalarSlackDirection.

Since the source predicate includes b=dM(0)e_slack<0, continuity gives
a ball of uniformly negative derivatives. A cone bound then yields a
K-dependent negative-shock radius on which every s-section is strictly
decreasing. Thus the mathematical C^1 bridge is discharged WITHOUT
postulating interval monotonicity. Neither the C^1 continuity at zero,
nor the source reduction witness, is proved by this module.
-/

namespace Ventura26LiquidityAllocation
namespace ProposedLocalScalarEconomicC1Monotonicity

open scoped Topology

open ProposedLocalScalarEconomicSlice
open ProposedLocalScalarEconomicConeRows

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- Continuity of the reduced scalar derivative at zero upgrades the
strictly negative derivative at zero to a STRICT SIGN on a full
five-dimensional neighborhood. -/
theorem locally_negative_schur_direction
    (M : (Fin 5 → ℝ) → ℝ)
    (hcont : ContinuousAt
      (fun y : Fin 5 → ℝ =>
        fderiv ℝ M y localScalarSlackDirection)
      (0 : Fin 5 → ℝ))
    (hb : fderiv ℝ M (0 : Fin 5 → ℝ) localScalarSlackDirection < 0) :
    ∃ radius : ℝ, 0 < radius ∧
      ∀ y ∈ Metric.ball (0 : Fin 5 → ℝ) radius,
        fderiv ℝ M y localScalarSlackDirection < 0 := by
  have hnear : ∀ᶠ y in 𝓝 (0 : Fin 5 → ℝ),
      fderiv ℝ M y localScalarSlackDirection < 0 :=
    hcont.tendsto.eventually_lt_const hb
  obtain ⟨radius, hradius, hsign⟩ :=
    Metric.eventually_nhds_iff.mp hnear
  refine ⟨radius, hradius, ?_⟩
  intro y hy
  exact hsign (Metric.mem_ball.mp hy)

/-- The economic five-vector is an affine differentiable function of s
for every fixed reserve-remuneration innovation h. -/
theorem economic_policy_slice_hasDerivAt_slack (h s : ℝ) :
    HasDerivAt
      (fun x : ℝ => reserveRemunerationSlice x h)
      localScalarSlackDirection s := by
  have hs : HasDerivAt
      (fun x : ℝ => x • localScalarSlackDirection)
      localScalarSlackDirection s := by
    simpa only [one_smul] using
      ((hasDerivAt_id s).smul_const localScalarSlackDirection)
  have hc : HasDerivAt
      (fun _x : ℝ => h • localScalarReserveRateDirection)
      (0 : Fin 5 → ℝ) s :=
    hasDerivAt_const s (h • localScalarReserveRateDirection)
  simpa only [reserveRemunerationSlice, add_zero] using hs.add hc

/-- The full local derivative requirement is sufficient to provide
K-dependent continuity and strict antitonicity on the source scalar
cone. This is the precise missing C1 -> monotonicity bridge. -/
theorem source_C1_implies_local_scalar_cone_antitonicity
    (P : Primitives S) (I : InheritedState) (Z0 : LocalPrefixCoordinates)
    (dateOne recurrent : S) (tail : LocalPrefixContinuationRule)
    (solutionLog : (Fin 5 → ℝ) → (Fin 33 → ℝ))
    (hred : LocalScalarImplicitReduction P I Z0 dateOne recurrent tail solutionLog)
    (hC1 : ContinuousAt
      (fun y : Fin 5 → ℝ =>
        fderiv ℝ (localScalarReducedMap P Z0 solutionLog)
          y localScalarSlackDirection)
      (0 : Fin 5 → ℝ)) :
    ∀ K : ℝ, 0 < K →
      ∃ rhoK : ℝ, 0 < rhoK ∧
        (∀ h : ℝ, -rhoK < h → h < 0 →
          ContinuousOn (fun s => economicReserveRemunerationMarginal
            P Z0 solutionLog s h) (Set.Icc (0 : ℝ) (-K * h))) ∧
        (∀ h : ℝ, -rhoK < h → h < 0 →
          StrictAntiOn (fun s => economicReserveRemunerationMarginal
            P Z0 solutionLog s h) (Set.Icc (0 : ℝ) (-K * h))) := by
  let M := localScalarReducedMap P Z0 solutionLog
  have hb : fderiv ℝ M (0 : Fin 5 → ℝ)
      localScalarSlackDirection < 0 :=
    (economicReserveRemunerationMarginal_source_signs
      P I Z0 dateOne recurrent tail solutionLog hred).1
  obtain ⟨radiusNeg, hradiusNeg, hnegSign⟩ :=
    locally_negative_schur_direction M hC1 hb
  obtain ⟨_hbase, radiusSrc, hradiusSrc, _hsol,
    hMdiff, _hrows, _hunique, _hblow, _hbhigh, _ha⟩ := hred
  intro K hK
  let radius : ℝ := min radiusSrc radiusNeg
  have hradius : 0 < radius := lt_min hradiusSrc hradiusNeg
  let rhoK : ℝ := radius / (K + 1)
  have hden : 0 < K + 1 := by linarith
  have hrhoK : 0 < rhoK := div_pos hradius hden
  refine ⟨rhoK, hrhoK, ?_, ?_⟩
  · intro h hlow hneg
    have hwithin : ∀ s ∈ Set.Icc (0 : ℝ) (-K * h),
        reserveRemunerationSlice s h ∈
          Metric.ball (0 : Fin 5 → ℝ) radiusSrc := by
      intro s hs
      have hsmall : -h < radius / (K + 1) := by
        dsimp [rhoK] at hlow
        linarith
      have hrad := reserveRemunerationSlice_cone_inside_ball
        s h K radius hK hradius hneg hs.1 hs.2 hsmall
      have hbound : radius ≤ radiusSrc := min_le_left ..
      exact Metric.mem_ball.mpr
        (lt_of_lt_of_le (Metric.mem_ball.mp hrad) hbound)
    have hpath : Continuous (fun s : ℝ => reserveRemunerationSlice s h) := by
      unfold reserveRemunerationSlice
      fun_prop
    have hcomposed : ContinuousOn
        (fun s : ℝ => M (reserveRemunerationSlice s h))
        (Set.Icc (0 : ℝ) (-K * h)) :=
      hMdiff.continuousOn.comp hpath.continuousOn hwithin
    simpa only [economicReserveRemunerationMarginal] using hcomposed
  · intro h hlow hneg
    have hwithin : ∀ s ∈ Set.Icc (0 : ℝ) (-K * h),
        reserveRemunerationSlice s h ∈
          Metric.ball (0 : Fin 5 → ℝ) radius := by
      intro s hs
      have hsmall : -h < radius / (K + 1) := by
        dsimp [rhoK] at hlow
        linarith
      exact reserveRemunerationSlice_cone_inside_ball
        s h K radius hK hradius hneg hs.1 hs.2 hsmall
    have hnegder : ∀ s ∈ Set.Icc (0 : ℝ) (-K * h),
        deriv (fun x : ℝ =>
          economicReserveRemunerationMarginal P Z0 solutionLog x h) s < 0 := by
      intro s hs
      have hrad := hwithin s hs
      have hsrc : reserveRemunerationSlice s h ∈
          Metric.ball (0 : Fin 5 → ℝ) radiusSrc := by
        exact Metric.mem_ball.mpr
          (lt_of_lt_of_le (Metric.mem_ball.mp hrad) (min_le_left ..))
      have hnegrad : reserveRemunerationSlice s h ∈
          Metric.ball (0 : Fin 5 → ℝ) radiusNeg := by
        exact Metric.mem_ball.mpr
          (lt_of_lt_of_le (Metric.mem_ball.mp hrad) (min_le_right ..))
      have hsource : HasFDerivAt M
          (fderiv ℝ M (reserveRemunerationSlice s h))
          (reserveRemunerationSlice s h) :=
        (hMdiff.differentiableAt
          (Metric.isOpen_ball.mem_nhds hsrc)).hasFDerivAt
      have hpath := economic_policy_slice_hasDerivAt_slack h s
      have hderiv : HasDerivAt
          (fun x : ℝ => M (reserveRemunerationSlice x h))
          ((fderiv ℝ M (reserveRemunerationSlice s h))
            localScalarSlackDirection) s := by
        simpa only [Function.comp_def] using
          hsource.comp_hasDerivAt_of_eq s hpath rfl
      have hderivEq : deriv
          (fun x : ℝ => economicReserveRemunerationMarginal
            P Z0 solutionLog x h) s =
          (fderiv ℝ M (reserveRemunerationSlice s h))
            localScalarSlackDirection := by
        simpa only [economicReserveRemunerationMarginal] using
          hderiv.deriv
      rw [hderivEq]
      exact hnegSign _ hnegrad
    have hpath : Continuous (fun s : ℝ => reserveRemunerationSlice s h) := by
      unfold reserveRemunerationSlice
      fun_prop
    have hsrcWithin : ∀ s ∈ Set.Icc (0 : ℝ) (-K * h),
        reserveRemunerationSlice s h ∈
          Metric.ball (0 : Fin 5 → ℝ) radiusSrc := by
      intro s hs
      have hrad := hwithin s hs
      exact Metric.mem_ball.mpr
        (lt_of_lt_of_le (Metric.mem_ball.mp hrad) (min_le_left ..))
    have hcont : ContinuousOn
        (fun s : ℝ => economicReserveRemunerationMarginal
          P Z0 solutionLog s h)
        (Set.Icc (0 : ℝ) (-K * h)) := by
      have hc := hMdiff.continuousOn.comp hpath.continuousOn hsrcWithin
      simpa only [economicReserveRemunerationMarginal] using hc
    apply strictAntiOn_of_deriv_neg (convex_Icc (0 : ℝ) (-K * h)) hcont
    intro s hs
    exact hnegder s (interior_subset hs)

/-- Removing the previous separately assumed interval antitonicity
from the SOURCE-SPECIFIC 33-row two-root result. Remaining premises
are the baseline marginal equality, source local solution predicate,
and continuity at zero of the source slack-direction Schur derivative. -/
theorem source_C1_two_local_roots_and_all_33_modified_rows
    (P : Primitives S) (I : InheritedState) (Z0 : LocalPrefixCoordinates)
    (dateOne recurrent : S) (tail : LocalPrefixContinuationRule)
    (solutionLog : (Fin 5 → ℝ) → (Fin 33 → ℝ))
    (hred : LocalScalarImplicitReduction P I Z0 dateOne recurrent tail solutionLog)
    (hzero : localScalarReducedMap P Z0 solutionLog (0 : Fin 5 → ℝ) = 0)
    (hC1 : ContinuousAt
      (fun y : Fin 5 → ℝ =>
        fderiv ℝ (localScalarReducedMap P Z0 solutionLog)
          y localScalarSlackDirection)
      (0 : Fin 5 → ℝ)) :
    ∃ K : ℝ, 0 < K ∧
      ∃ delta : ℝ, 0 < delta ∧
        ∀ h : ℝ, -delta < h → h < 0 →
          ∃ r : ℝ, 0 < r ∧ r < -K * h ∧
            economicReserveRemunerationMarginal P Z0 solutionLog r h = 0 ∧
            (∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) (-K * h) →
              (ProposedScalarComplementarityMultiplicity.ScalarComplementarity
                (fun s => economicReserveRemunerationMarginal
                  P Z0 solutionLog s h) s ↔ s = 0 ∨ s = r)) ∧
            (∀ row : Fin 33,
              localBindingResidualWithSlack P I Z0 dateOne recurrent tail
                (reserveRemunerationSlice 0 h)
                (solutionLog (reserveRemunerationSlice 0 h)) row = 0) ∧
            (∀ row : Fin 33,
              localBindingResidualWithSlack P I Z0 dateOne recurrent tail
                (reserveRemunerationSlice r h)
                (solutionLog (reserveRemunerationSlice r h)) row = 0) := by
  have hreg := source_C1_implies_local_scalar_cone_antitonicity
    P I Z0 dateOne recurrent tail solutionLog hred hC1
  exact economic_two_scalar_roots_satisfy_source_33_rows
    P I Z0 dateOne recurrent tail solutionLog
    hred hzero 1 (by norm_num) hreg

#print axioms locally_negative_schur_direction
#print axioms economic_policy_slice_hasDerivAt_slack
#print axioms source_C1_implies_local_scalar_cone_antitonicity
#print axioms source_C1_two_local_roots_and_all_33_modified_rows

end ProposedLocalScalarEconomicC1Monotonicity
end Ventura26LiquidityAllocation
