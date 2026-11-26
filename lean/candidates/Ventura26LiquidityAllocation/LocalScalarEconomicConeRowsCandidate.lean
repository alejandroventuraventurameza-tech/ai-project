import Mathlib.Analysis.Normed.Group.Constructions
import Ventura26LiquidityAllocation.LocalScalarEconomicPolicyCertificateCandidate

/-!
# From scalar roots to the full 33-row MODIFIED local prefix

The source LocalScalarImplicitReduction gives a ball in the five economic
parameters on which all 33 modified binding-prefix residuals vanish.
Previously the scalar root was proved only in a shrinking wedge, without
a formal bridge that this wedge is INSIDE the source ball.

This module derives an explicit bound on the five-dimensional
source slice, and shrinks the shock radius accordingly. Thus each
of the two scalar complementary solutions satisfies the SAME 33
modified residual rows via source solutionLog.

Important: one of those 33 rows is the prescribed slack row, NOT
the original omitted funding FOC. The complementary scalar
condition handles the dual but the 33-row bridge still does NOT
prove the original all-agent equilibrium, a global admissible
allocation, a nonlinear tail, or asymptotic growth.
-/

namespace Ventura26LiquidityAllocation
namespace ProposedLocalScalarEconomicConeRows

open ProposedLocalScalarEconomicSlice
open ProposedLocalScalarEconomicPolicyCertificate

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- Supremum norm on the source five-vector is bounded by the sum
of the magnitudes of the TWO nonzero policy/slack coordinates. -/
theorem reserveRemunerationSlice_norm_bound (s h : ℝ) :
    ‖reserveRemunerationSlice s h‖ ≤ |s| + |h| := by
  apply (pi_norm_le_iff_of_nonneg
      (add_nonneg (abs_nonneg s) (abs_nonneg h))).2
  intro j
  fin_cases j <;>
    simp [reserveRemunerationSlice, localScalarSlackDirection,
      localScalarReserveRateDirection, Real.norm_eq_abs] <;>
    linarith [abs_nonneg s, abs_nonneg h]

/-- Every point in the shrinking wedge 0<=s<=-K*h, h<0 lies
inside the true five-dimensional reduction ball whenever the
negative shock is smaller than radius/(K+1). -/
theorem reserveRemunerationSlice_cone_inside_ball
    (s h K radius : ℝ)
    (hK : 0 < K) (hradius : 0 < radius)
    (hneg : h < 0) (hs0 : 0 ≤ s)
    (hsK : s ≤ -K * h)
    (hsmall : -h < radius / (K + 1)) :
    reserveRemunerationSlice s h ∈
      Metric.ball (0 : Fin 5 → ℝ) radius := by
  have hden : 0 < K + 1 := by linarith
  have hprod : (-h) * (K + 1) < radius :=
    (lt_div_iff₀ hden).mp hsmall
  have hsum : |s| + |h| < radius := by
    rw [abs_of_nonneg hs0, abs_of_neg hneg]
    nlinarith only [hsK, hprod]
  have hnorm : ‖reserveRemunerationSlice s h‖ < radius :=
    lt_of_le_of_lt (reserveRemunerationSlice_norm_bound s h) hsum
  simpa only [Metric.mem_ball, dist_zero_right] using hnorm

/-- The actual source implicit-reduction predicate is enough to
impose all 33 modified binding-prefix rows on a narrow scalar
shock/slack wedge. This removes the previous missing ball-membership
assumption, but does not prove the reduction predicate itself. -/
theorem source_reduction_rows_on_local_remuneration_cone
    (P : Primitives S) (I : InheritedState) (Z0 : LocalPrefixCoordinates)
    (dateOne recurrent : S) (tail : LocalPrefixContinuationRule)
    (solutionLog : (Fin 5 → ℝ) → (Fin 33 → ℝ))
    (hred : LocalScalarImplicitReduction P I Z0 dateOne recurrent tail solutionLog)
    (K : ℝ) (hK : 0 < K) :
    ∃ rho : ℝ, 0 < rho ∧
      ∀ h : ℝ, -rho < h → h < 0 →
        ∀ s : ℝ, 0 ≤ s → s ≤ -K * h →
          ∀ row : Fin 33,
            localBindingResidualWithSlack P I Z0 dateOne recurrent tail
              (reserveRemunerationSlice s h)
              (solutionLog (reserveRemunerationSlice s h)) row = 0 := by
  obtain ⟨radius, hradius, hrows⟩ :=
    economicReserveRemunerationMarginal_source_rows
      P I Z0 dateOne recurrent tail solutionLog hred
  let rho : ℝ := radius / (K + 1)
  have hden : 0 < K + 1 := by linarith
  have hrho : 0 < rho := div_pos hradius hden
  refine ⟨rho, hrho, ?_⟩
  intro h hlower hneg s hs0 hsK row
  have hsmall : -h < radius / (K + 1) := by
    dsimp [rho] at hlower
    linarith
  have hinside := reserveRemunerationSlice_cone_inside_ball
    s h K radius hK hradius hneg hs0 hsK hsmall
  exact hrows s h hinside row

/-- Strengthen the source-specific two-root theorem: at both the
boundary root s=0 and positive interior root s=r(h), all 33
MODIFIED prefix rows hold exactly for their recovered log choices.
Local slice regularity is required only at a K-dependent shock radius.
This is the full local source reduced-system implication, NOT a
competitive-equilibrium existence theorem. -/
theorem economic_two_scalar_roots_satisfy_source_33_rows
    (P : Primitives S) (I : InheritedState) (Z0 : LocalPrefixCoordinates)
    (dateOne recurrent : S) (tail : LocalPrefixContinuationRule)
    (solutionLog : (Fin 5 → ℝ) → (Fin 33 → ℝ))
    (hred : LocalScalarImplicitReduction P I Z0 dateOne recurrent tail solutionLog)
    (hzero : localScalarReducedMap P Z0 solutionLog (0 : Fin 5 → ℝ) = 0)
    (rho : ℝ) (hrho : 0 < rho)
    (hreg : ∀ K : ℝ, 0 < K →
      ∃ rhoK : ℝ, 0 < rhoK ∧
        (∀ h : ℝ, -rhoK < h → h < 0 →
          ContinuousOn (fun s => economicReserveRemunerationMarginal
            P Z0 solutionLog s h) (Set.Icc (0 : ℝ) (-K * h))) ∧
        (∀ h : ℝ, -rhoK < h → h < 0 →
          StrictAntiOn (fun s => economicReserveRemunerationMarginal
            P Z0 solutionLog s h) (Set.Icc (0 : ℝ) (-K * h)))) :
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
  obtain ⟨K, hK, delta0, hdelta0, _hle, hroots⟩ :=
    source_economic_negative_remuneration_shock_two_roots
      P I Z0 dateOne recurrent tail solutionLog hred hzero
      rho hrho hreg
  obtain ⟨rhoRows, hrhoRows, hrows⟩ :=
    source_reduction_rows_on_local_remuneration_cone
      P I Z0 dateOne recurrent tail solutionLog hred K hK
  let delta : ℝ := min delta0 rhoRows
  have hdelta : 0 < delta := lt_min hdelta0 hrhoRows
  refine ⟨K, hK, delta, hdelta, ?_⟩
  intro h hlow hneg
  have hlow0 : -delta0 < h := by
    have hle : delta ≤ delta0 := min_le_left ..
    linarith
  have hlowRows : -rhoRows < h := by
    have hle : delta ≤ rhoRows := min_le_right ..
    linarith
  obtain ⟨r, hr0, hrK, hroot, hchar⟩ := hroots h hlow0 hneg
  refine ⟨r, hr0, hrK, hroot, hchar, ?_, ?_⟩
  · intro row
    exact hrows h hlowRows hneg 0 (le_refl 0)
      (le_of_lt (by nlinarith [hK, hneg] : 0 < -K * h)) row
  · intro row
    exact hrows h hlowRows hneg r (le_of_lt hr0) (le_of_lt hrK) row

#print axioms reserveRemunerationSlice_norm_bound
#print axioms reserveRemunerationSlice_cone_inside_ball
#print axioms source_reduction_rows_on_local_remuneration_cone
#print axioms economic_two_scalar_roots_satisfy_source_33_rows

end ProposedLocalScalarEconomicConeRows
end Ventura26LiquidityAllocation
