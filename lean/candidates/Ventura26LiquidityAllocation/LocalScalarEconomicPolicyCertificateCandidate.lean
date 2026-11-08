import Ventura26LiquidityAllocation.LocalScalarEconomicDerivativeBridgeCandidate

/-!
# Conditional LOCAL bifurcation for the literal economic reduced marginal

This module finally specializes the abstract mathematical two-root theorem
to the concrete localScalarReducedMap sourced from the 33 modified
binding-prefix equations. The five-dimensional source parameter vector
sets reserve-quantity, reserve-requirement, and corridor innovations to
zero, and varies ONLY normalized slack and reserve REMUNERATION.

LocalScalarImplicitReduction is an assumed economic predicate, not a
verified numerical certificate. Its signed Schur partials produce a
positive transverse ray and directional derivatives. An explicit
zero-baseline-dual premise and LOCAL slice continuity/antitonicity
premises remain. Under them there are exactly two complementary roots
inside the shrinking wedge for every sufficiently small negative
reserve-remuneration innovation. No global or infinite-horizon
competitive equilibrium is asserted.
-/

namespace Ventura26LiquidityAllocation
namespace ProposedLocalScalarEconomicPolicyCertificate

open ProposedLocalScalarEconomicSlice
open ProposedLocalScalarEconomicDerivativeBridge
open ProposedLocalScalarPolicyBifurcation

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- Construct a positive transverse slack coefficient using ONLY the
two signed source-Schur partial derivatives, without an arbitrary
directional sign premise. -/
theorem source_schur_has_positive_transverse_ray
    (dM : (Fin 5 → ℝ) →L[ℝ] ℝ)
    (hb : dM localScalarSlackDirection < 0)
    (ha : dM localScalarReserveRateDirection < 0) :
    ∃ K : ℝ, 0 < K ∧
      0 < dM ((-K) • localScalarSlackDirection +
        localScalarReserveRateDirection) := by
  let a : ℝ := dM localScalarReserveRateDirection
  let b : ℝ := dM localScalarSlackDirection
  let K : ℝ := (1 - a) / (-b)
  have hbpos : 0 < -b := neg_pos.mpr hb
  have hK : 0 < K := by
    dsimp [K]
    exact div_pos (by linarith only [ha]) hbpos
  have hKmul : K * (-b) = 1 - a := by
    dsimp [K]
    exact div_mul_cancel₀ (1 - a) (ne_of_gt hbpos)
  have hlinear : dM ((-K) • localScalarSlackDirection +
      localScalarReserveRateDirection) = a - K * b := by
    simp only [map_add, map_smul, smul_eq_mul]
    dsimp [a, b]
    ring
  refine ⟨K, hK, ?_⟩
  rw [hlinear]
  nlinarith only [hKmul]

/-- Two local scalar solutions for a NEGATIVE reserve-remuneration shock
in the actual source dual. Requires a genuine local implicit-reduction
witness, baseline dual equality, and continuity/strict decrease on each
transverse slice. None of these obligations is silently proved by this
theorem. -/
theorem source_economic_negative_remuneration_shock_two_roots
    (P : Primitives S) (I : InheritedState) (Z0 : LocalPrefixCoordinates)
    (dateOne recurrent : S) (tail : LocalPrefixContinuationRule)
    (solutionLog : (Fin 5 → ℝ) → (Fin 33 → ℝ))
    (hred : LocalScalarImplicitReduction P I Z0 dateOne recurrent tail solutionLog)
    (hzero : localScalarReducedMap P Z0 solutionLog (0 : Fin 5 → ℝ) = 0)
    (rho : ℝ) (hrho : 0 < rho)
    (hcont : ∀ K : ℝ, 0 < K →
      ∀ h : ℝ, -rho < h → h < 0 →
        ContinuousOn (fun s => economicReserveRemunerationMarginal
          P Z0 solutionLog s h) (Set.Icc (0 : ℝ) (-K * h)))
    (hanti : ∀ K : ℝ, 0 < K →
      ∀ h : ℝ, -rho < h → h < 0 →
        StrictAntiOn (fun s => economicReserveRemunerationMarginal
          P Z0 solutionLog s h) (Set.Icc (0 : ℝ) (-K * h))) :
    ∃ K : ℝ, 0 < K ∧
      ∃ delta : ℝ, 0 < delta ∧ delta ≤ rho ∧
        ∀ h : ℝ, -delta < h → h < 0 →
          ∃ r : ℝ, 0 < r ∧ r < -K * h ∧
            economicReserveRemunerationMarginal P Z0 solutionLog r h = 0 ∧
            (∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) (-K * h) →
              (ProposedScalarComplementarityMultiplicity.ScalarComplementarity
                (fun s => economicReserveRemunerationMarginal
                  P Z0 solutionLog s h) s ↔ s = 0 ∨ s = r)) := by
  let dM := fderiv ℝ (localScalarReducedMap P Z0 solutionLog)
    (0 : Fin 5 → ℝ)
  obtain ⟨hb, ha⟩ := economicReserveRemunerationMarginal_source_signs
    P I Z0 dateOne recurrent tail solutionLog hred
  obtain ⟨K, hK, hc⟩ := source_schur_has_positive_transverse_ray
    dM hb ha
  obtain ⟨haxis, hray⟩ :=
    source_economic_marginal_axis_and_ray_derivatives
      P I Z0 dateOne recurrent tail solutionLog hred K
  have hzero' : economicReserveRemunerationMarginal P Z0 solutionLog 0 0 = 0 := by
    simpa [economicReserveRemunerationMarginal, reserveRemunerationSlice] using hzero
  obtain ⟨delta, hdelta, hdeltale, hroots⟩ :=
    negative_shock_creates_exactly_two_local_scalar_roots
      (economicReserveRemunerationMarginal P Z0 solutionLog)
      (dM localScalarReserveRateDirection)
      (dM ((-K) • localScalarSlackDirection +
        localScalarReserveRateDirection))
      K rho hK hrho hzero' haxis ha hray hc
      (hcont K hK) (hanti K hK)
  exact ⟨K, hK, delta, hdelta, hdeltale, hroots⟩

/-- A positive reserve-remuneration innovation has NO complementary
root in the stated local interval if the source slice is strictly
decreasing there. This is not global nonexistence. -/
theorem source_economic_positive_remuneration_shock_no_local_root
    (P : Primitives S) (I : InheritedState) (Z0 : LocalPrefixCoordinates)
    (dateOne recurrent : S) (tail : LocalPrefixContinuationRule)
    (solutionLog : (Fin 5 → ℝ) → (Fin 33 → ℝ))
    (hred : LocalScalarImplicitReduction P I Z0 dateOne recurrent tail solutionLog)
    (hzero : localScalarReducedMap P Z0 solutionLog (0 : Fin 5 → ℝ) = 0)
    (rho eps : ℝ) (hrho : 0 < rho) (heps : 0 < eps)
    (hanti : ∀ h : ℝ, 0 < h → h < rho →
      StrictAntiOn (fun s => economicReserveRemunerationMarginal
        P Z0 solutionLog s h) (Set.Icc (0 : ℝ) eps)) :
    ∃ delta : ℝ, 0 < delta ∧ delta ≤ rho ∧
      ∀ h : ℝ, 0 < h → h < delta →
        ¬ ∃ s : ℝ, s ∈ Set.Icc (0 : ℝ) eps ∧
          ProposedScalarComplementarityMultiplicity.ScalarComplementarity
            (fun s => economicReserveRemunerationMarginal
              P Z0 solutionLog s h) s := by
  let dM := fderiv ℝ (localScalarReducedMap P Z0 solutionLog)
    (0 : Fin 5 → ℝ)
  have ha := (economicReserveRemunerationMarginal_source_signs
    P I Z0 dateOne recurrent tail solutionLog hred).2
  have haxis := (source_economic_marginal_axis_and_ray_derivatives
    P I Z0 dateOne recurrent tail solutionLog hred 1).1
  have hzero' : economicReserveRemunerationMarginal P Z0 solutionLog 0 0 = 0 := by
    simpa [economicReserveRemunerationMarginal, reserveRemunerationSlice] using hzero
  exact positive_shock_has_no_local_scalar_root
    (economicReserveRemunerationMarginal P Z0 solutionLog)
    (dM localScalarReserveRateDirection) rho eps
    hrho heps hzero' haxis ha hanti

#print axioms source_schur_has_positive_transverse_ray
#print axioms source_economic_negative_remuneration_shock_two_roots
#print axioms source_economic_positive_remuneration_shock_no_local_root

end ProposedLocalScalarEconomicPolicyCertificate
end Ventura26LiquidityAllocation
