import Mathlib.Analysis.Calculus.Deriv.Mul
import Ventura26LiquidityAllocation.LocalScalarEconomicSliceCandidate

/-!
# Source-reduced derivative bridge for the reserve-remuneration experiment

The original five-parameter economic marginal is restricted along
(1) the pure remuneration-rate axis and
(2) an economic collateral-slack/remuneration ray.

The source LocalScalarImplicitReduction includes an actual 33-row
solutionLog and assumes the numerical Schur derivative signs on the
source economic marginal. This module derives the two directional
derivatives on the exact source slice from its Frechet derivative.

It does NOT prove the source LocalScalarImplicitReduction predicate,
the numerical Schur intervals, C^1 regularity on a neighborhood,
or an equilibrium.
-/

namespace Ventura26LiquidityAllocation
namespace ProposedLocalScalarEconomicDerivativeBridge

open ProposedLocalScalarEconomicSlice

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- Reserve-remuneration innovation is a differentiable coordinate path in
the actual five-dimensional source parameter vector. -/
theorem reserveRemunerationSlice_policy_axis_hasDerivAt :
    HasDerivAt (fun h : ℝ => reserveRemunerationSlice 0 h)
      localScalarReserveRateDirection 0 := by
  simpa [reserveRemunerationSlice] using
    ((hasDerivAt_id (0 : ℝ)).smul_const localScalarReserveRateDirection)

/-- The transversal ray is differentiable in the actual source parameter
coordinates; its derivative is -K e_slack + e_R. -/
theorem reserveRemunerationSlice_transverse_hasDerivAt (K : ℝ) :
    HasDerivAt (fun h : ℝ => reserveRemunerationSlice (-K * h) h)
      ((-K) • localScalarSlackDirection + localScalarReserveRateDirection) 0 := by
  have hs : HasDerivAt
      (fun h : ℝ => (-K * h) • localScalarSlackDirection)
      ((-K) • localScalarSlackDirection) 0 := by
    simpa only [id_eq, mul_one] using
      (((hasDerivAt_id (0 : ℝ)).const_mul (-K)).smul_const
        localScalarSlackDirection)
  have hr : HasDerivAt
      (fun h : ℝ => h • localScalarReserveRateDirection)
      localScalarReserveRateDirection 0 := by
    simpa only [id_eq, one_smul] using
      ((hasDerivAt_id (0 : ℝ)).smul_const localScalarReserveRateDirection)
  simpa [reserveRemunerationSlice] using hs.add hr

/-- The source's local differentiability assumption produces a Frechet
derivative at the exact zero-innovation vector. -/
theorem source_local_reduction_hasFDerivAt
    (P : Primitives S) (I : InheritedState) (Z0 : LocalPrefixCoordinates)
    (dateOne recurrent : S) (tail : LocalPrefixContinuationRule)
    (solutionLog : (Fin 5 → ℝ) → (Fin 33 → ℝ))
    (hred : LocalScalarImplicitReduction P I Z0 dateOne recurrent tail solutionLog) :
    HasFDerivAt (localScalarReducedMap P Z0 solutionLog)
      (fderiv ℝ (localScalarReducedMap P Z0 solutionLog)
        (0 : Fin 5 → ℝ))
      (0 : Fin 5 → ℝ) := by
  rcases hred with ⟨_hbase, radius, hradius, _hsol, hMdiff, _hrows,
    _hunique, _hblow, _hbhigh, _ha⟩
  have hzero : (0 : Fin 5 → ℝ) ∈
      Metric.ball (0 : Fin 5 → ℝ) radius :=
    Metric.mem_ball_self hradius
  exact (hMdiff.differentiableAt
    (Metric.isOpen_ball.mem_nhds hzero)).hasFDerivAt

/-- A single source Frechet derivative determines both directional
derivatives of the EXACT economic normalized collateral dual. -/
theorem source_economic_marginal_axis_and_ray_derivatives
    (P : Primitives S) (I : InheritedState) (Z0 : LocalPrefixCoordinates)
    (dateOne recurrent : S) (tail : LocalPrefixContinuationRule)
    (solutionLog : (Fin 5 → ℝ) → (Fin 33 → ℝ))
    (hred : LocalScalarImplicitReduction P I Z0 dateOne recurrent tail solutionLog)
    (K : ℝ) :
    let dM := fderiv ℝ (localScalarReducedMap P Z0 solutionLog)
      (0 : Fin 5 → ℝ)
    HasDerivAt (fun h : ℝ =>
      economicReserveRemunerationMarginal P Z0 solutionLog 0 h)
      (dM localScalarReserveRateDirection) 0 ∧
    HasDerivAt (fun h : ℝ =>
      economicReserveRemunerationMarginal P Z0 solutionLog (-K * h) h)
      (dM ((-K) • localScalarSlackDirection +
          localScalarReserveRateDirection)) 0 := by
  let dM := fderiv ℝ (localScalarReducedMap P Z0 solutionLog)
    (0 : Fin 5 → ℝ)
  have hsource := source_local_reduction_hasFDerivAt
    P I Z0 dateOne recurrent tail solutionLog hred
  have haxis := reserveRemunerationSlice_policy_axis_hasDerivAt
  have hray := reserveRemunerationSlice_transverse_hasDerivAt K
  constructor
  · simpa only [economicReserveRemunerationMarginal, Function.comp_def] using
      hsource.comp_hasDerivAt_of_eq (0 : ℝ) haxis
        (by simp [reserveRemunerationSlice])
  · simpa only [economicReserveRemunerationMarginal, Function.comp_def] using
      hsource.comp_hasDerivAt_of_eq (0 : ℝ) hray
        (by simp [reserveRemunerationSlice])

#print axioms reserveRemunerationSlice_policy_axis_hasDerivAt
#print axioms reserveRemunerationSlice_transverse_hasDerivAt
#print axioms source_local_reduction_hasFDerivAt
#print axioms source_economic_marginal_axis_and_ray_derivatives

end ProposedLocalScalarEconomicDerivativeBridge
end Ventura26LiquidityAllocation
