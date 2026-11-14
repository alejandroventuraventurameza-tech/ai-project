import Ventura26LiquidityAllocation.SourceAugmented34LinearizedMultiplierCandidate
import Ventura26LiquidityAllocation.SourceReducedFundingDualChainCandidate

/-!
# SOURCE 34-equation Schur criterion from the reduced marginal sign

The genuine 5-dimensional SOURCE implicit-reduction predicate explicitly
ASSUMES a negative reserve-remuneration directional derivative of the L
funding multiplier. When solutionLog has the indicated derivative and
its linearization solves the actual 33 modified binding-prefix rows,
the strict sign transfers to the exact SOURCE 34x34 Schur gate.

This is conditional sign TRANSPORT. It does not certify the assumed
economic reduced derivative, A invertibility, root existence,
arbitrary tail regularity, or a full equilibrium.
-/

namespace Ventura26LiquidityAllocation
namespace ProposedLocalScalarAugmented34Source

open ProposedLocalScalarEconomicSlice

private abbrev Economic33 := Fin 33 → ℝ

/-- Given the genuine SOURCE predicate's negative rate derivative,
the same directional derivative of the normalized L dual along the
source solutionLog is strictly negative. This uses the actual CRRA
dual and its positive-log-chart Frechet chain rule. -/
theorem sourceReducedFundingDual_sourceRateDirection_negative
    {S : Type*} [Fintype S] [DecidableEq S]
    (P : Primitives S) (I : InheritedState)
    (Z0 : LocalPrefixCoordinates)
    (dateOne recurrent : S) (tail : LocalPrefixContinuationRule)
    (solutionLog : (Fin 5 → ℝ) → Economic33)
    (hZ0 : LocalPrefixCoordinatesPositive Z0)
    (hred : LocalScalarImplicitReduction P I Z0 dateOne recurrent tail
      solutionLog)
    (hsol : DifferentiableAt ℝ solutionLog (0 : Fin 5 → ℝ)) :
    (fderiv ℝ (sourceAugmented34Dual P Z0) (solutionLog 0))
      ((fderiv ℝ solutionLog 0) localScalarReserveRateDirection) < 0 := by
  have hsign := (economicReserveRemunerationMarginal_source_signs
    P I Z0 dateOne recurrent tail solutionLog hred).2
  rw [sourceReducedFundingDual_fderiv_chain
    P Z0 hZ0 solutionLog (0 : Fin 5 → ℝ) hsol] at hsign
  simpa only [ContinuousLinearMap.comp_apply, sourceAugmented34Dual] using hsign

#print axioms sourceReducedFundingDual_sourceRateDirection_negative

/-- Conditional SOURCE economic 34x34 rank:
a rate-direction linearized solution, together with the SOURCE
implicit reduction's strict negative marginal response and a supplied
invertible 33x33 block A, makes the ACTUAL augmented Frechet Jacobian
bijective. This does not prove the required hypotheses from primitives. -/
theorem sourceAugmented34_jacobian_bijective_of_reducedRateSign
    {S : Type*} [Fintype S] [DecidableEq S]
    (P : Primitives S) (I : InheritedState)
    (Z0 : LocalPrefixCoordinates)
    (dateOne recurrent : S) (tail : LocalPrefixContinuationRule)
    (solutionLog : (Fin 5 → ℝ) → Economic33)
    (hZ0 : LocalPrefixCoordinatesPositive Z0)
    (hred : LocalScalarImplicitReduction P I Z0 dateOne recurrent tail
      solutionLog)
    (hsol : DifferentiableAt ℝ solutionLog (0 : Fin 5 → ℝ))
    (A : Economic33 ≃ₗ[ℝ] Economic33)
    (hB : DifferentiableAt ℝ
      (sourceAugmented34Rows P I Z0 dateOne recurrent tail)
      ((0 : Economic33), (0 : ℝ)))
    (hA : ∀ x : Economic33,
      (fderiv ℝ
        (sourceAugmented34Rows P I Z0 dateOne recurrent tail)
        ((0 : Economic33), (0 : ℝ))) (x, (0 : ℝ)) = A x)
    (hlin : (fderiv ℝ
      (sourceAugmented34Rows P I Z0 dateOne recurrent tail)
      ((0 : Economic33), (0 : ℝ)))
      ((fderiv ℝ solutionLog 0) localScalarReserveRateDirection,
       (1 : ℝ)) = 0) :
    Function.Bijective
      (fderiv ℝ
        (sourceAugmented34Map P I Z0 dateOne recurrent tail)
        ((0 : Economic33), (0 : ℝ))) := by
  have hneg := sourceReducedFundingDual_sourceRateDirection_negative
    P I Z0 dateOne recurrent tail solutionLog hZ0 hred hsol
  have hzero : solutionLog (0 : Fin 5 → ℝ) = 0 := hred.1
  rw [hzero] at hneg
  apply (sourceAugmented34_actualJacobian_bijective_iff_linearizedDual_ne
    P I Z0 dateOne recurrent tail hZ0
    (0 : Economic33) (0 : ℝ) A hB hA
    ((fderiv ℝ solutionLog 0) localScalarReserveRateDirection)
    hlin).2
  exact ne_of_lt hneg

#print axioms sourceAugmented34_jacobian_bijective_of_reducedRateSign

end ProposedLocalScalarAugmented34Source
end Ventura26LiquidityAllocation
