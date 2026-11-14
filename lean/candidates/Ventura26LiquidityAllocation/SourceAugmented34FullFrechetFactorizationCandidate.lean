import Ventura26LiquidityAllocation.SourceAugmented34RowFrechetFactorizationCandidate
import Mathlib.Analysis.Calculus.FDeriv.Prod

/-!
# Genuine SOURCE augmented 34x34 Frechet factorization and rank equivalence

Unlike the earlier abstract row-scaling theorems, the derivative
equality here is the CONCLUSION, not a hypothesis. Its proof consumes
actual SOURCE row-5 and row-21 scalar Frechet identities, the proven
permutation of the other 31 rows, and the identical 34th dual equation.

Regularity of the two genuine SOURCE vector-valued maps and of the
collateral components is explicit. The basepoint must be an ACTUAL
augmented SOURCE root, and the common-pledge valuation must be positive.

The result does not construct the economic root, prove the regularity
assumptions, or establish that either economic Jacobian is invertible.
The Python row PERMUTATION here is an algebraic SOURCE index mapping,
not a proof that a Python floating engine is semantically identical.
-/

namespace Ventura26LiquidityAllocation
namespace ProposedLocalScalarAugmented34Source

open ProposedLocalScalarEconomicSlice
open ProposedLocalScalarCommonPledgeLogZero

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- Project the Frechet derivative of any differentiable R^33 x R
output onto the chosen SOURCE economic row. -/
theorem source34_fderiv_firstCoord
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : E → (Fin 33 → ℝ) × ℝ) (x : E)
    (hF : DifferentiableAt ℝ F x) (d : E) (row : Fin 33) :
    (fderiv ℝ (fun y => (F y).1 row) x) d =
      ((fderiv ℝ F x) d).1 row := by
  rw [fderiv_apply hF.fst row, fderiv.fst hF]
  rfl

#print axioms source34_fderiv_firstCoord

/-- The 34th SOURCE funding-dual coordinate is the second component
of the Frechet derivative of the full augmented map. -/
theorem source34_fderiv_dualCoord
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : E → (Fin 33 → ℝ) × ℝ) (x : E)
    (hF : DifferentiableAt ℝ F x) (d : E) :
    (fderiv ℝ (fun y => (F y).2) x) d =
      ((fderiv ℝ F x) d).2 := by
  rw [fderiv.snd hF]
  rfl

#print axioms source34_fderiv_dualCoord

/-- The exact SOURCE 34x34 Jacobian at a positive root changes by
the verified row permutation composed with two nonzero scalings:
row 5: -1 (relative to normalized slack), and row 21: 1/V2.
NO equality of the full derivatives is assumed. -/
theorem source34_actual_full_fderiv_factorization_at_root
    (P : Primitives S) (I : InheritedState) (Z0 : LocalPrefixCoordinates)
    (dateOne recurrent : S) (tail : LocalPrefixContinuationRule)
    (wstar : (Fin 33 → ℝ) × ℝ)
    (hF : DifferentiableAt ℝ
      (fun w : (Fin 33 → ℝ) × ℝ =>
        augmentedBoundaryZeroResidual P I Z0 dateOne recurrent tail w.1 w.2)
      wstar)
    (hG : DifferentiableAt ℝ
      (fun w : (Fin 33 → ℝ) × ℝ =>
        sourceCanonicalTwoPledgeLog34 P I Z0 dateOne recurrent tail w.1 w.2)
      wstar)
    (hslack : DifferentiableAt ℝ
      (fun w : (Fin 33 → ℝ) × ℝ =>
        localBindingResidualWithSlack P I Z0 dateOne recurrent tail
          (reserveRemunerationSlice 0 w.2) w.1 (5 : Fin 33)) wstar)
    (hJ : DifferentiableAt ℝ
      (fun w : (Fin 33 → ℝ) × ℝ =>
        (localPrefixLogChart Z0 w.1).stateTwo.commonPledgeValue) wstar)
    (hV : DifferentiableAt ℝ
      (fun w : (Fin 33 → ℝ) × ℝ =>
        sourceDateOneCommonPledgeValuation
          (sourceReserveSlicePrimitives P w.2)
          (localPrefixLogChart Z0 w.1) dateOne recurrent tail) wstar)
    (hpositive : 0 <
      sourceDateOneCommonPledgeValuation
        (sourceReserveSlicePrimitives P wstar.2)
        (localPrefixLogChart Z0 wstar.1) dateOne recurrent tail)
    (hroot : augmentedBoundaryZeroResidual P I Z0 dateOne recurrent tail
      wstar.1 wstar.2 = (0, 0))
    (d : (Fin 33 → ℝ) × ℝ) :
    (fderiv ℝ
      (fun w : (Fin 33 → ℝ) × ℝ =>
        sourceCanonicalTwoPledgeLog34 P I Z0 dateOne recurrent tail w.1 w.2)
      wstar) d =
    source34RowsInPythonOrder
      (source34TwoRowRescale (-1)
        (sourceDateOneCommonPledgeValuation
          (sourceReserveSlicePrimitives P wstar.2)
          (localPrefixLogChart Z0 wstar.1) dateOne recurrent tail)⁻¹
        ((fderiv ℝ
          (fun w : (Fin 33 → ℝ) × ℝ =>
            augmentedBoundaryZeroResidual P I Z0 dateOne recurrent tail w.1 w.2)
          wstar) d)) := by
  let F : ((Fin 33 → ℝ) × ℝ) → (Fin 33 → ℝ) × ℝ :=
    fun w => augmentedBoundaryZeroResidual
      P I Z0 dateOne recurrent tail w.1 w.2
  let G : ((Fin 33 → ℝ) × ℝ) → (Fin 33 → ℝ) × ℝ :=
    fun w => sourceCanonicalTwoPledgeLog34
      P I Z0 dateOne recurrent tail w.1 w.2
  change (fderiv ℝ G wstar) d =
    source34RowsInPythonOrder
      (source34TwoRowRescale (-1)
        (sourceDateOneCommonPledgeValuation
          (sourceReserveSlicePrimitives P wstar.2)
          (localPrefixLogChart Z0 wstar.1) dateOne recurrent tail)⁻¹
        ((fderiv ℝ F wstar) d))
  apply Prod.ext
  · funext row
    change ((fderiv ℝ G wstar) d).1 row =
      (source34TwoRowRescale (-1)
        (sourceDateOneCommonPledgeValuation
          (sourceReserveSlicePrimitives P wstar.2)
          (localPrefixLogChart Z0 wstar.1) dateOne recurrent tail)⁻¹
        ((fderiv ℝ F wstar) d)).1
          (pythonToSource33Index row)
    rw [← source34_fderiv_firstCoord G wstar hG d row]
    have hr := source34_actual_twoPledge_fderiv_eachRow
      P I Z0 dateOne recurrent tail wstar hslack hJ hV
      hpositive hroot row
    rw [hr]
    have hdf := source34_fderiv_firstCoord F wstar hF d
      (pythonToSource33Index row)
    by_cases h5 : row = (5 : Fin 33)
    · subst row
      simpa [source34TwoRowRescale, pythonToSource33Index,
        hdf] using hdf
    · by_cases h21 : row = (21 : Fin 33)
      · subst row
        simpa [source34TwoRowRescale, pythonToSource33Index,
          hdf, smul_eq_mul] using hdf
      · have hsource5 : pythonToSource33Index row ≠ (5 : Fin 33) :=
          source34_python_nonfive_stays_nonfive row h5
        have hsource21 : pythonToSource33Index row ≠ (21 : Fin 33) := by
          intro heq
          have ht := congrArg sourceToPython33Index heq
          rw [sourceToPython33_pythonToSource33] at ht
          have hfix : sourceToPython33Index (21 : Fin 33) = 21 := by
            decide
          rw [hfix] at ht
          exact h21 ht
        simpa [source34TwoRowRescale, h5, h21, hsource5,
          hsource21] using hdf
  · change ((fderiv ℝ G wstar) d).2 = ((fderiv ℝ F wstar) d).2
    calc
      ((fderiv ℝ G wstar) d).2 =
          (fderiv ℝ (fun w => (G w).2) wstar) d :=
        (source34_fderiv_dualCoord G wstar hG d).symm
      _ = (fderiv ℝ (fun w => (F w).2) wstar) d := by
        rw [show (fun w => (G w).2) = (fun w => (F w).2) from
          funext (fun w => source34_twoPledge_dual_eq_source
            P I Z0 dateOne recurrent tail w.1 w.2)]
      _ = ((fderiv ℝ F wstar) d).2 :=
        source34_fderiv_dualCoord F wstar hF d

#print axioms source34_actual_full_fderiv_factorization_at_root

end ProposedLocalScalarAugmented34Source
end Ventura26LiquidityAllocation
