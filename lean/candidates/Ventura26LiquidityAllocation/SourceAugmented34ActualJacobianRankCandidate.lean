import Ventura26LiquidityAllocation.SourceAugmented34FullFrechetFactorizationCandidate

/-!
# Conditional bijectivity of the ACTUAL SOURCE 34x34 economic Jacobians

Unlike prior abstract lemmas, this result does not assume a derivative
identity. It obtains that identity from the exact original SOURCE
34 residuals and exact SOURCE two-collateral-log normalization, then
applies the certified nonzero output permutation/row scaling theorem.

Assumptions: a genuine augmented SOURCE root, positivity of the date-one
common pledge valuation, the local Frechet regularity of both SOURCE
vector residuals and the collateral inputs. There is NO assumption
that either Jacobian is invertible, and NO economic equilibrium
existence claim. Also no semantic identity to finite_irf.py.
-/

namespace Ventura26LiquidityAllocation
namespace ProposedLocalScalarAugmented34Source

open ProposedLocalScalarEconomicSlice
open ProposedLocalScalarCommonPledgeLogZero

variable {S : Type*} [Fintype S] [DecidableEq S]

theorem source34_actual_source_jacobian_bijective_iff_log_normalized
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
      wstar.1 wstar.2 = (0, 0)) :
    Function.Bijective
      (fderiv ℝ
        (fun w : (Fin 33 → ℝ) × ℝ =>
          sourceCanonicalTwoPledgeLog34 P I Z0 dateOne recurrent tail w.1 w.2)
        wstar) ↔
    Function.Bijective
      (fderiv ℝ
        (fun w : (Fin 33 → ℝ) × ℝ =>
          augmentedBoundaryZeroResidual P I Z0 dateOne recurrent tail w.1 w.2)
        wstar) := by
  let F : ((Fin 33 → ℝ) × ℝ) → (Fin 33 → ℝ) × ℝ :=
    fun w => augmentedBoundaryZeroResidual
      P I Z0 dateOne recurrent tail w.1 w.2
  let G : ((Fin 33 → ℝ) × ℝ) → (Fin 33 → ℝ) × ℝ :=
    fun w => sourceCanonicalTwoPledgeLog34
      P I Z0 dateOne recurrent tail w.1 w.2
  let V : ℝ :=
    sourceDateOneCommonPledgeValuation
      (sourceReserveSlicePrimitives P wstar.2)
      (localPrefixLogChart Z0 wstar.1) dateOne recurrent tail
  have hscale21 : V⁻¹ ≠ 0 := inv_ne_zero (ne_of_gt hpositive)
  have hfactor :
      (fun d : (Fin 33 → ℝ) × ℝ => (fderiv ℝ G wstar) d) =
      (fun d : (Fin 33 → ℝ) × ℝ =>
        source34RowsInPythonOrder
          (source34TwoRowRescale (-1) V⁻¹
            ((fderiv ℝ F wstar) d))) := by
    funext d
    exact source34_actual_full_fderiv_factorization_at_root
      P I Z0 dateOne recurrent tail wstar hF hG hslack hJ hV
      hpositive hroot d
  change Function.Bijective
      (fun d : (Fin 33 → ℝ) × ℝ => (fderiv ℝ G wstar) d) ↔
    Function.Bijective
      (fun d : (Fin 33 → ℝ) × ℝ => (fderiv ℝ F wstar) d)
  rw [hfactor]
  exact source34PythonPermutation_twoRowScale_bijective_iff
    (fun d : (Fin 33 → ℝ) × ℝ => (fderiv ℝ F wstar) d)
    (-1) V⁻¹ (by norm_num) hscale21

#print axioms source34_actual_source_jacobian_bijective_iff_log_normalized

end ProposedLocalScalarAugmented34Source
end Ventura26LiquidityAllocation
