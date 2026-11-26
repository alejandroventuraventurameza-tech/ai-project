import Ventura26LiquidityAllocation.SourceAugmented34RowFrechetFactorizationCandidate

/-!
# SOURCE 34 positive-root differentiability of the two-pledge log map

This module removes an independent differentiability assumption for
the 34-output SOURCE log-normalized residual. At a genuine positive
augmented SOURCE root, differentiability of the ORIGINAL 34-output
economic map and of the two date-two pledge-value primitives implies
differentiability of the transformed 34-output map.

The row-5 log is locally log(1 - normalizedSlackL); row 21 is the log
of the positive J2/V2 ratio; all other 31 rows and the 34th dual are
unchanged after the audited permutation.

No existence of a SOURCE root or Jacobian invertibility is asserted.
-/

namespace Ventura26LiquidityAllocation
namespace ProposedLocalScalarAugmented34Source

open ProposedLocalScalarEconomicSlice
open ProposedLocalScalarCommonPledgeLogZero

variable {S : Type*} [Fintype S] [DecidableEq S]

theorem source34_twoPledge_differentiableAt_of_original_at_positive_root
    (P : Primitives S) (I : InheritedState) (Z0 : LocalPrefixCoordinates)
    (dateOne recurrent : S) (tail : LocalPrefixContinuationRule)
    (wstar : (Fin 33 → ℝ) × ℝ)
    (hF : DifferentiableAt ℝ
      (fun w : (Fin 33 → ℝ) × ℝ =>
        augmentedBoundaryZeroResidual P I Z0 dateOne recurrent tail w.1 w.2)
      wstar)
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
    DifferentiableAt ℝ
      (fun w : (Fin 33 → ℝ) × ℝ =>
        sourceCanonicalTwoPledgeLog34 P I Z0 dateOne recurrent tail w.1 w.2)
      wstar := by
  let F : ((Fin 33 → ℝ) × ℝ) → (Fin 33 → ℝ) × ℝ :=
    fun w => augmentedBoundaryZeroResidual
      P I Z0 dateOne recurrent tail w.1 w.2
  let G : ((Fin 33 → ℝ) × ℝ) → (Fin 33 → ℝ) × ℝ :=
    fun w => sourceCanonicalTwoPledgeLog34
      P I Z0 dateOne recurrent tail w.1 w.2
  let J : ((Fin 33 → ℝ) × ℝ) → ℝ :=
    fun w => (localPrefixLogChart Z0 w.1).stateTwo.commonPledgeValue
  let V : ((Fin 33 → ℝ) × ℝ) → ℝ :=
    fun w => sourceDateOneCommonPledgeValuation
      (sourceReserveSlicePrimitives P w.2)
      (localPrefixLogChart Z0 w.1) dateOne recurrent tail
  have hFrows : ∀ row : Fin 33,
      DifferentiableAt ℝ (fun w => (F w).1 row) wstar :=
    (differentiableAt_pi).mp hF.fst
  have hslackzero :
      localBindingResidualWithSlack P I Z0 dateOne recurrent tail
        (reserveRemunerationSlice 0 wstar.2) wstar.1
        (5 : Fin 33) = 0 := by
    have h := congrArg
      (fun v : (Fin 33 → ℝ) × ℝ => v.1 (5 : Fin 33)) hroot
    simpa [augmentedBoundaryZeroResidual] using h
  have hslack : DifferentiableAt ℝ
      (fun w : (Fin 33 → ℝ) × ℝ =>
        localBindingResidualWithSlack P I Z0 dateOne recurrent tail
          (reserveRemunerationSlice 0 w.2) w.1 (5 : Fin 33)) wstar := by
    simpa only [F, augmentedBoundaryZeroResidual] using
      hFrows (5 : Fin 33)
  have hlog5 : DifferentiableAt ℝ
      (fun w : (Fin 33 → ℝ) × ℝ =>
        Real.log (1 - localBindingResidualWithSlack
          P I Z0 dateOne recurrent tail
          (reserveRemunerationSlice 0 w.2) w.1 (5 : Fin 33))) wstar := by
    have hinner : DifferentiableAt ℝ
        (fun w : (Fin 33 → ℝ) × ℝ =>
          (1 : ℝ) - localBindingResidualWithSlack
            P I Z0 dateOne recurrent tail
            (reserveRemunerationSlice 0 w.2) w.1 (5 : Fin 33)) wstar :=
      (differentiableAt_const (1 : ℝ)).sub hslack
    exact hinner.log (by simp [hslackzero])
  have hsourceRow21 : ∀ w : (Fin 33 → ℝ) × ℝ,
      (sourceCanonicalPythonOrder34 P I Z0 dateOne recurrent tail
        w.1 w.2).1 (21 : Fin 33) = J w - V w := by
    intro w
    rw [sourceCanonicalPythonOrder34_row21_eq_source_pledge_level]
    exact source_common_pledge_level_row
      (sourceReserveSlicePrimitives P w.2) I
      (localPrefixLogChart Z0 w.1) dateOne recurrent tail
  have hsourceRoot21 :
      (sourceCanonicalPythonOrder34 P I Z0 dateOne recurrent tail
        wstar.1 wstar.2).1 (21 : Fin 33) = 0 := by
    rw [source34_python_row21_eq_augmented_source]
    have hz := congrArg
      (fun v : (Fin 33 → ℝ) × ℝ => v.1 (21 : Fin 33)) hroot
    simpa using hz
  have hJV : J wstar = V wstar := by
    rw [hsourceRow21 wstar] at hsourceRoot21
    exact sub_eq_zero.mp hsourceRoot21
  have hratio : DifferentiableAt ℝ (fun w => J w / V w) wstar := by
    simpa only [div_eq_mul_inv] using
      hJ.mul (hV.inv (ne_of_gt hpositive))
  have hratio_ne : J wstar / V wstar ≠ 0 := by
    rw [hJV, div_self (ne_of_gt hpositive)]
    norm_num
  have hlog21 : DifferentiableAt ℝ
      (fun w => Real.log (J w / V w)) wstar :=
    hratio.log hratio_ne
  have hGrows : ∀ row : Fin 33,
      DifferentiableAt ℝ (fun w => (G w).1 row) wstar := by
    intro row
    by_cases h5 : row = (5 : Fin 33)
    · subst row
      have hfun :
          (fun w : (Fin 33 → ℝ) × ℝ =>
            (G w).1 (5 : Fin 33)) =
          (fun w : (Fin 33 → ℝ) × ℝ =>
            Real.log (1 - localBindingResidualWithSlack
              P I Z0 dateOne recurrent tail
              (reserveRemunerationSlice 0 w.2) w.1 (5 : Fin 33))) := by
        funext w
        simpa [G, sourceCanonicalTwoPledgeLog34,
          sourceCanonicalPythonOrder34, sourceRowsInPython33Order,
          pythonToSource33Index] using
          (sourceCanonicalLogBindingResidual_eq_log_slack_row
            P I Z0 dateOne recurrent tail w.1 w.2 (5 : Fin 33))
      rw [hfun]
      exact hlog5
    · by_cases h21 : row = (21 : Fin 33)
      · subst row
        have hfun :
            (fun w : (Fin 33 → ℝ) × ℝ =>
              (G w).1 (21 : Fin 33)) =
            (fun w : (Fin 33 → ℝ) × ℝ =>
              Real.log (J w / V w)) := by
          funext w
          simp [G, sourceCanonicalTwoPledgeLog34, J, V]
        rw [hfun]
        exact hlog21
      · have hfun :
            (fun w : (Fin 33 → ℝ) × ℝ => (G w).1 row) =
            (fun w : (Fin 33 → ℝ) × ℝ =>
              (F w).1 (pythonToSource33Index row)) := by
          funext w
          exact source34_twoPledge_unmodified_row_eq_source
            P I Z0 dateOne recurrent tail w.1 w.2 row h5 h21
        rw [hfun]
        exact hFrows (pythonToSource33Index row)
  have hfirst : DifferentiableAt ℝ (fun w => (G w).1) wstar :=
    (differentiableAt_pi).mpr hGrows
  have hdual : DifferentiableAt ℝ (fun w => (G w).2) wstar := by
    have hfun :
        (fun w : (Fin 33 → ℝ) × ℝ => (G w).2) =
        (fun w : (Fin 33 → ℝ) × ℝ => (F w).2) := by
      funext w
      exact source34_twoPledge_dual_eq_source
        P I Z0 dateOne recurrent tail w.1 w.2
    rw [hfun]
    exact hF.snd
  exact hfirst.prodMk hdual

#print axioms source34_twoPledge_differentiableAt_of_original_at_positive_root

end ProposedLocalScalarAugmented34Source
end Ventura26LiquidityAllocation
