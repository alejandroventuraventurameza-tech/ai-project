import Ventura26LiquidityAllocation.SourceAugmented34CanonicalLogBoundaryCandidate
import Ventura26LiquidityAllocation.SourceBindingSlackRowFrechetCandidate
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Genuine SOURCE logarithmic collateral-row Frechet differential

At a SOURCE binding root, the canonical log-face row is the negative
logarithm of the normalized slack complement. Hence its derivative is
minus the slack derivative. Since the normalized slack is the NEGATIVE
raw binding residual divided by the positive pledge face, the
canonical log-face row has POSITIVE Jacobian scaling +1/Gamma of the
raw SOURCE binding row.

This fixes the exact sign of the row-5 SOURCE/Python-shaped Jacobian
transport at nonzero remuneration shock h. It does not prove that
the Python engine actually evaluates the same economic function,
or certify existence/invertibility of any economic root.
-/

namespace Ventura26LiquidityAllocation
namespace ProposedLocalScalarAugmented34Source

open ProposedLocalScalarEconomicSlice

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- Abstract Fréchet identity for log(1-f) at a zero of f.
The sign is strictly NEGATIVE, an essential distinction between
normalized slack and log face/pledge diagnostics. -/
theorem sourceFDeriv_log_one_sub_at_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → ℝ) (x : E)
    (hf : DifferentiableAt ℝ f x) (hf0 : f x = 0) :
    fderiv ℝ (fun y => Real.log (1 - f y)) x =
      -fderiv ℝ f x := by
  have hone : DifferentiableAt ℝ (fun _ : E => (1 : ℝ)) x :=
    differentiableAt_const (1 : ℝ)
  have hinner : DifferentiableAt ℝ (fun y : E => (1 : ℝ) - f y) x :=
    hone.sub hf
  have hne : (1 : ℝ) - f x ≠ 0 := by simp [hf0]
  rw [fderiv.log hinner hne]
  have hsub : fderiv ℝ (fun y : E => (1 : ℝ) - f y) x =
      -fderiv ℝ f x := by
    rw [fderiv_fun_sub hone hf]
    simp
  rw [hsub, hf0]
  simp

#print axioms sourceFDeriv_log_one_sub_at_zero

/-- Exactly at a genuine 33-row binding root, the actual SOURCE
log-face collateral row derivative is minus the source normalized
slack row derivative. No approximation, and h may be nonzero. -/
theorem sourceCanonicalLogBinding_row5_fderiv_eq_neg_slack
    (P : Primitives S) (I : InheritedState) (Z0 : LocalPrefixCoordinates)
    (dateOne recurrent : S) (tail : LocalPrefixContinuationRule)
    (zstar : Fin 33 → ℝ) (h : ℝ)
    (hslack : DifferentiableAt ℝ
      (fun z : Fin 33 → ℝ =>
        localBindingResidualWithSlack P I Z0 dateOne recurrent tail
          (reserveRemunerationSlice 0 h) z (5 : Fin 33)) zstar)
    (hroot : localBindingResidualWithSlack P I Z0 dateOne recurrent tail
      (reserveRemunerationSlice 0 h) zstar (5 : Fin 33) = 0) :
    fderiv ℝ
      (fun z : Fin 33 → ℝ =>
        sourceCanonicalLogBindingResidual P I Z0
          dateOne recurrent tail z h (5 : Fin 33)) zstar =
    -fderiv ℝ
      (fun z : Fin 33 → ℝ =>
        localBindingResidualWithSlack P I Z0 dateOne recurrent tail
          (reserveRemunerationSlice 0 h) z (5 : Fin 33)) zstar := by
  have hfun :
      (fun z : Fin 33 → ℝ =>
        sourceCanonicalLogBindingResidual P I Z0
          dateOne recurrent tail z h (5 : Fin 33)) =
      (fun z : Fin 33 → ℝ =>
        Real.log (1 - localBindingResidualWithSlack P I Z0
          dateOne recurrent tail
          (reserveRemunerationSlice 0 h) z (5 : Fin 33))) := by
    funext z
    simpa using (sourceCanonicalLogBindingResidual_eq_log_slack_row
      P I Z0 dateOne recurrent tail z h (5 : Fin 33))
  rw [hfun]
  exact sourceFDeriv_log_one_sub_at_zero _ zstar hslack hroot

#print axioms sourceCanonicalLogBinding_row5_fderiv_eq_neg_slack

/-- The exact economically meaningful row scaling:
  D_z log(face_L/Gamma_L) = + (1/Gamma_L) D_z rawBinding_L
at a genuine SOURCE binding root under arbitrary h.
Hypotheses are explicit regularity/nondegeneracy requirements;
the claim neither supplies a SOURCE root nor matches the Python
floating AD matrix to the Lean fderiv. -/
theorem sourceCanonicalLogBinding_row5_fderiv_eq_raw_div_pledge
    (P : Primitives S) (I : InheritedState) (Z0 : LocalPrefixCoordinates)
    (dateOne recurrent : S) (tail : LocalPrefixContinuationRule)
    (zstar : Fin 33 → ℝ) (h : ℝ)
    (hraw : DifferentiableAt ℝ
      (fun z : Fin 33 → ℝ =>
        localReducedPrefixResidual LocalPrefixBranch.binding
          (sourceReserveSlicePrimitives P h) I
          (localPrefixLogChart Z0 z) dateOne recurrent tail
          LocalPrefixEquation.firmRegimeZeroL) zstar)
    (hpledge : DifferentiableAt ℝ
      (fun z : Fin 33 → ℝ =>
        sourceBindingLPledgeFace (sourceReserveSlicePrimitives P h)
          (localPrefixLogChart Z0 z)) zstar)
    (hslack : DifferentiableAt ℝ
      (fun z : Fin 33 → ℝ =>
        localBindingResidualWithSlack P I Z0 dateOne recurrent tail
          (reserveRemunerationSlice 0 h) z (5 : Fin 33)) zstar)
    (hroot : localReducedPrefixResidual LocalPrefixBranch.binding
      (sourceReserveSlicePrimitives P h) I
      (localPrefixLogChart Z0 zstar) dateOne recurrent tail
      LocalPrefixEquation.firmRegimeZeroL = 0)
    (hne : sourceBindingLPledgeFace (sourceReserveSlicePrimitives P h)
      (localPrefixLogChart Z0 zstar) ≠ 0) :
    fderiv ℝ
      (fun z : Fin 33 → ℝ =>
        sourceCanonicalLogBindingResidual P I Z0
          dateOne recurrent tail z h (5 : Fin 33)) zstar =
      (sourceBindingLPledgeFace (sourceReserveSlicePrimitives P h)
        (localPrefixLogChart Z0 zstar))⁻¹ •
      fderiv ℝ
        (fun z : Fin 33 → ℝ =>
          localReducedPrefixResidual LocalPrefixBranch.binding
            (sourceReserveSlicePrimitives P h) I
            (localPrefixLogChart Z0 z) dateOne recurrent tail
            LocalPrefixEquation.firmRegimeZeroL) zstar := by
  have hmodfun :
      (fun z : Fin 33 → ℝ =>
        localBindingResidualWithSlack P I Z0 dateOne recurrent tail
          (reserveRemunerationSlice 0 h) z (5 : Fin 33)) =
      (fun z : Fin 33 → ℝ =>
        localNormalizedSlackL (sourceReserveSlicePrimitives P h)
          (localPrefixLogChart Z0 z)) := by
    funext z
    simpa [localPrefixEquationOfIndex] using
      (sourceBinding33_nonzeroPolicy_eachRow
        P I Z0 dateOne recurrent tail z h (5 : Fin 33))
  have hslackroot :
      localBindingResidualWithSlack P I Z0 dateOne recurrent tail
        (reserveRemunerationSlice 0 h) zstar (5 : Fin 33) = 0 := by
    rw [hmodfun]
    exact (sourceBindingNormalizedSlackL_zero_iff_rawL_zero
      (sourceReserveSlicePrimitives P h) I
      (localPrefixLogChart Z0 zstar) dateOne recurrent tail hne).mpr hroot
  have hlog := sourceCanonicalLogBinding_row5_fderiv_eq_neg_slack
    P I Z0 dateOne recurrent tail zstar h hslack hslackroot
  rw [hmodfun] at hlog
  rw [hlog, sourceBindingSlackL_fderiv_eq_scaled_raw_at_root
    (sourceReserveSlicePrimitives P h) I Z0
    dateOne recurrent tail zstar hraw hpledge hroot hne]
  simp

#print axioms sourceCanonicalLogBinding_row5_fderiv_eq_raw_div_pledge

end ProposedLocalScalarAugmented34Source
end Ventura26LiquidityAllocation
