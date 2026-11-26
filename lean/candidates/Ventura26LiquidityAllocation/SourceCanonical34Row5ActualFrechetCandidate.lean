import Ventura26LiquidityAllocation.SourceAugmented34CanonicalLogFrechetCandidate
import Ventura26LiquidityAllocation.SourceAugmented34PythonOrderSourceCanonicalCandidate

/-!
# Actual SOURCE 34 Jacobian: key row 5 and lower-right block

The 34-row canonical SOURCE map has the same OUTPUT ROW ORDER as Python.
Its row 5 is the *genuine SOURCE log collateral face*; its row 34
is the *genuine SOURCE L funding dual*, not a Python transcription.

At a genuine SOURCE binding root, row 5 has Jacobian
  (1 / Gamma_L) * D_z (face_L - Gamma_L),
and the lower-right h derivative is zero for any h.

These are exact Lean SOURCE identities and do not assert the
actual Python 34x34 matrix is a Jacobian of EconomicModel.lean.
-/

namespace Ventura26LiquidityAllocation
namespace ProposedLocalScalarAugmented34Source

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- In Python OUTPUT row 5, SOURCE's true Fréchet z-derivative is
+1/Gamma_L times the genuine raw collateral binding residual
derivative, at a true SOURCE root. The mapping fixes index 5. -/
theorem sourceCanonicalPythonOrder34_row5_actual_fderiv
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
          (ProposedLocalScalarEconomicSlice.reserveRemunerationSlice 0 h)
          z (5 : Fin 33)) zstar)
    (hroot : localReducedPrefixResidual LocalPrefixBranch.binding
      (sourceReserveSlicePrimitives P h) I
      (localPrefixLogChart Z0 zstar) dateOne recurrent tail
      LocalPrefixEquation.firmRegimeZeroL = 0)
    (hne : sourceBindingLPledgeFace (sourceReserveSlicePrimitives P h)
      (localPrefixLogChart Z0 zstar) ≠ 0) :
    fderiv ℝ
      (fun z : Fin 33 → ℝ =>
        (sourceCanonicalPythonOrder34 P I Z0
          dateOne recurrent tail z h).1 (5 : Fin 33)) zstar =
      (sourceBindingLPledgeFace (sourceReserveSlicePrimitives P h)
        (localPrefixLogChart Z0 zstar))⁻¹ •
      fderiv ℝ
        (fun z : Fin 33 → ℝ =>
          localReducedPrefixResidual LocalPrefixBranch.binding
            (sourceReserveSlicePrimitives P h) I
            (localPrefixLogChart Z0 z) dateOne recurrent tail
            LocalPrefixEquation.firmRegimeZeroL) zstar := by
  have hfun :
      (fun z : Fin 33 → ℝ =>
        (sourceCanonicalPythonOrder34 P I Z0
          dateOne recurrent tail z h).1 (5 : Fin 33)) =
      (fun z : Fin 33 → ℝ =>
        sourceCanonicalLogBindingResidual P I Z0
          dateOne recurrent tail z h (5 : Fin 33)) := by
    funext z
    simp [sourceCanonicalPythonOrder34,
      sourceRowsInPython33Order, pythonToSource33Index]
  rw [hfun]
  exact sourceCanonicalLogBinding_row5_fderiv_eq_raw_div_pledge
    P I Z0 dateOne recurrent tail zstar h
    hraw hpledge hslack hroot hne

#print axioms sourceCanonicalPythonOrder34_row5_actual_fderiv

/-- The 34th SOURCE economic residual (L funding dual) has NO direct
dependence on the monetary innovation h at FIXED log coordinates.
Therefore the bottom-right block of the genuine 34x34 Jacobian
is exactly zero. Other block entries are not inferred here. -/
theorem sourceCanonicalPythonOrder34_dual_fderiv_policy_zero
    (P : Primitives S) (I : InheritedState) (Z0 : LocalPrefixCoordinates)
    (dateOne recurrent : S) (tail : LocalPrefixContinuationRule)
    (z : Fin 33 → ℝ) (hstar : ℝ) :
    fderiv ℝ
      (fun h : ℝ => (sourceCanonicalPythonOrder34 P I Z0
        dateOne recurrent tail z h).2) hstar = 0 := by
  change fderiv ℝ
    (fun _ : ℝ => localNormalizedCollateralDualL P
      (localPrefixLogChart Z0 z)) hstar = 0
  simp

#print axioms sourceCanonicalPythonOrder34_dual_fderiv_policy_zero

end ProposedLocalScalarAugmented34Source
end Ventura26LiquidityAllocation
