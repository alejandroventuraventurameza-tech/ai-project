import Ventura26LiquidityAllocation.SourceAugmented34CanonicalLogFrechetCandidate
import Ventura26LiquidityAllocation.SourceAugmented34PythonOrderSourceCanonicalCandidate

/-!
# Joint 34-coordinate SOURCE row-5 Frechet scaling

The true SOURCE augmented 34 operator uses normalized L collateral
slack in its row 5, whereas sourceCanonicalPythonOrder34 uses
log(face_L/pledge_L). At a binding root, the joint (z,h)
derivative of the log row equals MINUS the derivative of the
normalized slack row, including the direction of the monetary policy
innovation h. This is the appropriate row-5 sign when the original
reference is augmentedBoundaryZeroResidual, not a raw level residual.

Differentiability of the source slack is explicit; no root existence,
SOURCE/Python floating operator equality, or Jacobian inverse is
asserted.
-/

namespace Ventura26LiquidityAllocation
namespace ProposedLocalScalarAugmented34Source

open ProposedLocalScalarEconomicSlice

variable {S : Type*} [Fintype S] [DecidableEq S]

theorem source_row5_joint34_log_fderiv_eq_neg_original_source
    (P : Primitives S) (I : InheritedState) (Z0 : LocalPrefixCoordinates)
    (dateOne recurrent : S) (tail : LocalPrefixContinuationRule)
    (wstar : (Fin 33 → ℝ) × ℝ)
    (hslack : DifferentiableAt ℝ
      (fun w : (Fin 33 → ℝ) × ℝ =>
        localBindingResidualWithSlack P I Z0 dateOne recurrent tail
          (reserveRemunerationSlice 0 w.2) w.1 (5 : Fin 33)) wstar)
    (hroot :
      (augmentedBoundaryZeroResidual P I Z0 dateOne recurrent tail
        wstar.1 wstar.2).1 (5 : Fin 33) = 0) :
    fderiv ℝ
      (fun w : (Fin 33 → ℝ) × ℝ =>
        (sourceCanonicalPythonOrder34 P I Z0 dateOne recurrent tail
          w.1 w.2).1 (5 : Fin 33)) wstar =
      - fderiv ℝ
        (fun w : (Fin 33 → ℝ) × ℝ =>
          (augmentedBoundaryZeroResidual P I Z0 dateOne recurrent tail
            w.1 w.2).1 (5 : Fin 33)) wstar := by
  have hfun :
      (fun w : (Fin 33 → ℝ) × ℝ =>
        (sourceCanonicalPythonOrder34 P I Z0 dateOne recurrent tail
          w.1 w.2).1 (5 : Fin 33)) =
      (fun w : (Fin 33 → ℝ) × ℝ =>
        Real.log (1 -
          localBindingResidualWithSlack P I Z0 dateOne recurrent tail
            (reserveRemunerationSlice 0 w.2) w.1 (5 : Fin 33))) := by
    funext w
    simpa [sourceCanonicalPythonOrder34, sourceRowsInPython33Order,
      pythonToSource33Index] using
      (sourceCanonicalLogBindingResidual_eq_log_slack_row
        P I Z0 dateOne recurrent tail w.1 w.2 (5 : Fin 33))
  have hzero :
      localBindingResidualWithSlack P I Z0 dateOne recurrent tail
        (reserveRemunerationSlice 0 wstar.2) wstar.1
        (5 : Fin 33) = 0 := hroot
  rw [hfun]
  simpa only [augmentedBoundaryZeroResidual] using
    (sourceFDeriv_log_one_sub_at_zero
      (fun w : (Fin 33 → ℝ) × ℝ =>
        localBindingResidualWithSlack P I Z0 dateOne recurrent tail
          (reserveRemunerationSlice 0 w.2) w.1 (5 : Fin 33))
      wstar hslack hzero)

#print axioms source_row5_joint34_log_fderiv_eq_neg_original_source

end ProposedLocalScalarAugmented34Source
end Ventura26LiquidityAllocation
