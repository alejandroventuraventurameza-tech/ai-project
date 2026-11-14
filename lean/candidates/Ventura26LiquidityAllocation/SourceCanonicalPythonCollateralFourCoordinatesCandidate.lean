import Ventura26LiquidityAllocation.SourceCanonical34Row5ActualFrechetCandidate

/-!
# Genuine SOURCE/Python-shaped L collateral row: four exact log coordinates

At every z, every remuneration innovation h, and without a binding-root
assumption, the genuine SOURCE 34-equation residual in Python output
row 5 equals a single explicitly displayed log expression involving
ONLY coordinates z_1, z_3, z_28 and z_29, the original SOURCE
pledgeability and depreciation, and the pinned economic reference levels.

The four coordinate indices are inherited from the original SOURCE
LocalPrefixCoordinates vector. The real-arithmetic expression is
the equation-body contract for finite_irf.prefix_residual's binding
L regime row, which is independently checked using Python AST in CI.

This proves an exact formula in genuine SOURCE, not a proof that every
Python float64 operation equals its real-arithmetic counterpart.
-/

namespace Ventura26LiquidityAllocation
namespace ProposedLocalScalarAugmented34Source

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- A transparent SOURCE real-arithmetic clone of the four-coordinate
Python L binding logarithm. This depends on precisely the coordinates
x1[3], x1[1], u1[5], u1[6], in that order. -/
noncomputable def sourcePythonLBindingFourCoordinates
    (P : Primitives S) (Z0 : LocalPrefixCoordinates)
    (z : Fin 33 → ℝ) : ℝ :=
  Real.log
    ((Z0.stateOne.firmFaceL * Real.exp (z 3)) /
      ((P.pledgeability FirmType.L *
          (1 - P.depreciation) *
          (Z0.controlsOne.inflation * Real.exp (z 28)) *
          (Z0.controlsOne.capitalPrice * Real.exp (z 29))) *
        (Z0.stateOne.capitalL * Real.exp (z 1))))

/-- The genuine SOURCE log-collateral row in Python OUTPUT index 5
is exactly the explicit four-coordinate formula. Crucially,
the equality holds OFF ROOT, at arbitrary h, and does not assume
any numerical Python approximation or imported matrix. -/
theorem sourceCanonicalPythonOrder34_row5_eq_fourCoordinates
    (P : Primitives S) (I : InheritedState)
    (Z0 : LocalPrefixCoordinates) (dateOne recurrent : S)
    (tail : LocalPrefixContinuationRule)
    (z : Fin 33 → ℝ) (h : ℝ) :
    (sourceCanonicalPythonOrder34 P I Z0 dateOne recurrent tail z h).1
      (5 : Fin 33) =
    sourcePythonLBindingFourCoordinates P Z0 z := by
  simp [sourceCanonicalPythonOrder34,
    sourceRowsInPython33Order, pythonToSource33Index,
    sourceCanonicalLogBindingResidual,
    sourceReserveSlicePrimitives,
    sourceBindingLPledgeFace,
    sourcePythonLBindingFourCoordinates,
    localPrefixLogChart,
    localPrefixCoordinatesOfVector,
    localPrefixCoordinatesVector]

#print axioms sourceCanonicalPythonOrder34_row5_eq_fourCoordinates

/-- Exact *nonlinear functional sparsity*: varying any of the other
29 endogenous log coordinates, or varying reserve remuneration h,
cannot change the genuine SOURCE canonical row 5. This proves
support of the residual function, not only its numerical Jacobian. -/
theorem sourceCanonicalPythonOrder34_row5_only_four_coordinates
    (P : Primitives S) (I : InheritedState)
    (Z0 : LocalPrefixCoordinates) (dateOne recurrent : S)
    (tail : LocalPrefixContinuationRule)
    (z z' : Fin 33 → ℝ) (h h' : ℝ)
    (h1 : z 1 = z' 1)
    (h3 : z 3 = z' 3)
    (h28 : z 28 = z' 28)
    (h29 : z 29 = z' 29) :
    (sourceCanonicalPythonOrder34 P I Z0 dateOne recurrent tail z h).1
      (5 : Fin 33) =
    (sourceCanonicalPythonOrder34 P I Z0 dateOne recurrent tail z' h').1
      (5 : Fin 33) := by
  rw [sourceCanonicalPythonOrder34_row5_eq_fourCoordinates,
      sourceCanonicalPythonOrder34_row5_eq_fourCoordinates]
  simp [sourcePythonLBindingFourCoordinates, h1, h3, h28, h29]

#print axioms sourceCanonicalPythonOrder34_row5_only_four_coordinates

end ProposedLocalScalarAugmented34Source
end Ventura26LiquidityAllocation
