import Ventura26LiquidityAllocation.SourceAugmented34PermutationRescaleCandidate

/-!
# SOURCE 34-coordinate exact functional correspondence except rows 5 and 21

The canonical two-pledge log map changes two collateral equations. All
remaining economic row FUNCTIONS agree identically with the original
augmented SOURCE boundary after the proved SOURCE-to-Python permutation.
This exact pointwise agreement implies derivative equality on every
unmodified row, without an additional differentiability hypothesis.

The scalar 34th funding-dual residual is identical in both maps.
This is a SOURCE/SOURCE identity, not an assertion about floating Python.
-/

namespace Ventura26LiquidityAllocation
namespace ProposedLocalScalarAugmented34Source

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- Python-order row 21 before taking logs is exactly the original
augmented SOURCE common-pledge row in SOURCE order. -/
theorem source34_python_row21_eq_augmented_source
    (P : Primitives S) (I : InheritedState) (Z0 : LocalPrefixCoordinates)
    (dateOne recurrent : S) (tail : LocalPrefixContinuationRule)
    (z : Fin 33 → ℝ) (h : ℝ) :
    (sourceCanonicalPythonOrder34 P I Z0 dateOne recurrent tail z h).1
      (21 : Fin 33) =
    (augmentedBoundaryZeroResidual P I Z0 dateOne recurrent tail z h).1
      (21 : Fin 33) := by
  simp [sourceCanonicalPythonOrder34, sourceRowsInPython33Order,
    pythonToSource33Index, sourceCanonicalLogBindingResidual,
    augmentedBoundaryZeroResidual]

#print axioms source34_python_row21_eq_augmented_source

/-- Source-to-Python permutation cannot move any other row into
the exceptional SOURCE L collateral row 5. -/
theorem source34_python_nonfive_stays_nonfive
    (row : Fin 33) (h5 : row ≠ (5 : Fin 33)) :
    pythonToSource33Index row ≠ (5 : Fin 33) := by
  intro heq
  have ht := congrArg sourceToPython33Index heq
  rw [sourceToPython33_pythonToSource33] at ht
  have hfix : sourceToPython33Index (5 : Fin 33) = 5 := by decide
  rw [hfix] at ht
  exact h5 ht

#print axioms source34_python_nonfive_stays_nonfive

/-- Every other SOURCE economic equation is pointwise unchanged
in the canonical Python-row output after the exact permutation. -/
theorem source34_twoPledge_unmodified_row_eq_source
    (P : Primitives S) (I : InheritedState) (Z0 : LocalPrefixCoordinates)
    (dateOne recurrent : S) (tail : LocalPrefixContinuationRule)
    (z : Fin 33 → ℝ) (h : ℝ)
    (row : Fin 33)
    (h5 : row ≠ (5 : Fin 33)) (h21 : row ≠ (21 : Fin 33)) :
    (sourceCanonicalTwoPledgeLog34 P I Z0 dateOne recurrent tail z h).1 row =
    (augmentedBoundaryZeroResidual P I Z0 dateOne recurrent tail z h).1
      (pythonToSource33Index row) := by
  have hsource5 := source34_python_nonfive_stays_nonfive row h5
  simp [sourceCanonicalTwoPledgeLog34, sourceCanonicalPythonOrder34,
    sourceRowsInPython33Order, sourceCanonicalLogBindingResidual,
    augmentedBoundaryZeroResidual, h21, hsource5]

#print axioms source34_twoPledge_unmodified_row_eq_source

/-- The 34th normalized SOURCE funding-dual row is literally identical. -/
theorem source34_twoPledge_dual_eq_source
    (P : Primitives S) (I : InheritedState) (Z0 : LocalPrefixCoordinates)
    (dateOne recurrent : S) (tail : LocalPrefixContinuationRule)
    (z : Fin 33 → ℝ) (h : ℝ) :
    (sourceCanonicalTwoPledgeLog34 P I Z0 dateOne recurrent tail z h).2 =
      (augmentedBoundaryZeroResidual P I Z0 dateOne recurrent tail z h).2 := by
  rfl

#print axioms source34_twoPledge_dual_eq_source

end ProposedLocalScalarAugmented34Source
end Ventura26LiquidityAllocation
