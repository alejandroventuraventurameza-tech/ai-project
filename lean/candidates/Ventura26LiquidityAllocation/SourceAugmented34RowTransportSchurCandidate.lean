import Ventura26LiquidityAllocation.SourceAugmented34SchurBlockCandidate

/-!
# The 34-row Schur multiplier is invariant under invertible SOURCE row changes

The 33 Python and 33 SOURCE residuals may differ by a nontrivial
invertible row operation T (permutation, normalization, Euler shear).
Therefore an entrywise comparison of J_Python to J_SOURCE is generally
WRONG: the correct candidate comparison is J_Python = T * J_SOURCE
in the first 33 rows, with the 34th funding-dual row unchanged.

These are precise abstract identities, not an assertion that the
existing Python row transformation actually equals SOURCE at the
economic boundary. That functional/derivative bridge remains OPEN.
-/

namespace Ventura26LiquidityAllocation

private abbrev Source33Row := Fin 33 → ℝ

/-- The inverse policy-response vector transforms contragrediently
under a left change of the first 33 equation rows. -/
theorem sourceAugmentedSchur_response_invariant_under_row_equiv
    (A T : Source33Row ≃ₗ[ℝ] Source33Row)
    (b : Source33Row) :
    (A.trans T).symm (T b) = A.symm b := by
  apply (A.trans T).injective
  simp

/-- In particular, the exact Schur scalar, and therefore its sign,
is unchanged by an invertible permutation/shear/rescaling of the
33 SOURCE economic equations. -/
theorem sourceAugmentedSchur_scalar_invariant_under_row_equiv
    (A T : Source33Row ≃ₗ[ℝ] Source33Row)
    (b : Source33Row) (c : Source33Row →ₗ[ℝ] ℝ) :
    c ((A.trans T).symm (T b)) = c (A.symm b) := by
  rw [sourceAugmentedSchur_response_invariant_under_row_equiv]

/-- The entire 34-dimensional linear block transforms by T in the
first 33 output coordinates, leaving the funding-dual row fixed. -/
theorem sourceAugmentedSchur_block_transports_by_row_equiv
    (A T : Source33Row ≃ₗ[ℝ] Source33Row)
    (b : Source33Row) (c : Source33Row →ₗ[ℝ] ℝ)
    (p : Source33Row × ℝ) :
    sourceAugmentedSchurBlock (A.trans T) (T b) c p =
      (T ((sourceAugmentedSchurBlock A b c p).1),
       (sourceAugmentedSchurBlock A b c p).2) := by
  rcases p with ⟨z, h⟩
  change (T (A z) + h • T b, c z) =
    (T (A z + h • b), c z)
  simp only [map_add, map_smul]

/-- The full 34-dimensional Jacobian rank condition is invariant
under the exact left row change T. This is the correct abstract
bridge for a SOURCE-to-Python 33-row candidate map. -/
theorem sourceAugmentedSchur_bijective_iff_transported_rows
    (A T : Source33Row ≃ₗ[ℝ] Source33Row)
    (b : Source33Row) (c : Source33Row →ₗ[ℝ] ℝ) :
    Function.Bijective (sourceAugmentedSchurBlock A b c) ↔
      Function.Bijective
        (sourceAugmentedSchurBlock (A.trans T) (T b) c) := by
  rw [sourceAugmentedSchurBlock_bijective_iff,
      sourceAugmentedSchurBlock_bijective_iff]
  rw [sourceAugmentedSchur_response_invariant_under_row_equiv]

#print axioms sourceAugmentedSchur_response_invariant_under_row_equiv
#print axioms sourceAugmentedSchur_scalar_invariant_under_row_equiv
#print axioms sourceAugmentedSchur_block_transports_by_row_equiv
#print axioms sourceAugmentedSchur_bijective_iff_transported_rows

end Ventura26LiquidityAllocation
