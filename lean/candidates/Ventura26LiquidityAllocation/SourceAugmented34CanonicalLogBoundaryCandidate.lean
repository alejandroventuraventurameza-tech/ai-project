import Ventura26LiquidityAllocation.SourceBinding33NonzeroPolicyLogRow5Candidate

/-!
# Exact SOURCE 34-boundary with Python-shaped log collateral row

The *genuine* SOURCE modified binding boundary uses its normalized L
collateral slack in row 5; the frozen Python binding branch uses
log(faceL/pledgeL). This module defines a canonical log-face 34-row map
using only the original SOURCE economic definitions, and proves that
its full zero set is IDENTICAL to the genuine SOURCE augmented zero
set at any reserve-remuneration innovation h, on the positive face
ratio domain.

This is an exact functional bridge INSIDE SOURCE, not a proof that
finite_irf.py computes the same source map. The existence of an exact
economic 34-dimensional root and source/Python operator equality
remain open.
-/

namespace Ventura26LiquidityAllocation
namespace ProposedLocalScalarAugmented34Source

open ProposedLocalScalarEconomicSlice

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- The exact SOURCE 33-row modified binding residual, transformed
only in the L collateral row from normalized slack to a logarithm
of the face-to-pledge ratio. The other 32 rows and the intervention
are the ORIGINAL source equations, not Python transcriptions. -/
noncomputable def sourceCanonicalLogBindingResidual
    (P : Primitives S) (I : InheritedState) (Z0 : LocalPrefixCoordinates)
    (dateOne recurrent : S) (tail : LocalPrefixContinuationRule)
    (z : Fin 33 → ℝ) (h : ℝ) : Fin 33 → ℝ :=
  fun row =>
    if row = (5 : Fin 33) then
      Real.log ((localPrefixLogChart Z0 z).stateOne.firmFaceL /
        sourceBindingLPledgeFace (sourceReserveSlicePrimitives P h)
          (localPrefixLogChart Z0 z))
    else
      localBindingResidualWithSlack P I Z0 dateOne recurrent tail
        (reserveRemunerationSlice 0 h) z row

/-- The Python-shaped log collateral row is exactly log(1-S_L)
with S_L the ORIGINAL SOURCE modified slack. This is a pointwise
SOURCE functional equality, for every z and h, without a root. -/
theorem sourceCanonicalLogBindingResidual_eq_log_slack_row
    (P : Primitives S) (I : InheritedState) (Z0 : LocalPrefixCoordinates)
    (dateOne recurrent : S) (tail : LocalPrefixContinuationRule)
    (z : Fin 33 → ℝ) (h : ℝ) (row : Fin 33) :
    sourceCanonicalLogBindingResidual P I Z0 dateOne recurrent tail z h row =
    if row = (5 : Fin 33) then
      Real.log (1 - localBindingResidualWithSlack P I Z0
        dateOne recurrent tail (reserveRemunerationSlice 0 h)
        z (5 : Fin 33))
    else
      localBindingResidualWithSlack P I Z0 dateOne recurrent tail
        (reserveRemunerationSlice 0 h) z row := by
  by_cases hrow : row = (5 : Fin 33)
  · subst row
    simpa [sourceCanonicalLogBindingResidual] using
      (sourceBinding33_nonzeroPolicy_logFace_eq_logSlackComplement
        P I Z0 dateOne recurrent tail z h)
  · simp [sourceCanonicalLogBindingResidual, hrow]

#print axioms sourceCanonicalLogBindingResidual_eq_log_slack_row

/-- With a positive collateral face/pledge ratio, each log-normalized
SOURCE row vanishes iff its ORIGINAL normalized-slack SOURCE row
vanishes. Other 32 rows are definitionally identical. -/
theorem sourceCanonicalLogBindingResidual_row_zero_iff
    (P : Primitives S) (I : InheritedState) (Z0 : LocalPrefixCoordinates)
    (dateOne recurrent : S) (tail : LocalPrefixContinuationRule)
    (z : Fin 33 → ℝ) (h : ℝ) (row : Fin 33)
    (hp : 0 < (localPrefixLogChart Z0 z).stateOne.firmFaceL /
      sourceBindingLPledgeFace (sourceReserveSlicePrimitives P h)
        (localPrefixLogChart Z0 z)) :
    sourceCanonicalLogBindingResidual P I Z0 dateOne recurrent tail z h row = 0 ↔
      localBindingResidualWithSlack P I Z0 dateOne recurrent tail
        (reserveRemunerationSlice 0 h) z row = 0 := by
  by_cases hrow : row = (5 : Fin 33)
  · subst row
    simpa [sourceCanonicalLogBindingResidual] using
      (sourceBinding33_nonzeroPolicy_logFace_zero_iff_slack_zero
        P I Z0 dateOne recurrent tail z h hp)
  · simp [sourceCanonicalLogBindingResidual, hrow]

#print axioms sourceCanonicalLogBindingResidual_row_zero_iff

/-- Exact SOURCE 33-row zero-set invariance under log conversion,
at any h and on the positive face/pledge chart. -/
theorem sourceCanonicalLogBindingResidual_all_zero_iff
    (P : Primitives S) (I : InheritedState) (Z0 : LocalPrefixCoordinates)
    (dateOne recurrent : S) (tail : LocalPrefixContinuationRule)
    (z : Fin 33 → ℝ) (h : ℝ)
    (hp : 0 < (localPrefixLogChart Z0 z).stateOne.firmFaceL /
      sourceBindingLPledgeFace (sourceReserveSlicePrimitives P h)
        (localPrefixLogChart Z0 z)) :
    (∀ row : Fin 33,
      sourceCanonicalLogBindingResidual P I Z0 dateOne recurrent tail z h row = 0) ↔
    (∀ row : Fin 33,
      localBindingResidualWithSlack P I Z0 dateOne recurrent tail
        (reserveRemunerationSlice 0 h) z row = 0) := by
  constructor
  · intro hz row
    exact (sourceCanonicalLogBindingResidual_row_zero_iff
      P I Z0 dateOne recurrent tail z h row hp).mp (hz row)
  · intro hz row
    exact (sourceCanonicalLogBindingResidual_row_zero_iff
      P I Z0 dateOne recurrent tail z h row hp).mpr (hz row)

#print axioms sourceCanonicalLogBindingResidual_all_zero_iff

/-- The exact SOURCE 33+1 residual, with the log collateral face
in row 5 and the SAME SOURCE L funding dual as the 34th row. -/
noncomputable def sourceCanonicalLogBoundary
    (P : Primitives S) (I : InheritedState) (Z0 : LocalPrefixCoordinates)
    (dateOne recurrent : S) (tail : LocalPrefixContinuationRule)
    (z : Fin 33 → ℝ) (h : ℝ) : (Fin 33 → ℝ) × ℝ :=
  (sourceCanonicalLogBindingResidual P I Z0 dateOne recurrent tail z h,
   localNormalizedCollateralDualL P (localPrefixLogChart Z0 z))

/-- At ANY reserve-rate innovation, the 34-row canonical log
SOURCE map has precisely the same solutions as the ACTUAL 34-row
SOURCE normalized-slack boundary operator. No Python hypothesis. -/
theorem sourceCanonicalLogBoundary_eq_zero_iff_original_boundary_zero
    (P : Primitives S) (I : InheritedState) (Z0 : LocalPrefixCoordinates)
    (dateOne recurrent : S) (tail : LocalPrefixContinuationRule)
    (z : Fin 33 → ℝ) (h : ℝ)
    (hp : 0 < (localPrefixLogChart Z0 z).stateOne.firmFaceL /
      sourceBindingLPledgeFace (sourceReserveSlicePrimitives P h)
        (localPrefixLogChart Z0 z)) :
    sourceCanonicalLogBoundary P I Z0 dateOne recurrent tail z h = (0, 0) ↔
      augmentedBoundaryZeroResidual P I Z0 dateOne recurrent tail z h = (0, 0) := by
  constructor
  · intro hz
    have hfirst : ∀ row : Fin 33,
        sourceCanonicalLogBindingResidual P I Z0 dateOne recurrent tail z h row = 0 := by
      intro row
      have h := congrArg (fun f : Fin 33 → ℝ => f row) (congrArg Prod.fst hz)
      simpa [sourceCanonicalLogBoundary] using h
    have hlast : localNormalizedCollateralDualL P
        (localPrefixLogChart Z0 z) = 0 := by
      simpa [sourceCanonicalLogBoundary] using congrArg Prod.snd hz
    apply (augmentedBoundaryZeroResidual_eq_zero_iff
      P I Z0 dateOne recurrent tail z h).mpr
    exact ⟨(sourceCanonicalLogBindingResidual_all_zero_iff
      P I Z0 dateOne recurrent tail z h hp).mp hfirst, hlast⟩
  · intro hz
    have hboth := (augmentedBoundaryZeroResidual_eq_zero_iff
      P I Z0 dateOne recurrent tail z h).mp hz
    apply Prod.ext
    · funext row
      exact (sourceCanonicalLogBindingResidual_row_zero_iff
        P I Z0 dateOne recurrent tail z h row hp).mpr (hboth.1 row)
    · exact hboth.2

#print axioms sourceCanonicalLogBoundary_eq_zero_iff_original_boundary_zero

/-- At fixed endogenous coordinates, the true SOURCE canonical log
collateral row is independent of reserve-rate rule innovation h,
although other economic equations and the equilibrium z respond. -/
theorem sourceCanonicalLogBindingResidual_row5_policy_invariant
    (P : Primitives S) (I : InheritedState) (Z0 : LocalPrefixCoordinates)
    (dateOne recurrent : S) (tail : LocalPrefixContinuationRule)
    (z : Fin 33 → ℝ) (h h' : ℝ) :
    sourceCanonicalLogBindingResidual P I Z0 dateOne recurrent tail z h (5 : Fin 33) =
      sourceCanonicalLogBindingResidual P I Z0 dateOne recurrent tail z h' (5 : Fin 33) := by
  simp only [sourceCanonicalLogBindingResidual, if_true]
  rw [sourceReserveSlice_pledgeFace_invariant,
    sourceReserveSlice_pledgeFace_invariant]

#print axioms sourceCanonicalLogBindingResidual_row5_policy_invariant

end ProposedLocalScalarAugmented34Source
end Ventura26LiquidityAllocation
