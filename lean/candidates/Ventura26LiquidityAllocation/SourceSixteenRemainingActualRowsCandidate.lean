import Ventura26LiquidityAllocation.SourceFundingDualAffineIncrementCandidate
import Ventura26LiquidityAllocation.SourceAugmented34PermutationRescaleCandidate

/-!
# Literal 16 other SOURCE economic rows of the augmented 34-boundary

We inspect the actual source functions, NOT numerical transcriptions.
The original SOURCE equation partition has 8 heterogeneous firm rows,
9 scalar/normalization rows and 16 additional economic rows. These
16 are capital supply, aggregate resources, Rotemberg NK Phillips,
reserve-rate rule, reserve-quantity rule, loan pricing, deposit pricing,
and bank balance at each of dates zero and one.

For every original 33-log vector z and every reserve-remuneration
innovation h, the genuine 34-output SOURCE residual has precisely
these 16 raw economic functions at the recorded SOURCE indices.
This is OFF ROOT and requires no numerical calibration or finite
differences. The intervened primitives Pv, both date-data objects,
the inherited I and the SOURCE tail rule are literal and explicit.

A separate theorem proves these 16 indices are fixed by the already
certified SOURCE-to-Python row permutation. Row/order agreement is
NOT functional SOURCE/Python equality, nor a verified SOURCE root.
-/

namespace Ventura26LiquidityAllocation

open ProposedLocalScalarAugmented34Source
open ProposedLocalScalarEconomicSlice

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- All 16 original SOURCE identity/other rows, with the same
intervention, inherited state and date-one/date-two transition data
as the original SOURCE augmented boundary. The right side is the
literal 11-row date-data function, not an independently postulated
Python surrogate. -/
theorem source16_actual_remaining_rows
    (P : Primitives S) (I : InheritedState)
    (Z0 : LocalPrefixCoordinates) (dateOne recurrent : S)
    (tail : LocalPrefixContinuationRule)
    (z : Fin 33 → ℝ) (h : ℝ) :
    let Pv := initialIntervenedPrimitives P
      (localScalarParameterIntervention (reserveRemunerationSlice 0 h));
    let Z := localPrefixLogChart Z0 z;
    let d0 := localPrefixDateZeroData Pv I Z dateOne;
    let d1 := localPrefixDateOneData Pv Z dateOne recurrent tail;
    (augmentedBoundaryZeroResidual P I Z0 dateOne recurrent tail z h).1
        (7 : Fin 33) = localReducedRemainingResidual Pv d0 (1 : Fin 11) ∧
          (augmentedBoundaryZeroResidual P I Z0 dateOne recurrent tail z h).1
        (8 : Fin 33) = localReducedRemainingResidual Pv d0 (2 : Fin 11) ∧
          (augmentedBoundaryZeroResidual P I Z0 dateOne recurrent tail z h).1
        (11 : Fin 33) = localReducedRemainingResidual Pv d0 (5 : Fin 11) ∧
          (augmentedBoundaryZeroResidual P I Z0 dateOne recurrent tail z h).1
        (12 : Fin 33) = localReducedRemainingResidual Pv d0 (6 : Fin 11) ∧
          (augmentedBoundaryZeroResidual P I Z0 dateOne recurrent tail z h).1
        (13 : Fin 33) = localReducedRemainingResidual Pv d0 (7 : Fin 11) ∧
          (augmentedBoundaryZeroResidual P I Z0 dateOne recurrent tail z h).1
        (14 : Fin 33) = localReducedRemainingResidual Pv d0 (8 : Fin 11) ∧
          (augmentedBoundaryZeroResidual P I Z0 dateOne recurrent tail z h).1
        (15 : Fin 33) = localReducedRemainingResidual Pv d0 (9 : Fin 11) ∧
          (augmentedBoundaryZeroResidual P I Z0 dateOne recurrent tail z h).1
        (16 : Fin 33) = localReducedRemainingResidual Pv d0 (10 : Fin 11) ∧
          (augmentedBoundaryZeroResidual P I Z0 dateOne recurrent tail z h).1
        (23 : Fin 33) = localReducedRemainingResidual Pv d1 (1 : Fin 11) ∧
          (augmentedBoundaryZeroResidual P I Z0 dateOne recurrent tail z h).1
        (24 : Fin 33) = localReducedRemainingResidual Pv d1 (2 : Fin 11) ∧
          (augmentedBoundaryZeroResidual P I Z0 dateOne recurrent tail z h).1
        (27 : Fin 33) = localReducedRemainingResidual Pv d1 (5 : Fin 11) ∧
          (augmentedBoundaryZeroResidual P I Z0 dateOne recurrent tail z h).1
        (28 : Fin 33) = localReducedRemainingResidual Pv d1 (6 : Fin 11) ∧
          (augmentedBoundaryZeroResidual P I Z0 dateOne recurrent tail z h).1
        (29 : Fin 33) = localReducedRemainingResidual Pv d1 (7 : Fin 11) ∧
          (augmentedBoundaryZeroResidual P I Z0 dateOne recurrent tail z h).1
        (30 : Fin 33) = localReducedRemainingResidual Pv d1 (8 : Fin 11) ∧
          (augmentedBoundaryZeroResidual P I Z0 dateOne recurrent tail z h).1
        (31 : Fin 33) = localReducedRemainingResidual Pv d1 (9 : Fin 11) ∧
          (augmentedBoundaryZeroResidual P I Z0 dateOne recurrent tail z h).1
        (32 : Fin 33) = localReducedRemainingResidual Pv d1 (10 : Fin 11) := by
  dsimp
  repeat' apply And.intro
  all_goals rfl

#print axioms source16_actual_remaining_rows

/-- The unaffected 16 residuals retain their ordinal positions
under the real SOURCE-to-Python row index permutation. -/
theorem source16_remaining_indices_fixed :
    sourceToPython33Index (7 : Fin 33) = 7 ∧
    sourceToPython33Index (8 : Fin 33) = 8 ∧
    sourceToPython33Index (11 : Fin 33) = 11 ∧
    sourceToPython33Index (12 : Fin 33) = 12 ∧
    sourceToPython33Index (13 : Fin 33) = 13 ∧
    sourceToPython33Index (14 : Fin 33) = 14 ∧
    sourceToPython33Index (15 : Fin 33) = 15 ∧
    sourceToPython33Index (16 : Fin 33) = 16 ∧
    sourceToPython33Index (23 : Fin 33) = 23 ∧
    sourceToPython33Index (24 : Fin 33) = 24 ∧
    sourceToPython33Index (27 : Fin 33) = 27 ∧
    sourceToPython33Index (28 : Fin 33) = 28 ∧
    sourceToPython33Index (29 : Fin 33) = 29 ∧
    sourceToPython33Index (30 : Fin 33) = 30 ∧
    sourceToPython33Index (31 : Fin 33) = 31 ∧
    sourceToPython33Index (32 : Fin 33) = 32 := by
  decide

#print axioms source16_remaining_indices_fixed

end Ventura26LiquidityAllocation
