import Ventura26LiquidityAllocation.SourceSixteenRemainingActualRowsCandidate
import Ventura26LiquidityAllocation.SourceFrozenP0LiteralDateCalendarCandidate

/-!
# Eight actual SOURCE date-one rows with literal frozen P0 next controls

The true SOURCE 34-output boundary residual uses 8 economic
non-firm rows at date one. This theorem INSTANTIATES the previously
audited original SOURCE 16-row theorem with the exactly pinned real
decimal 10x6 P0 continuation and proves that the date-one LocalPrefixDateData
used in those 8 ORIGINAL economic equations contains next-period
controls equal to the intended P0 exponential formula.

No Python binary64 calculation, economic operator parity, interval
Jacobian box, full dynamic equilibrium or root-existence claim follows.
-/

namespace Ventura26LiquidityAllocation

open ProposedLocalScalarAugmented34Source
open ProposedLocalScalarEconomicSlice

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- At all positive date-two SOURCE log-chart points and at arbitrary
reserve-remuneration innovations h, the eight actual date-one economic
rows are evaluated with the identical data record whose ten next
controls are P0. This is OFF ROOT and uses no numerical Newton solver. -/
theorem source16_dateOne_actual_rows_with_exact_frozenP0
    (P : Primitives S) (I : InheritedState)
    (Z0 : LocalPrefixCoordinates) (dateOne recurrent : S)
    (x0 : LocalPrefixStateSix) (u0 : LocalPrefixControlsTen)
    (hx0 : LocalPrefixStateSixPositive x0)
    (z : Fin 33 → ℝ) (z2 : Fin 6 → ℝ) (h : ℝ)
    (hstate :
      (localPrefixLogChart Z0 z).stateTwo =
        localPrefixStateSixLogChart x0 z2)
    (j : Fin 10) :
    let Pv := initialIntervenedPrimitives P
      (localScalarParameterIntervention (reserveRemunerationSlice 0 h));
    let Z := localPrefixLogChart Z0 z;
    let tail := sourceLogLinearContinuation x0 u0 sourceFrozenP0TenControls;
    let d1 := localPrefixDateOneData Pv Z dateOne recurrent tail;
    ((augmentedBoundaryZeroResidual P I Z0 dateOne recurrent tail z h).1
      (23 : Fin 33) = localReducedRemainingResidual Pv d1 (1 : Fin 11)) ∧
    ((augmentedBoundaryZeroResidual P I Z0 dateOne recurrent tail z h).1
      (24 : Fin 33) = localReducedRemainingResidual Pv d1 (2 : Fin 11)) ∧
    ((augmentedBoundaryZeroResidual P I Z0 dateOne recurrent tail z h).1
      (27 : Fin 33) = localReducedRemainingResidual Pv d1 (5 : Fin 11)) ∧
    ((augmentedBoundaryZeroResidual P I Z0 dateOne recurrent tail z h).1
      (28 : Fin 33) = localReducedRemainingResidual Pv d1 (6 : Fin 11)) ∧
    ((augmentedBoundaryZeroResidual P I Z0 dateOne recurrent tail z h).1
      (29 : Fin 33) = localReducedRemainingResidual Pv d1 (7 : Fin 11)) ∧
    ((augmentedBoundaryZeroResidual P I Z0 dateOne recurrent tail z h).1
      (30 : Fin 33) = localReducedRemainingResidual Pv d1 (8 : Fin 11)) ∧
    ((augmentedBoundaryZeroResidual P I Z0 dateOne recurrent tail z h).1
      (31 : Fin 33) = localReducedRemainingResidual Pv d1 (9 : Fin 11)) ∧
    ((augmentedBoundaryZeroResidual P I Z0 dateOne recurrent tail z h).1
      (32 : Fin 33) = localReducedRemainingResidual Pv d1 (10 : Fin 11)) ∧
    (localPrefixControlsTenVector d1.nextControls j =
      localPrefixControlsTenVector u0 j *
        Real.exp (∑ k : Fin 6, sourceFrozenP0TenControls j k * z2 k)) := by
  dsimp
  have hrows := source16_actual_remaining_rows
    P I Z0 dateOne recurrent
      (sourceLogLinearContinuation x0 u0 sourceFrozenP0TenControls)
      z h
  dsimp at hrows
  rcases hrows with
    ⟨_, _, _, _, _, _, _, _, h23, h24, h27, h28, h29, h30, h31, h32⟩
  have hnext := sourceFrozenP0_dateOne_nextControl_level
    (initialIntervenedPrimitives P
      (localScalarParameterIntervention (reserveRemunerationSlice 0 h)))
    (localPrefixLogChart Z0 z) dateOne recurrent x0 u0 hx0 z2 hstate j
  exact ⟨h23, h24, h27, h28, h29, h30, h31, h32, hnext⟩

#print axioms source16_dateOne_actual_rows_with_exact_frozenP0

end Ventura26LiquidityAllocation
