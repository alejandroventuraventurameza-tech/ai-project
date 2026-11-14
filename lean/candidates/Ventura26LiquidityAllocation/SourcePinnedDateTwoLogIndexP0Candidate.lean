import Ventura26LiquidityAllocation.SourceFullyPinnedStationaryP0OperatorCandidate

/-!
# SOURCE t=2 six-state log slice is LITERALLY z[17:23]

The full 33-log chart now has an exact stationary 7+10+6+10
SOURCE reference. The six date-two log-state coordinates are
original indices 17,18,19,20,21,22, not separately postulated z2.

This module proves the ACTUAL source date-two compact-state chart
agrees pointwise with its six-coordinate log representation, and
therefore the original SOURCE date-one nextControls evaluate the
frozen exact-decimal P0 with precisely those six SOURCE log entries.

The result is off root and exact over real arithmetic for EVERY z,h.
It is not a proof that floating-point Python matches those real values,
nor an infinite-horizon optimal continuation, Jacobian enclosure,
or equilibrium IRF.
-/

namespace Ventura26LiquidityAllocation

/-- Exact SOURCE 33-index to 6-index state extraction, matching
the original original-Python `z[17:23]` slice. -/
def fullyPinnedSOURCEDateTwoLog (z : Fin 33 → ℝ) : Fin 6 → ℝ
  | 0 => z 17
  | 1 => z 18
  | 2 => z 19
  | 3 => z 20
  | 4 => z 21
  | 5 => z 22

/-- No unstated source chart identification: the six compact SOURCE
date-two states are exactly the 6-log chart of the stationary source
stateSix, using indices 17-22 from the ORIGINAL 33-log vector. -/
theorem fullyPinnedSOURCE_dateTwoLogChart_exact
    (z : Fin 33 → ℝ) :
    (localPrefixLogChart fullyPinnedStationarySOURCEZ0 z).stateTwo =
      localPrefixStateSixLogChart
        ProposedStationaryRealScale.stateSix
        (fullyPinnedSOURCEDateTwoLog z) := by
  rfl

#print axioms fullyPinnedSOURCE_dateTwoLogChart_exact

/-- On the original SOURCE 33-log chart, the literal date-one
LocalPrefixDateData nextControls use the exact pinned P0 coefficients
and precisely original log coordinates 17-22. The new date-zero
remuneration h changes current policy primitives but not this
fixed-coordinate finite-tail formula. -/
theorem fullyPinnedSOURCE_dateOne_frozenP0_nextControls
    (G : ℝ) (z : Fin 33 → ℝ) (h : ℝ) (j : Fin 10) :
    let Pv := initialIntervenedPrimitives
      (ProposedStationaryPrimitives.primitives G)
      (ProposedLocalScalarEconomicSlice.localScalarParameterIntervention
        (ProposedLocalScalarEconomicSlice.reserveRemunerationSlice 0 h));
    let Z := localPrefixLogChart fullyPinnedStationarySOURCEZ0 z;
    let tail := sourceLogLinearContinuation
      ProposedStationaryRealScale.stateSix
      ProposedStationaryRealScale.controls
      sourceFrozenP0TenControls;
    let d1 := localPrefixDateOneData Pv Z .dateOne .recurrent tail;
    localPrefixControlsTenVector d1.nextControls j =
      localPrefixControlsTenVector ProposedStationaryRealScale.controls j *
        Real.exp (∑ k : Fin 6,
          sourceFrozenP0TenControls j k * fullyPinnedSOURCEDateTwoLog z k) := by
  dsimp
  exact sourceFrozenP0_dateOne_nextControl_level
    (initialIntervenedPrimitives
      (ProposedStationaryPrimitives.primitives G)
      (ProposedLocalScalarEconomicSlice.localScalarParameterIntervention
        (ProposedLocalScalarEconomicSlice.reserveRemunerationSlice 0 h)))
    (localPrefixLogChart fullyPinnedStationarySOURCEZ0 z)
    LocalBridgePhase.dateOne LocalBridgePhase.recurrent
    ProposedStationaryRealScale.stateSix
    ProposedStationaryRealScale.controls
    ProposedStationaryRealScale.stateSix_positive
    (fullyPinnedSOURCEDateTwoLog z)
    (fullyPinnedSOURCE_dateTwoLogChart_exact z) j

#print axioms fullyPinnedSOURCE_dateOne_frozenP0_nextControls

/-- The previous SOURCE/P0 composite theorem is now instantiated at
the REAL stationary primitives, inherited balance, fixed reference
and literal 33-coordinate SOURCE t=2 slice. In particular, eight
date-one SOURCE economic rows use precisely these P0 future controls
for EVERY z,h; there is NO external chart or time-alignment premise. -/
theorem fullyPinnedSOURCE_dateOne_eight_rows_with_P0
    (G : ℝ) (z : Fin 33 → ℝ) (h : ℝ) (j : Fin 10) :
    let P := ProposedStationaryPrimitives.primitives G;
    let I := ProposedStationaryInheritedState.inheritedState G;
    let Z0 := fullyPinnedStationarySOURCEZ0;
    let Pv := initialIntervenedPrimitives P
      (ProposedLocalScalarEconomicSlice.localScalarParameterIntervention
        (ProposedLocalScalarEconomicSlice.reserveRemunerationSlice 0 h));
    let Z := localPrefixLogChart Z0 z;
    let tail := sourceLogLinearContinuation
      ProposedStationaryRealScale.stateSix
      ProposedStationaryRealScale.controls
      sourceFrozenP0TenControls;
    let d1 := localPrefixDateOneData Pv Z .dateOne .recurrent tail;
    ((ProposedLocalScalarAugmented34Source.augmentedBoundaryZeroResidual
        P I Z0 .dateOne .recurrent tail z h).1
        (23 : Fin 33) = localReducedRemainingResidual Pv d1 (1 : Fin 11)) ∧
    ((ProposedLocalScalarAugmented34Source.augmentedBoundaryZeroResidual
        P I Z0 .dateOne .recurrent tail z h).1
        (24 : Fin 33) = localReducedRemainingResidual Pv d1 (2 : Fin 11)) ∧
    ((ProposedLocalScalarAugmented34Source.augmentedBoundaryZeroResidual
        P I Z0 .dateOne .recurrent tail z h).1
        (27 : Fin 33) = localReducedRemainingResidual Pv d1 (5 : Fin 11)) ∧
    ((ProposedLocalScalarAugmented34Source.augmentedBoundaryZeroResidual
        P I Z0 .dateOne .recurrent tail z h).1
        (28 : Fin 33) = localReducedRemainingResidual Pv d1 (6 : Fin 11)) ∧
    ((ProposedLocalScalarAugmented34Source.augmentedBoundaryZeroResidual
        P I Z0 .dateOne .recurrent tail z h).1
        (29 : Fin 33) = localReducedRemainingResidual Pv d1 (7 : Fin 11)) ∧
    ((ProposedLocalScalarAugmented34Source.augmentedBoundaryZeroResidual
        P I Z0 .dateOne .recurrent tail z h).1
        (30 : Fin 33) = localReducedRemainingResidual Pv d1 (8 : Fin 11)) ∧
    ((ProposedLocalScalarAugmented34Source.augmentedBoundaryZeroResidual
        P I Z0 .dateOne .recurrent tail z h).1
        (31 : Fin 33) = localReducedRemainingResidual Pv d1 (9 : Fin 11)) ∧
    ((ProposedLocalScalarAugmented34Source.augmentedBoundaryZeroResidual
        P I Z0 .dateOne .recurrent tail z h).1
        (32 : Fin 33) = localReducedRemainingResidual Pv d1 (10 : Fin 11)) ∧
    (localPrefixControlsTenVector d1.nextControls j =
      localPrefixControlsTenVector ProposedStationaryRealScale.controls j *
        Real.exp (∑ k : Fin 6,
          sourceFrozenP0TenControls j k * fullyPinnedSOURCEDateTwoLog z k)) := by
  dsimp
  exact source16_dateOne_actual_rows_with_exact_frozenP0
    (ProposedStationaryPrimitives.primitives G)
    (ProposedStationaryInheritedState.inheritedState G)
    fullyPinnedStationarySOURCEZ0
    LocalBridgePhase.dateOne LocalBridgePhase.recurrent
    ProposedStationaryRealScale.stateSix
    ProposedStationaryRealScale.controls
    ProposedStationaryRealScale.stateSix_positive
    z (fullyPinnedSOURCEDateTwoLog z) h
    (fullyPinnedSOURCE_dateTwoLogChart_exact z) j

#print axioms fullyPinnedSOURCE_dateOne_eight_rows_with_P0

end Ventura26LiquidityAllocation
