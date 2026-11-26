import Ventura26LiquidityAllocation.SourceFullyPinnedStationaryP0OperatorCandidate

/-!
# Parity between the actual SOURCE two-date finite prefix and the
# already kernel-proven stationary economic date-data witness.

Proves only identities of SOURCE date data at the original positive
33-coordinate logarithmic origin. The incumbent stationary reduced
one-date system is NOT silently promoted to a two-date/root theorem.
-/

namespace Ventura26LiquidityAllocation
namespace CurrentPinnedDateParity

/-- The exact SOURCE 33-vector logarithmic origin maps back to its
own pinned stationary basepoint, not a Python float64 reference. -/
theorem sourcePinnedLogChart_zero :
    localPrefixLogChart fullyPinnedStationarySOURCEZ0
      (0 : Fin 33 → ℝ) = fullyPinnedStationarySOURCEZ0 := by
  simp [localPrefixLogChart,
    localPrefixCoordinatesOfVector, localPrefixCoordinatesVector]

#print axioms sourcePinnedLogChart_zero

/-- Date-zero SOURCE data agree with the existing stationary economic
witness when evaluated on the ORIGINAL pinned baseline. -/
theorem sourcePinnedDateZero_eq_stationary (G : ℝ) :
    localPrefixDateZeroData
      (ProposedStationaryPrimitives.primitives G)
      (ProposedStationaryInheritedState.inheritedState G)
      fullyPinnedStationarySOURCEZ0 .dateOne =
    ProposedStationaryRealScale.dateData := by
  rfl

#print axioms sourcePinnedDateZero_eq_stationary

/-- Date-one SOURCE data use the common pledge value and the same
fixed P0 continuation at the stationary reference. -/
theorem sourcePinnedDateOne_eq_stationary (G : ℝ) :
    localPrefixDateOneData
      (ProposedStationaryPrimitives.primitives G)
      fullyPinnedStationarySOURCEZ0 .dateOne .recurrent
      (sourceLogLinearContinuation
        ProposedStationaryRealScale.stateSix
        ProposedStationaryRealScale.controls
        sourceFrozenP0TenControls) =
    ProposedStationaryRealScale.dateData := by
  have hfaces :
      localPrefixStateSixFace
        (ProposedStationaryPrimitives.primitives G)
        ProposedStationaryRealScale.stateSix =
      ProposedStationaryRealScale.firmFace :=
    ProposedStationaryRealScale.stateSix_faces
      (ProposedStationaryPrimitives.primitives G) (by intro i; rfl)
  have htail := fullyPinnedStationaryP0_tail_baseline
  ext <;> first
    | rfl
    | simp [localPrefixDateOneData,
        fullyPinnedStationarySOURCEZ0,
        ProposedStationaryPrimitives.primitives,
        ProposedStationaryRealScale.dateData,
        hfaces, htail]

#print axioms sourcePinnedDateOne_eq_stationary

end CurrentPinnedDateParity
end Ventura26LiquidityAllocation
