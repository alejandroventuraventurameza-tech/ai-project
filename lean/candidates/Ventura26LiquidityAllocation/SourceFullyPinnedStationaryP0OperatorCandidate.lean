import Ventura26LiquidityAllocation.SourceStationaryFrozenP0ConcreteOperatorCandidate

/-!
# A FULLY specified Lean SOURCE finite-prefix reference, except bond supply G

Earlier SOURCE 34->33 root proofs allowed an arbitrary 33-component
reference Z0, even after fixing the stationary primitives, inherited
state, and frozen P0 continuation. Here Z0 is assembled from exactly
the proved SOURCE stationary capital, nominal firm faces, bank face,
reserve lags, ten controls, and compact six-state reference.

This source object has NO caller-selected basepoint/initial controls,
Primitives, inherited state, calendar or finite P0 tail. Only the
government bond-supply parameter G remains free, exactly as in the
stationary Primitives construction, and endogenous log deviations
and h remain unknown.

The resulting original SOURCE log chart is positive in all 33 entries.
We establish exact 34->33 root-set equivalence but DO NOT construct
a root, identify Python binary64's frozen_stationary_seed with the
Lean reference, certify Jacobian enclosures, or prove that the finite
P0 tail is an infinite-horizon equilibrium.
-/

namespace Ventura26LiquidityAllocation

open ProposedStationaryRealScale

/-- Literal stationary finite-prefix reference in all 7+10+6+10
original SOURCE coordinates. At fixed baseline it has identical
date-zero/date-one controls and the original stationary date-two state. -/
noncomputable def fullyPinnedStationarySOURCEZ0 :
    LocalPrefixCoordinates where
  stateOne := {
    capitalH := ProposedStationaryRealScale.capital .H
    capitalL := ProposedStationaryRealScale.capital .L
    firmFaceH := ProposedStationaryRealScale.firmFace .H
    firmFaceL := ProposedStationaryRealScale.firmFace .L
    bankFace := ProposedStationaryRealScale.bankEquity
    reserveRateLag := ProposedStationaryBank.reserveRate
    reservesPreLag := ProposedStationaryRealScale.reservesPre }
  controlsZero := ProposedStationaryRealScale.controls
  stateTwo := ProposedStationaryRealScale.stateSix
  controlsOne := ProposedStationaryRealScale.controls

/-- All 33 SOURCE log-reference levels are strictly positive.
The chart positivity is not borrowed from Python. -/
theorem fullyPinnedStationarySOURCEZ0_positive :
    LocalPrefixCoordinatesPositive fullyPinnedStationarySOURCEZ0 := by
  intro j
  fin_cases j <;> first
    | exact ProposedStationaryRealScale.capital_pos .H
    | exact ProposedStationaryRealScale.capital_pos .L
    | exact ProposedStationaryRealScale.firmFace_pos .H
    | exact ProposedStationaryRealScale.firmFace_pos .L
    | exact ProposedStationaryRealScale.bank_scale_pos.1
    | exact ProposedStationaryBank.reserveRate_spec.1
    | exact ProposedStationaryRealScale.bank_scale_pos.2.2
    | exact ProposedStationaryRealScale.controls_positive (0 : Fin 10)
    | exact ProposedStationaryRealScale.controls_positive (1 : Fin 10)
    | exact ProposedStationaryRealScale.controls_positive (2 : Fin 10)
    | exact ProposedStationaryRealScale.controls_positive (3 : Fin 10)
    | exact ProposedStationaryRealScale.controls_positive (4 : Fin 10)
    | exact ProposedStationaryRealScale.controls_positive (5 : Fin 10)
    | exact ProposedStationaryRealScale.controls_positive (6 : Fin 10)
    | exact ProposedStationaryRealScale.controls_positive (7 : Fin 10)
    | exact ProposedStationaryRealScale.controls_positive (8 : Fin 10)
    | exact ProposedStationaryRealScale.controls_positive (9 : Fin 10)
    | exact ProposedStationaryRealScale.stateSix_positive (0 : Fin 6)
    | exact ProposedStationaryRealScale.stateSix_positive (1 : Fin 6)
    | exact ProposedStationaryRealScale.stateSix_positive (2 : Fin 6)
    | exact ProposedStationaryRealScale.stateSix_positive (3 : Fin 6)
    | exact ProposedStationaryRealScale.stateSix_positive (4 : Fin 6)
    | exact ProposedStationaryRealScale.stateSix_positive (5 : Fin 6)

#print axioms fullyPinnedStationarySOURCEZ0_positive

/-- The original SOURCE augmented 34-output model is now specialized
to the EXACT stationary 33-coordinate reference, stationary inherited
financial state, and real-decimal frozen P0 finite continuation. -/
noncomputable def fullyPinnedStationaryP0SOURCE34
    (G : ℝ) (z : Fin 33 → ℝ) (h : ℝ) :
    (Fin 33 → ℝ) × ℝ :=
  concreteStationaryP0SOURCE34 G fullyPinnedStationarySOURCEZ0
    ProposedStationaryRealScale.stateSix
    ProposedStationaryRealScale.controls z h

/-- Same ACTUAL SOURCE operator reduced by the exact analytic L
funding-dual elimination: 33 economic rows, 32 free logs plus h. -/
noncomputable def fullyPinnedStationaryP0SOURCE33
    (G : ℝ) (w : (Fin 32 → ℝ) × ℝ) : Fin 33 → ℝ :=
  concreteStationaryP0SOURCE33 G fullyPinnedStationarySOURCEZ0
    ProposedStationaryRealScale.stateSix
    ProposedStationaryRealScale.controls w

/-- The fully pinned real SOURCE 34 and reduced 33 root sets are
equivalent, without any free baseline/continuation assumptions. -/
theorem fullyPinnedStationaryP0SOURCE_root_exists_iff (G : ℝ) :
    (∃ z : Fin 33 → ℝ, ∃ h : ℝ,
      fullyPinnedStationaryP0SOURCE34 G z h = (0, 0)) ↔
    (∃ w : (Fin 32 → ℝ) × ℝ,
      fullyPinnedStationaryP0SOURCE33 G w = 0) := by
  change
    (∃ z : Fin 33 → ℝ, ∃ h : ℝ,
      concreteStationaryP0SOURCE34 G fullyPinnedStationarySOURCEZ0
        ProposedStationaryRealScale.stateSix
        ProposedStationaryRealScale.controls z h = (0, 0)) ↔
    (∃ w : (Fin 32 → ℝ) × ℝ,
      concreteStationaryP0SOURCE33 G fullyPinnedStationarySOURCEZ0
        ProposedStationaryRealScale.stateSix
        ProposedStationaryRealScale.controls w = 0)
  exact concreteStationaryP0SOURCE_root_exists_iff G
    fullyPinnedStationarySOURCEZ0
    ProposedStationaryRealScale.stateSix
    ProposedStationaryRealScale.controls
    rfl
    (ProposedStationaryRealScale.firmConsumption_pos .L)
    rfl ProposedStationaryRealScale.loanRate_pos

#print axioms fullyPinnedStationaryP0SOURCE_root_exists_iff

/-- The fixed real SOURCE P0 tail returns all ten baseline controls
at exactly the stationary six-state reference. -/
theorem fullyPinnedStationaryP0_tail_baseline :
    sourceLogLinearContinuation
      ProposedStationaryRealScale.stateSix
      ProposedStationaryRealScale.controls
      sourceFrozenP0TenControls
      ProposedStationaryRealScale.stateSix =
    ProposedStationaryRealScale.controls :=
  sourceLogLinearContinuation_at_baseline
    ProposedStationaryRealScale.stateSix
    ProposedStationaryRealScale.controls
    sourceFrozenP0TenControls
    ProposedStationaryRealScale.stateSix_positive

#print axioms fullyPinnedStationaryP0_tail_baseline

end Ventura26LiquidityAllocation
