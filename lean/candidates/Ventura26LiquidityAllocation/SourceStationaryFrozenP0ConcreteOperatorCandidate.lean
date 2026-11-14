import Ventura26LiquidityAllocation.SourceSixteenRowsFrozenP0CompositeCandidate
import Ventura26LiquidityAllocation.StationaryInterventionSourceBridgeCandidate
import Ventura26LiquidityAllocation.SourceReduced33FixedPolicyFiberCandidate

/-!
# Concrete SOURCE reduced operator with frozen stationary predecessor and P0

The earlier SOURCE 34->33 proof allowed arbitrary Primitives,
InheritedState and tail. This module fixes ACTUAL stationary Lean
Primitives and inherited nominal faces from the separately proven
stationary source construction, fixes dateOne/recurrent on the
concrete three-phase tree, and fixes the exact real-decimal 10x6
finite P0 control continuation. It leaves only the date-zero/date-one
prefix chart Z0, the six baseline date-two states and ten baseline
controls explicit rather than silently importing an unmatched Python
boundary or stationary seed.

For this concrete finite SOURCE object we prove (1) exact 34<->33
root equivalence under stated positive-prefix conditions; (2) the
literal date-zero single-instrument policy field contract; and
(3) date-one data are policy-invariant at FIXED economic coordinates.

No numerical root, Python function identity, closed Jacobian enclosure,
branch-specific IRF, or infinite-horizon equilibrium is claimed.
-/

namespace Ventura26LiquidityAllocation

open ProposedLocalScalarAugmented34Source
open ProposedLocalScalarEconomicSlice
open ProposedStationaryPrimitives
open ProposedStationaryInheritedState
open ProposedStationaryInterventionSourceBridge

/-- The original 34-output SOURCE augmented boundary evaluated with
the explicit stationary SOURCE primitives, inherited financial state,
real-decimal frozen 10x6 P0, and concrete date-one/recurrent states. -/
noncomputable def concreteStationaryP0SOURCE34
    (G : ℝ) (Z0 : LocalPrefixCoordinates)
    (x0 : LocalPrefixStateSix) (u0 : LocalPrefixControlsTen)
    (z : Fin 33 → ℝ) (h : ℝ) :
    (Fin 33 → ℝ) × ℝ :=
  augmentedBoundaryZeroResidual
    (ProposedStationaryPrimitives.primitives G)
    (ProposedStationaryInheritedState.inheritedState G)
    Z0 .dateOne .recurrent
    (sourceLogLinearContinuation x0 u0 sourceFrozenP0TenControls)
    z h

/-- The SAME concrete SOURCE numerical target with the analytic
L funding-dual elimination, hence 32 free SOURCE logs plus h. -/
noncomputable def concreteStationaryP0SOURCE33
    (G : ℝ) (Z0 : LocalPrefixCoordinates)
    (x0 : LocalPrefixStateSix) (u0 : LocalPrefixControlsTen)
    (w : (Fin 32 → ℝ) × ℝ) : Fin 33 → ℝ :=
  sourceReduced33EconomicMap
    (ProposedStationaryPrimitives.primitives G)
    (ProposedStationaryInheritedState.inheritedState G)
    Z0 .dateOne .recurrent
    (sourceLogLinearContinuation x0 u0 sourceFrozenP0TenControls)
    w

/-- The concrete stationary primitives establish sigmaE=1 and
betaE>0 exactly. No Python float64 equality is inferred. -/
theorem concreteStationaryP0_euler_parameters (G : ℝ) :
    (ProposedStationaryPrimitives.primitives G).entrepreneurRiskAversion = 1 ∧
    0 < (ProposedStationaryPrimitives.primitives G).entrepreneurDiscount := by
  constructor
  · rfl
  · change (0 : ℝ) < 24 / 25
    norm_num

#print axioms concreteStationaryP0_euler_parameters

/-- A concrete stationary-inheritance/frozen-P0 34-output root exists
iff its genuine reduced SOURCE 33-output root exists. This is a
logical equivalence, not a proof that either root exists. -/
theorem concreteStationaryP0SOURCE_root_exists_iff
    (G : ℝ) (Z0 : LocalPrefixCoordinates)
    (x0 : LocalPrefixStateSix) (u0 : LocalPrefixControlsTen)
    (hc_same : Z0.controlsZero.consumptionL = Z0.controlsOne.consumptionL)
    (hc_positive : 0 < Z0.controlsZero.consumptionL)
    (hpi : Z0.controlsOne.inflation = 1)
    (hr : 0 < Z0.controlsZero.loanRate) :
    (∃ z : Fin 33 → ℝ, ∃ h : ℝ,
      concreteStationaryP0SOURCE34 G Z0 x0 u0 z h = (0, 0)) ↔
    (∃ w : (Fin 32 → ℝ) × ℝ,
      concreteStationaryP0SOURCE33 G Z0 x0 u0 w = 0) := by
  change
    (∃ z : Fin 33 → ℝ, ∃ h : ℝ,
      augmentedBoundaryZeroResidual
        (ProposedStationaryPrimitives.primitives G)
        (ProposedStationaryInheritedState.inheritedState G)
        Z0 .dateOne .recurrent
        (sourceLogLinearContinuation x0 u0 sourceFrozenP0TenControls)
        z h = (0, 0)) ↔
    (∃ w : (Fin 32 → ℝ) × ℝ,
      sourceReduced33EconomicMap
        (ProposedStationaryPrimitives.primitives G)
        (ProposedStationaryInheritedState.inheritedState G)
        Z0 .dateOne .recurrent
        (sourceLogLinearContinuation x0 u0 sourceFrozenP0TenControls)
        w = 0)
  exact source34_root_exists_iff_sourceReduced33EconomicMap_zero
    (ProposedStationaryPrimitives.primitives G)
    (ProposedStationaryInheritedState.inheritedState G)
    Z0 .dateOne .recurrent
    (sourceLogLinearContinuation x0 u0 sourceFrozenP0TenControls)
    (concreteStationaryP0_euler_parameters G).1
    hc_same hc_positive hpi hr
    (concreteStationaryP0_euler_parameters G).2

#print axioms concreteStationaryP0SOURCE_root_exists_iff

/-- At fixed economic prefix coordinates, the literal SOURCE
date-one data are unchanged by a DATE-ZERO remuneration announcement,
even after instantiating the frozen P0 continuation. The resulting
endogenous equilibrium date-one response need NOT be zero. -/
theorem concreteStationaryP0_dateOne_data_invariant
    (G : ℝ) (Z0 : LocalPrefixCoordinates)
    (x0 : LocalPrefixStateSix) (u0 : LocalPrefixControlsTen)
    (z : Fin 33 → ℝ) (h : ℝ) :
    localPrefixDateOneData
      (initialIntervenedPrimitives
        (ProposedStationaryPrimitives.primitives G)
        (localScalarParameterIntervention (reserveRemunerationSlice 0 h)))
      (localPrefixLogChart Z0 z)
      .dateOne .recurrent
      (sourceLogLinearContinuation x0 u0 sourceFrozenP0TenControls) =
    localPrefixDateOneData
      (ProposedStationaryPrimitives.primitives G)
      (localPrefixLogChart Z0 z)
      .dateOne .recurrent
      (sourceLogLinearContinuation x0 u0 sourceFrozenP0TenControls) := by
  exact source_stationary_dateone_data_invariant_fixed_coordinates
    G (localScalarParameterIntervention (reserveRemunerationSlice 0 h))
    (localPrefixLogChart Z0 z)
    (sourceLogLinearContinuation x0 u0 sourceFrozenP0TenControls)

#print axioms concreteStationaryP0_dateOne_data_invariant

/-- The concrete date-zero source record sees ONLY the date-zero
reserve remuneration innovation h, with quantity/requirement/corridor
held at exact illustrative stationary levels. -/
theorem concreteStationaryP0_dateZero_policy_fields
    (G : ℝ) (Z0 : LocalPrefixCoordinates)
    (z : Fin 33 → ℝ) (h : ℝ) :
    let v := localScalarParameterIntervention (reserveRemunerationSlice 0 h)
    let d0 := sourceStationaryDateZeroData G v (localPrefixLogChart Z0 z)
    d0.reserveRateInnovation = h ∧
    d0.reserveQuantityInnovation = 0 ∧
    d0.reserveRequirement = (1 / 10 : ℝ) ∧
    d0.corridorWidth = (1 / 50 : ℝ) := by
  have hd := source_stationary_datezero_four_policy_fields
    G (localScalarParameterIntervention (reserveRemunerationSlice 0 h))
    (localPrefixLogChart Z0 z)
  have hp := augmentedBoundaryZeroResidual_policy_contract h
  rcases hd with ⟨hR, hM, hrho, hcorr⟩
  rcases hp with ⟨hvR, hvM, hvRho, hvCorr⟩
  dsimp
  constructor
  · exact hR.trans hvR
  constructor
  · exact hM.trans hvM
  constructor
  · rw [hrho, hvRho]
    ring
  · rw [hcorr, hvCorr]
    ring

#print axioms concreteStationaryP0_dateZero_policy_fields

end Ventura26LiquidityAllocation
