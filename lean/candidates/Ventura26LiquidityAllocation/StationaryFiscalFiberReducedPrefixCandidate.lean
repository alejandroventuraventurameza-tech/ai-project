import Ventura26LiquidityAllocation.ReducedPrefixInheritedExtCandidate
import Ventura26LiquidityAllocation.StationaryInheritedStateCandidate

/-!
# Fiscal fiber in the actual stationary SOURCE inherited record

The record ProposedStationaryInheritedState.inheritedState G changes inherited
household bonds with G, but keeps five fields read by the 33-row reduced prefix
fixed. All propositions below hold for a COMMON Primitives P, a common chart
and a common continuation; they do NOT compare primitives G versus primitives G'.
-/

namespace Ventura26LiquidityAllocation

theorem stationaryInherited_five_fields_independent_of_G (G H : ℝ) :
    (ProposedStationaryInheritedState.inheritedState G).capital =
      (ProposedStationaryInheritedState.inheritedState H).capital ∧
    (ProposedStationaryInheritedState.inheritedState G).firmFace =
      (ProposedStationaryInheritedState.inheritedState H).firmFace ∧
    (ProposedStationaryInheritedState.inheritedState G).bankFace =
      (ProposedStationaryInheritedState.inheritedState H).bankFace ∧
    (ProposedStationaryInheritedState.inheritedState G).reserveRateLag =
      (ProposedStationaryInheritedState.inheritedState H).reserveRateLag ∧
    (ProposedStationaryInheritedState.inheritedState G).reservesPreLag =
      (ProposedStationaryInheritedState.inheritedState H).reservesPreLag := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

#print axioms stationaryInherited_five_fields_independent_of_G

/-- Unlike the reduced inherited coordinates, household bond stocks do change
with the fiscal debt parameter.  This is exactly the omitted financial fiber. -/
theorem stationaryInherited_householdBonds_difference (G H : ℝ) :
    (ProposedStationaryInheritedState.inheritedState G).householdBonds -
      (ProposedStationaryInheritedState.inheritedState H).householdBonds =
    G - H := by
  change G - ProposedStationaryInheritedState.reservesPre -
      (H - ProposedStationaryInheritedState.reservesPre) = G - H
  ring

#print axioms stationaryInherited_householdBonds_difference



theorem stationaryInherited_fiscalFiber_logResidual_eq
    (P : Primitives LocalBridgePhase)
    (G H : ℝ) (branch : LocalPrefixBranch)
    (Z0 : LocalPrefixCoordinates)
    (tail : LocalPrefixContinuationRule) :
    localReducedPrefixLogResidualVector branch P
        (ProposedStationaryInheritedState.inheritedState G)
        Z0 .dateOne .recurrent tail =
      localReducedPrefixLogResidualVector branch P
        (ProposedStationaryInheritedState.inheritedState H)
        Z0 .dateOne .recurrent tail := by
  obtain ⟨hcapital, hface, hbank, hrate, hreserves⟩ :=
    stationaryInherited_five_fields_independent_of_G G H
  exact localReducedPrefixLogResidualVector_inherited_extensionality
    branch P
    (ProposedStationaryInheritedState.inheritedState G)
    (ProposedStationaryInheritedState.inheritedState H)
    Z0 .dateOne .recurrent tail hcapital hface hbank hrate hreserves

#print axioms stationaryInherited_fiscalFiber_logResidual_eq

theorem stationaryInherited_fiscalFiber_certificate_iff
    (P : Primitives LocalBridgePhase)
    (G H : ℝ) (branch : LocalPrefixBranch)
    (Z0 : LocalPrefixCoordinates)
    (tail : LocalPrefixContinuationRule) (inverseNormBound : ℝ) :
    LocalReducedPrefixLogJacobianCertifiedAt branch P
        (ProposedStationaryInheritedState.inheritedState G)
        Z0 .dateOne .recurrent tail inverseNormBound ↔
      LocalReducedPrefixLogJacobianCertifiedAt branch P
        (ProposedStationaryInheritedState.inheritedState H)
        Z0 .dateOne .recurrent tail inverseNormBound := by
  obtain ⟨hcapital, hface, hbank, hrate, hreserves⟩ :=
    stationaryInherited_five_fields_independent_of_G G H
  exact localReducedPrefixLogJacobianCertifiedAt_inherited_iff
    branch P
    (ProposedStationaryInheritedState.inheritedState G)
    (ProposedStationaryInheritedState.inheritedState H)
    Z0 .dateOne .recurrent tail inverseNormBound
    hcapital hface hbank hrate hreserves

#print axioms stationaryInherited_fiscalFiber_certificate_iff

end Ventura26LiquidityAllocation
