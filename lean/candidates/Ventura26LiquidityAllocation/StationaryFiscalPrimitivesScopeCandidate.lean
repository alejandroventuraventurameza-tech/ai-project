import Ventura26LiquidityAllocation.StationaryFiscalFiberReducedPrefixCandidate

/-!
# Restricted fiscal primitive support of the genuine SOURCE 33-row reduction

The stationary Primitives(G) record changes governmentBondSupply with G.
The following propositions are candidate *definitional* equalities and
must pass the pinned Lean kernel. No full equilibrium neutrality follows.
-/

namespace Ventura26LiquidityAllocation

open ProposedStationaryPrimitives
open ProposedStationaryInheritedState

/-- The concrete stationary primitives differ in the government-bond-supply
field, with every other primitive fixed definitionally. -/
theorem stationaryPrimitives_only_bond_supply_changes (G H : ℝ) :
    primitives G = { primitives H with governmentBondSupply := G } := by
  rfl

#print axioms stationaryPrimitives_only_bond_supply_changes

/-- The two local date-data constructions do not read bond supply when the
same SOURCE coordinates and continuation are held fixed. -/
theorem stationaryFiscal_dateZeroData_eq
    (G H : ℝ) (Z : LocalPrefixCoordinates) :
    localPrefixDateZeroData (primitives G) (inheritedState G)
      Z .dateOne =
    localPrefixDateZeroData (primitives H) (inheritedState H)
      Z .dateOne := by
  rfl

#print axioms stationaryFiscal_dateZeroData_eq

theorem stationaryFiscal_dateOneData_eq
    (G H : ℝ) (Z : LocalPrefixCoordinates)
    (tail : LocalPrefixContinuationRule) :
    localPrefixDateOneData (primitives G) Z .dateOne .recurrent tail =
    localPrefixDateOneData (primitives H) Z .dateOne .recurrent tail := by
  rfl

#print axioms stationaryFiscal_dateOneData_eq

/-- Economic 33-row reduction under two ACTUAL primitive instances P(G) and P(H).
Both inherited records vary as prescribed. Definitional equality is audited
against SOURCE, not assumed as a new axiom. -/
theorem stationaryFiscal_reducedResidual_row_eq
    (G H : ℝ) (branch : LocalPrefixBranch)
    (Z : LocalPrefixCoordinates)
    (tail : LocalPrefixContinuationRule)
    (eqn : LocalPrefixEquation) :
    localReducedPrefixResidual branch (primitives G) (inheritedState G)
        Z .dateOne .recurrent tail eqn =
      localReducedPrefixResidual branch (primitives H) (inheritedState H)
        Z .dateOne .recurrent tail eqn := by
  cases eqn <;> rfl

#print axioms stationaryFiscal_reducedResidual_row_eq

/-- The resulting full 33-row log operator, with a common positive baseline
chart and common terminal continuation, is independent of stationary G. -/
theorem stationaryFiscal_reducedLogOperator_eq
    (G H : ℝ) (branch : LocalPrefixBranch)
    (Z0 : LocalPrefixCoordinates)
    (tail : LocalPrefixContinuationRule) :
    localReducedPrefixLogResidualVector branch (primitives G) (inheritedState G)
        Z0 .dateOne .recurrent tail =
      localReducedPrefixLogResidualVector branch (primitives H) (inheritedState H)
        Z0 .dateOne .recurrent tail := by
  funext z row
  exact stationaryFiscal_reducedResidual_row_eq G H branch
    (localPrefixLogChart Z0 z) tail (localPrefixEquationOfIndex row)

#print axioms stationaryFiscal_reducedLogOperator_eq


end Ventura26LiquidityAllocation
