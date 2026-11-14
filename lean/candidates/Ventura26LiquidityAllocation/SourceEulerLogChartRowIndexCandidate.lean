import Ventura26LiquidityAllocation.SourceEulerLogChartDirectionalBridgeCandidate

/-!
# Exact enumeration bridge from genuine SOURCE 33-row labels to Fin 33

The SOURCE log-chart paper uses Fin 33, whereas its economic operator
uses LocalPrefixEquation. We prove the actual source-defined enumeration
is bijective and lift the 33-label zero-set equivalence to the EXACT
indexed SOURCE log residual system. These are combinatorial and
economic zero-set facts, not Jacobian-inverse certificates.
-/

namespace Ventura26LiquidityAllocation

/-- The actual SOURCE row enumeration is a bijection: all 33 positions
are used and there are no repeated economic equation labels. -/
theorem sourceLogRowIndex_bijective :
    Function.Bijective localPrefixEquationOfIndex := by
  decide

#print axioms sourceLogRowIndex_bijective

/-- Exact equivalence of all 33 indexed log residual zeros before and
after the genuine SOURCE economic Euler shears. This uses the actual
Fin 33 indexing in the manuscript, not an unlabelled surrogate. -/
theorem sourceShearedLogResidual_all_zero_iff
    (branch : LocalPrefixBranch)
    (P : Primitives LocalBridgePhase) (I : InheritedState)
    (Z0 : LocalPrefixCoordinates)
    (dateOne recurrent : LocalBridgePhase)
    (tail : LocalPrefixContinuationRule)
    (z : Fin 33 → ℝ) :
    (∀ row : Fin 33,
      sourceNominalPledgeShearedLogResidualVector branch P I Z0
        dateOne recurrent tail z row = 0) ↔
    (∀ row : Fin 33,
      localReducedPrefixLogResidualVector branch P I Z0
        dateOne recurrent tail z row = 0) := by
  have hb := sourceNominalPledgeShearedResidual_all_zero_iff
    branch P I (localPrefixLogChart Z0 z) dateOne recurrent tail
  constructor
  · intro h row
    have hall : ∀ eqn : LocalPrefixEquation,
        sourceNominalPledgeShearedResidual branch P I
          (localPrefixLogChart Z0 z) dateOne recurrent tail eqn = 0 := by
      intro eqn
      obtain ⟨j, hj⟩ := sourceLogRowIndex_bijective.2 eqn
      rw [← hj]
      exact h j
    exact (hb.mp hall) (localPrefixEquationOfIndex row)
  · intro h row
    have hall : ∀ eqn : LocalPrefixEquation,
        localReducedPrefixResidual branch P I
          (localPrefixLogChart Z0 z) dateOne recurrent tail eqn = 0 := by
      intro eqn
      obtain ⟨j, hj⟩ := sourceLogRowIndex_bijective.2 eqn
      rw [← hj]
      exact h j
    exact (hb.mpr hall) (localPrefixEquationOfIndex row)

#print axioms sourceShearedLogResidual_all_zero_iff

end Ventura26LiquidityAllocation
