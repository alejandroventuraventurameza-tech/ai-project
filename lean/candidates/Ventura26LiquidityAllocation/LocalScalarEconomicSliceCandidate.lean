import Ventura26LiquidityAllocation.LocalScalarJointDerivativeBridgeCandidate

/-!
# Exact economic specialization of the five source parameters to (s, v_R)

The source system fixes the parameter order (slack, reserve remuneration
innovation, reserve quantity, reserve requirement, corridor width).
This module restricts the source-defined economic reduced marginal to
the two-dimensional experiment, without replacing the marginal by an
arbitrary mathematical function.

The exact 33 residual equations are inherited from
LocalScalarImplicitReduction when the embedded parameter vector lies
inside its certified neighborhood. The numerical derivative signs are
premises of that source predicate, not consequences of a matrix
certificate proven here.

This does not assert C^1 regularity, a nonzero solution radius in policy
units, a literal equilibrium, or any welfare/growth comparison.
-/

namespace Ventura26LiquidityAllocation
namespace ProposedLocalScalarEconomicSlice

open ProposedLocalScalarJointDerivativeBridge
open ProposedLocalScalarPolicyBifurcation

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- The *exact* source five-parameter vector, with only the normalized
collateral slack and remuneration-of-reserves innovation varied. -/
def reserveRemunerationSlice (s h : ℝ) : Fin 5 → ℝ :=
  s • localScalarSlackDirection + h • localScalarReserveRateDirection

@[simp] theorem reserveRemunerationSlice_slack (s h : ℝ) :
    reserveRemunerationSlice s h 0 = s := by
  simp [reserveRemunerationSlice, localScalarSlackDirection,
    localScalarReserveRateDirection]

@[simp] theorem reserveRemunerationSlice_rate (s h : ℝ) :
    reserveRemunerationSlice s h 1 = h := by
  simp [reserveRemunerationSlice, localScalarSlackDirection,
    localScalarReserveRateDirection]

@[simp] theorem reserveRemunerationSlice_quantity (s h : ℝ) :
    reserveRemunerationSlice s h 2 = 0 := by
  simp [reserveRemunerationSlice, localScalarSlackDirection,
    localScalarReserveRateDirection]

@[simp] theorem reserveRemunerationSlice_requirement (s h : ℝ) :
    reserveRemunerationSlice s h 3 = 0 := by
  simp [reserveRemunerationSlice, localScalarSlackDirection,
    localScalarReserveRateDirection]

@[simp] theorem reserveRemunerationSlice_corridor (s h : ℝ) :
    reserveRemunerationSlice s h 4 = 0 := by
  simp [reserveRemunerationSlice, localScalarSlackDirection,
    localScalarReserveRateDirection]

@[simp] theorem reserveRemunerationSlice_zero :
    reserveRemunerationSlice 0 0 = 0 := by
  simp [reserveRemunerationSlice]

/-- The source policy contract: varying h never silently perturbs the
reserve requirement or corridor. -/
theorem reserveRemunerationSlice_policy_contract (s h : ℝ) :
    (localScalarParameterIntervention (reserveRemunerationSlice s h)).reserveRateInnovation = h ∧
    (localScalarParameterIntervention (reserveRemunerationSlice s h)).reserveQuantityInnovation = 0 ∧
    (localScalarParameterIntervention (reserveRemunerationSlice s h)).reserveRequirement = 0 ∧
    (localScalarParameterIntervention (reserveRemunerationSlice s h)).corridorWidth = 0 := by
  simp [localScalarParameterIntervention]

/-- The marginal is the literal dual recovered through the source
33-variable log chart and the source solutionLog, not a free function. -/
noncomputable def economicReserveRemunerationMarginal
    (P : Primitives S) (Z0 : LocalPrefixCoordinates)
    (solutionLog : (Fin 5 → ℝ) → (Fin 33 → ℝ))
    (s h : ℝ) : ℝ :=
  localScalarReducedMap P Z0 solutionLog (reserveRemunerationSlice s h)

/-- The specific economic scalar is precisely the source financing dual. -/
theorem economicReserveRemunerationMarginal_eq_source_dual
    (P : Primitives S) (Z0 : LocalPrefixCoordinates)
    (solutionLog : (Fin 5 → ℝ) → (Fin 33 → ℝ))
    (s h : ℝ) :
    economicReserveRemunerationMarginal P Z0 solutionLog s h =
      localNormalizedCollateralDualL P
        (localPrefixLogChart Z0
          (solutionLog (reserveRemunerationSlice s h))) := by
  rfl

/-- A source implicit reduction supplies ALL original 33 modified
binding-prefix rows along the experiment, at every parameter point
inside its own open ball. No row is replaced by an assumed zero. -/
theorem economicReserveRemunerationMarginal_source_rows
    (P : Primitives S) (I : InheritedState) (Z0 : LocalPrefixCoordinates)
    (dateOne recurrent : S) (tail : LocalPrefixContinuationRule)
    (solutionLog : (Fin 5 → ℝ) → (Fin 33 → ℝ))
    (hred : LocalScalarImplicitReduction P I Z0 dateOne recurrent tail solutionLog) :
    ∃ radius : ℝ, 0 < radius ∧
      ∀ (s h : ℝ), reserveRemunerationSlice s h ∈
          Metric.ball (0 : Fin 5 → ℝ) radius →
        ∀ row : Fin 33,
          localBindingResidualWithSlack P I Z0 dateOne recurrent tail
            (reserveRemunerationSlice s h)
            (solutionLog (reserveRemunerationSlice s h)) row = 0 := by
  rcases hred with ⟨_hbase, radius, hradius, _hsol, _hM, hrows,
    _hunique, _hblow, _hbhigh, _ha⟩
  refine ⟨radius, hradius, ?_⟩
  intro s h hinside row
  exact hrows (reserveRemunerationSlice s h) hinside row

/-- The two strict signs required by the abstract bifurcation theorem
are extracted from the exact source predicate. The magnitude of the
Schur derivative is NOT independently certified by this proof. -/
theorem economicReserveRemunerationMarginal_source_signs
    (P : Primitives S) (I : InheritedState) (Z0 : LocalPrefixCoordinates)
    (dateOne recurrent : S) (tail : LocalPrefixContinuationRule)
    (solutionLog : (Fin 5 → ℝ) → (Fin 33 → ℝ))
    (hred : LocalScalarImplicitReduction P I Z0 dateOne recurrent tail solutionLog) :
    fderiv ℝ (localScalarReducedMap P Z0 solutionLog)
      (0 : Fin 5 → ℝ) localScalarSlackDirection < 0 ∧
    fderiv ℝ (localScalarReducedMap P Z0 solutionLog)
      (0 : Fin 5 → ℝ) localScalarReserveRateDirection < 0 := by
  rcases hred with ⟨_hbase, radius, _hradius, _hsol, _hM, _hrows,
    _hunique, _hblow, hbhigh, ha⟩
  constructor
  · exact lt_trans hbhigh (by norm_num)
  · exact ha

#print axioms reserveRemunerationSlice_policy_contract
#print axioms economicReserveRemunerationMarginal_eq_source_dual
#print axioms economicReserveRemunerationMarginal_source_rows
#print axioms economicReserveRemunerationMarginal_source_signs

end ProposedLocalScalarEconomicSlice
end Ventura26LiquidityAllocation
