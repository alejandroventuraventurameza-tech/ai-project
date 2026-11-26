import Ventura26LiquidityAllocation.StationaryBankContinuationCandidate

/-!
# Optimalidad bancaria del padre estacionario: PROPUESTA SIN COMPILAR

Proyecto: alejandroventuraventurameza-tech/ai-project.
Rama: work/chat-continuity.
Commit: 16e24fe828a5a0002ef13bb82bae9e295f190f86.
Base AppliedModelingLib: 194edcc95df74806a39b961d10dedddc6e730cce.
Lean previsto: leanprover/lean4:v4.30.0-rc2.
Mathlib: 5450b53e5ddc75d46418fabb605edbf36bd0beb6.

ESTADO: PROPUESTA SIN COMPILAR. No hay Lean, Lake, Elan ni ejecutor
Lean remoto disponible en esta sesion. Las demostraciones matematicas y
la revision estatica de interfaces no acreditan elaboracion, compilacion,
revision del kernel ni auditoria transitiva de axiomas.
Los archivos fuente fijados no se modifican. G permanece simbolico y
se conservan ambas ramas macroeconomicas S y B. Estos modulos se refieren
al padre estacionario; no certifican una continuacion perturbada.

Destino propuesto: papers/Ventura26LiquidityAllocation/StationaryBankOptimalityCandidate.lean.
SHA256 de StationaryBankContinuationCandidate.lean utilizado:
0651680182801f185aeff0f82d76432817272d8fe8d1ae19ad6f4a8e49e28ed5

Argumento matematico previo al codigo:
1. La continuacion concreta es factible, tiene objetivo sumable y cumple
   la condicion terminal: son resultados separados de la cadena previa.
2. Toda alternativa fuente factible con objetivo bien definido tiene
   pago<=vB*E. La continuacion concreta alcanza vB*E. Esto completa
   BankContinuationOptimalAt sin agregar TVC a las alternativas.
3. El plan comun es factible y la continuacion coincide con sus seis
   campos iniciales. Junto con V(t,e,h)=vB*e, su homogeneidad y el entorno
   Bellman demostrado, se satisface BankOptimalWithValue y luego BankOptimal.
4. Se reunen las comparaciones de H, L, hogar y banco. G>=Mpre aparece
   solo para la factibilidad del hogar; el bloque bancario vale para todo G.

ALCANCE: optimalidad bancaria del padre en el predicado literal fuente.
No constituye CompetitiveEquilibrium: RetailOptimal, CapitalProducerOptimal,
las obligaciones de poblacion y el resto del registro de equilibrio siguen
separados. No se afirma unicidad, distribucion individual estacionaria ni
continuacion perturbada de S o B.
-/

open scoped BigOperators
open Filter

namespace Ventura26LiquidityAllocation
namespace ProposedStationaryBankOptimality

open ProposedStationaryRealScale
open ProposedStationaryPrimitives
open ProposedStationaryInheritedState
open ProposedStationaryLiteralAccounts
open ProposedStationaryPrivateFeasibility
open ProposedStationaryTerminal

/-- Optimalidad de la continuacion individual completa, ante TODA
alternativa factible con objetivo bien definido en el sentido fuente. -/
theorem parent_bankContinuationOptimal
    (G : ℝ) (t : ℕ) (h : History LocalBridgePhase t)
    (hh : FirmHistoryAdmissible (primitives G) t h) :
    BankContinuationOptimalAt (primitives G) (parentAllocation G) t h bankEquity
      (parentBankContinuation G t h) := by
  refine ⟨parent_bankContinuation_feasible G t h hh,
    (parent_bankContinuation_objective_and_terminal G t h).1,
    (parent_bankContinuation_objective_and_terminal G t h).2, ?_⟩
  intro alternative hfeasible hdefined
  rw [parent_bankContinuation_payoff_eq_value]
  exact parent_bankContinuationPayoff_le G bankValueSlope bankValueSlope_gt_one.le
    bankValueSlope_identity t h bankEquity alternative hfeasible hdefined

/-- El proceso V(t,e,h)=v*e satisface la homogeneidad y el entorno Bellman,
y su valor en E es alcanzado por una continuacion optima que coincide con
los seis controles iniciales del plan comun. No se asume ninguna de esas
conclusiones como hipotesis economica. -/
theorem parent_bankOptimalWithValue (G : ℝ) :
    BankOptimalWithValue (primitives G) (inheritedState G) (parentAllocation G)
      (commonBankPlan G) parentBankValue := by
  refine ⟨commonBankPlan_feasible G, ?_⟩
  intro t h hh
  refine ⟨parent_bankValue_homogeneous G t h,
    parent_bankBellmanLocalEnvironment G t h hh,
    parentBankContinuation G t h,
    parent_bankContinuation_startsWithPlanAt G t h, ?_, ?_⟩
  · have hequity : (commonBankPlan G).equity t h = bankEquity :=
      parent_bankEquity G t h
    simpa only [hequity] using parent_bankContinuationOptimal G t h hh
  · change bankContinuationPayoffAt (primitives G) (parentAllocation G) t h
        (parentBankContinuation G t h) =
      bankValueSlope * ((commonBankPlan G).equity t h)
    have hequity : (commonBankPlan G).equity t h = bankEquity :=
      parent_bankEquity G t h
    rw [hequity]
    exact parent_bankContinuation_payoff_eq_value G t h

/-- Predicado bancario literal del checkpoint para el padre construido.
G sigue siendo simbolico. Esto no afirma el equilibrio competitivo completo. -/
theorem parent_bankOptimal (G : ℝ) :
    BankOptimal (primitives G) (inheritedState G) (parentAllocation G) := by
  exact ⟨commonBankPlan G, parentBankValue, parent_bankOptimalWithValue G⟩

/-- Reunir las tres comparaciones realizadas: ambas empresas, hogar y banco.
La restriccion sobre G se necesita para la cartera de bonos del hogar.
Minoristas, productores de capital y el resto del registro de equilibrio
continuan siendo obligaciones separadas. -/
theorem parent_firms_household_bankOptimal (G : ℝ) (hG : reservesPre ≤ G) :
    (∀ i, FirmOptimal (primitives G) (inheritedState G) (parentAllocation G) i) ∧
      HouseholdOptimal (primitives G) (inheritedState G) (parentAllocation G) ∧
      BankOptimal (primitives G) (inheritedState G) (parentAllocation G) := by
  refine ⟨?_, ?_, parent_bankOptimal G⟩
  · intro i
    exact ProposedStationaryFirmOptimality.parent_firmOptimal G i
  · exact ProposedStationaryHouseholdOptimality.parent_householdOptimal G hG

end ProposedStationaryBankOptimality
end Ventura26LiquidityAllocation
