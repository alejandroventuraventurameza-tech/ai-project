import Ventura26LiquidityAllocation.StationaryProductionSectorsCandidate
import Ventura26LiquidityAllocation.StationaryBankPopulationCandidate

/-!
# Ensamblaje del equilibrio competitivo estacionario: PROPUESTA SIN COMPILAR

Proyecto: alejandroventuraventurameza-tech/ai-project.
Rama: work/chat-continuity.
Commit: 16e24fe828a5a0002ef13bb82bae9e295f190f86.
Base AppliedModelingLib: 194edcc95df74806a39b961d10dedddc6e730cce.
Lean previsto: leanprover/lean4:v4.30.0-rc2.
Mathlib: 5450b53e5ddc75d46418fabb605edbf36bd0beb6.

ESTADO: PROPUESTA SIN COMPILAR. No se han ejecutado Lean, Lake ni
simulaciones. Las demostraciones matematicas y las revisiones de codigo
no acreditan elaboracion, compilacion, comprobacion por el kernel ni
una auditoria transitiva de axiomas. Toda la cadena propuesta conserva
este estado. Las fuentes fijadas no se modifican.

Las cantidades son las del padre estacionario. G permanece simbolico;
no se fija a un multiplo de reservas. Se conservan S y B como ramas
macroeconomicas separadas. Ningun resultado de estos modulos acredita
una continuacion perturbada, una IRF o unicidad del equilibrio completo.

Destino propuesto: papers/Ventura26LiquidityAllocation/StationaryEquilibriumCandidate.lean.
SHA256 de StationaryProductionSectorsCandidate.lean utilizado:
c99ba16310fa721e63af0bc22a409ca38d26a937d60348178c1ca2852de4b60c
SHA256 de StationaryBankPopulationCandidate.lean utilizado:
84724d7f7a5c7080100cf488dd73e5d0ff98f11e2c1ef3309e3c1fa4a671c8bf

Argumento matematico previo al codigo:
1. Se verifican todos los dominios positivos, la identidad de caras
   nominales y las cuatro reglas monetarias. Los interceptos y rezagos
   monetarios coinciden con RR y Mpre; inflacion=1 e innovaciones=0.
   Se distingue el rezago Mpre del Mpost empleado en la cuenta fiscal.
2. Los lemas fuente de completacion real dan produccion y acumulacion
   con el capital heredado en fecha cero y las elecciones anteriores en
   sucesores. La completacion fiscal preserva esos campos.
3. Se ensamblan los 22 componentes de CompetitiveEquilibrium: dominios,
   reglas, optimalidades de ambos empresarios/hogar/poblacion bancaria/
   minorista/productor de capital, presupuestos, caras nominales,
   produccion, cuentas, balance, fiscalidad y vaciado de todos los mercados.
   Ningun componente de equilibrio aparece como premisa del teorema final.
4. G>=Mpre se requiere para los bonos del hogar G-Mpre>=0; como Mpre>0,
   tambien garantiza G>0 en el dominio monetario primitivo. El banco y
   ambos sectores de produccion conservan sus resultados para todo G.
5. Reciprocamente, si ESTA asignacion cumple CompetitiveEquilibrium,
   HouseholdOptimal contiene la factibilidad de sus bonos en la historia
   inicial de peso positivo. Ello fuerza G>=Mpre. La equivalencia final
   caracteriza esta familia de candidatos, no todas las asignaciones posibles.

ALCANCE FINAL:
  CompetitiveEquilibrium (primitives G) (inheritedState G) (parentAllocation G)
    si y solo si reservesPre<=G.
Es la conclusion matematica que el codigo propone formalizar. El archivo
sigue SIN COMPILAR y depende de toda la cadena de candidatos sin compilar.
No aporta FiniteBankPrefixDynamicWitness, las 33 ecuaciones del prefijo
intervenido, un certificado no lineal de cola ni una distribucion invariante
individual. Esas tareas y las continuaciones perturbadas S/B siguen separadas.
-/

open scoped BigOperators
open Filter

namespace Ventura26LiquidityAllocation
namespace ProposedStationaryEquilibrium

open ProposedStationaryRealScale
open ProposedStationaryPrimitives
open ProposedStationaryInheritedState
open ProposedStationaryLiteralAccounts
open ProposedStationaryPrivateFeasibility

theorem parent_monetaryPolicyPrimitiveDomain (G : ℝ) (hG : reservesPre ≤ G) :
    MonetaryPolicyPrimitiveDomain (primitives G) (inheritedState G) := by
  exact inherited_monetary_domain G hG

/-- Todos los dominios corrientes se verifican sin restringir G; su cota
inferior se necesita por separado para los bonos y el dominio primitivo. -/
theorem parent_positiveDomain (G : ℝ) :
    PositiveDomain (primitives G) (parentAllocation G) := by
  have hRR : 0 < ProposedStationaryBank.reserveRate :=
    lt_trans (by norm_num) ProposedStationaryBank.reserveRate_spec.1
  have hRD : 0 < ProposedStationaryBank.depositRate := by
    norm_num [ProposedStationaryBank.depositRate]
  intro t h _hh
  simp only [parent_workerConsumption, parent_firmConsumption, parent_capital,
    parent_aggregateCapital, parent_output, parent_inputPrice, parent_wage,
    parent_inflation, parent_capitalPrice, parent_reserveRate, parent_depositRate,
    parent_loanRate, parent_facilityRate, parent_reservesPrePayment]
  change 0 < workerConsumption ∧
    (∀ i, 0 < firmConsumption i ∧ 0 < capital i) ∧
    0 < aggregateCapital ∧ 0 < aggregateOutput ∧
    0 < (5 / 6 : ℝ) ∧ 0 < wage ∧ 0 < (1 : ℝ) ∧ 0 < capitalPrice ∧
    0 < ProposedStationaryBank.reserveRate ∧ 0 < ProposedStationaryBank.depositRate ∧
    0 < ProposedStationaryBank.loanRate ∧ 0 < (1 / 50 : ℝ) ∧
    facilityRate = ProposedStationaryBank.reserveRate + (1 / 50 : ℝ) ∧
    0 ≤ (1 / 10 : ℝ) ∧ (1 / 10 : ℝ) < 1 ∧ 0 < reservesPre
  exact ⟨workerConsumption_pos, fun i ↦ ⟨firmConsumption_pos i, capital_pos i⟩,
    aggregates_pos.1, aggregates_pos.2.1, by norm_num, wage_pos, by norm_num,
    capitalPrice_pos, hRR, hRD, loanRate_pos, by norm_num, rfl,
    by norm_num, by norm_num, bank_scale_pos.2.2⟩

/-- Las cuatro reglas fuente se verifican tanto en fecha cero con los
rezagos heredados como en cada sucesor con su historia anterior. -/
theorem parent_monetaryPolicyRules (G : ℝ) :
    MonetaryPolicyRules (primitives G) (inheritedState G) (parentAllocation G) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro h _hh
    simp only [parent_reserveRate, parent_inflation, parent_output]
    change Real.log ProposedStationaryBank.reserveRate =
      (1 / 2 : ℝ) * Real.log ProposedStationaryBank.reserveRate +
        (1 - (1 / 2 : ℝ)) *
          (Real.log ProposedStationaryBank.reserveRate +
            (3 / 2 : ℝ) * Real.log (1 : ℝ) +
            (1 / 8 : ℝ) * Real.log (aggregateOutput / aggregateOutput)) + 0
    simp only [div_self (ne_of_gt aggregates_pos.2.1), Real.log_one]
    ring
  · intro h _hh
    simp only [parent_reservesPrePayment]
    change Real.log reservesPre =
      (1 / 2 : ℝ) * Real.log reservesPre +
        (1 - (1 / 2 : ℝ)) * Real.log reservesPre + 0
    ring
  · intro t h s _hh
    simp only [parent_reserveRate, parent_inflation, parent_output]
    change Real.log ProposedStationaryBank.reserveRate =
      (1 / 2 : ℝ) * Real.log ProposedStationaryBank.reserveRate +
        (1 - (1 / 2 : ℝ)) *
          (Real.log ProposedStationaryBank.reserveRate +
            (3 / 2 : ℝ) * Real.log (1 : ℝ) +
            (1 / 8 : ℝ) * Real.log (aggregateOutput / aggregateOutput)) + 0
    simp only [div_self (ne_of_gt aggregates_pos.2.1), Real.log_one]
    ring
  · intro t h s _hh
    simp only [parent_reservesPrePayment]
    change Real.log reservesPre =
      (1 / 2 : ℝ) * Real.log reservesPre +
        (1 - (1 / 2 : ℝ)) * Real.log reservesPre + 0
    ring

/-- La cara vigente es el reembolso nominal neto del deposito empresarial.
La consistencia heredada sigue siendo el teorema separado ya conservado. -/
theorem parent_currentNominalFaceConsistency (G : ℝ) :
    CurrentNominalFaceConsistency (primitives G) (parentAllocation G) := by
  intro i t h _hh
  simp only [parent_firmFace, parent_loanRate, parent_loan, parent_depositRate,
    parent_firmDeposit, mul_zero, sub_zero]
  exact (firm_loan_face_identity i).symm

/-- La produccion respeta el capital heredado de fecha cero y el capital
elegido en la historia anterior de cada sucesor. Se usa el lema fuente. -/
theorem parent_aggregateProduction (G : ℝ) :
    AggregateProduction (primitives G) (inheritedState G) (parentAllocation G) := by
  simpa only [parentAllocation, withSourceAccountingCompletion,
    AggregateProduction, withSourceFiscalAccounts] using
      withSourceRealAccounts_aggregateProduction (primitives G) (inheritedState G)
        (parentSettlementCarrier G)

/-- Las tres identidades fuente del mercado de capital, incluido su timing
heredado y la acumulacion con inversion, provienen de la completacion real. -/
theorem parent_capitalClears (G : ℝ) :
    CapitalClears (primitives G) (inheritedState G) (parentAllocation G) := by
  simpa only [parentAllocation, withSourceAccountingCompletion,
    CapitalClears, withSourceFiscalAccounts] using
      withSourceRealAccounts_capitalClears (primitives G) (inheritedState G)
        (parentSettlementCarrier G)

/-- Costo de ajuste de precios e ingreso minorista se mantienen separados;
el ingreso no se confunde con el costo de recursos. -/
theorem parent_accountingIdentities (G : ℝ) :
    AccountingIdentities (primitives G) (parentAllocation G) := by
  change AccountingIdentities (primitives G)
    (withSourceFiscalAccounts (primitives G) (inheritedState G)
      (withSourceRealAccounts (primitives G) (inheritedState G)
        (parentSettlementCarrier G)))
  apply (withSourceFiscalAccounts_preserves_accountingIdentities
    (primitives G) (inheritedState G)
    (withSourceRealAccounts (primitives G) (inheritedState G)
      (parentSettlementCarrier G))).2
  exact withSourceRealAccounts_accountingIdentities
    (primitives G) (inheritedState G) (parentSettlementCarrier G)

open ProposedStationaryRealScale
open ProposedStationaryPrimitives
open ProposedStationaryInheritedState
open ProposedStationaryLiteralAccounts
open ProposedStationaryPrivateFeasibility
open ProposedStationaryFirmOptimality
open ProposedStationaryHouseholdOptimality
open ProposedStationaryProductionSectors

/-- Equilibrio competitivo del padre estacionario, en el predicado literal
del checkpoint. La cota sobre G mantiene no negativos los bonos del hogar
y garantiza el dominio monetario primitivo, puesto que Mpre>0.
Este enunciado no es una afirmacion sobre perturbaciones de S o B. -/
theorem parent_competitiveEquilibrium (G : ℝ) (hG : reservesPre ≤ G) :
    CompetitiveEquilibrium (primitives G) (inheritedState G) (parentAllocation G) := by
  exact ⟨parent_monetaryPolicyPrimitiveDomain G hG,
    parent_positiveDomain G,
    parent_monetaryPolicyRules G,
    (fun i ↦ parent_firmOptimal G i),
    parent_householdOptimal G hG,
    parent_bankPopulationEquilibrium G,
    parent_retailOptimal G,
    parent_capitalProducerOptimal G,
    parent_firmBudgetFlows G,
    parent_householdBudgetFlows G,
    inherited_nominalFaceConsistency G,
    parent_currentNominalFaceConsistency G,
    parent_aggregateProduction G,
    parent_capitalProducerAccounts G,
    parent_accountingIdentities G,
    parent_bankBalance G,
    parentAllocation_fiscalClosure G,
    parent_creditClears G,
    parent_depositsClear G,
    parent_capitalClears G,
    parent_laborClears G,
    parent_resourceClears G⟩

/-- La condicion sobre G es tambien necesaria para ESTA asignacion:
HouseholdOptimal contiene factibilidad, y el hogar tiene bonos G-Mpre
en la historia canonica inicial, cuyo peso es positivo.
No se afirma inexistencia de otras asignaciones cuando G<Mpre. -/
theorem parent_competitiveEquilibrium_iff (G : ℝ) :
    CompetitiveEquilibrium (primitives G) (inheritedState G) (parentAllocation G) ↔
      reservesPre ≤ G := by
  constructor
  · intro hEquilibrium
    have hHousehold : HouseholdOptimal (primitives G) (inheritedState G)
        (parentAllocation G) := hEquilibrium.2.2.2.2.1
    have hFeasible : HouseholdFeasible (primitives G) (inheritedState G)
        (parentAllocation G) (householdPlanOfAllocation (parentAllocation G)) :=
      hHousehold.1
    have hBonds := (hFeasible.1 0 (localBridgeHistory 0)
      (localBridgeHistory_admissible G 0)).2.2.2
    change 0 ≤ (parentAllocation G).householdBonds 0 (localBridgeHistory 0) at hBonds
    rw [parent_householdBonds] at hBonds
    exact sub_nonneg.mp hBonds
  · intro hG
    exact parent_competitiveEquilibrium G hG

end ProposedStationaryEquilibrium
end Ventura26LiquidityAllocation
