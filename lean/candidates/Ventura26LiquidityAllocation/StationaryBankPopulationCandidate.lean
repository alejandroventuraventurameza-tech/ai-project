import Ventura26LiquidityAllocation.StationaryBankOptimalityCandidate

/-!
# Poblacion bancaria y liquidacion del padre: PROPUESTA SIN COMPILAR

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

Destino propuesto: papers/Ventura26LiquidityAllocation/StationaryBankPopulationCandidate.lean.
SHA256 de StationaryBankOptimalityCandidate.lean utilizado:
2f13e9b1f8e455cbc8e3676066a5dde674b4acf285292990330f21bed84bc918

Argumento matematico previo al codigo:
1. Se usa el constructor fuente de un tipo ex ante, masa uno, cara
   heredada E y la misma ley de pagos. Su plan y valor son los que ya
   tienen optimalidad dinamica, con riqueza individual dependiente de pagos.
2. El patrimonio pre-salida es R*E tanto inicialmente como en sucesores.
   El factor de renovacion 1/R restaura el agregado E; el ingreso neto al
   propietario es eta*(1-psi)*R*E=(R-1)*E.
3. Los saldos -4*W y 8*W, con probabilidades 1/2, generan ofertas
   efectivas 2*W y 4*W. W>0 y su razon 1/2 prueban actividad bilateral.
4. Se transportan los calculos de los flujos individuales que ya
   conservamos: facilidad esperada W, reservas posteriores Mpre+W e
   interbancario esperado cero. No se asume la liquidacion poblacional.
5. Se verifican los ocho bloques de BankPopulationEquilibriumFor:
   masas/caras, cara agregada, optimalidad, renovacion, seis agregados,
   ingreso al propietario, regimen OTC y tres puentes de expectativas.
   El existencial usa n=0, de modo que Fin(n+1)=Fin 1.

ALCANCE: BankPopulationEquilibrium literal, para todo G real. Ese predicado
trata tipos ex ante y sus continuaciones; no contiene la construccion de una
medida invariante de riquezas individuales. Este archivo tampoco la afirma.
-/

open scoped BigOperators
open Filter

namespace Ventura26LiquidityAllocation
namespace ProposedStationaryEquilibrium

open ProposedStationaryRealScale
open ProposedStationaryProductionBridge
open ProposedStationaryReducedSystem
open ProposedStationaryPrimitives
open ProposedStationaryInheritedState
open ProposedStationaryLiteralAccounts
open ProposedStationaryPrivateFeasibility
open ProposedStationaryBankOptimality

/-- Un tipo ex ante de masa uno. Su riqueza individual futura sigue siendo
la del constructor de continuaciones fuente, no una riqueza constante. -/
noncomputable def parentBankPopulation (G : ℝ) :
    BankPopulationCandidate LocalBridgePhase (Fin 1) :=
  massOneFullRetentionBankPopulation (primitives G) (inheritedState G)
    (parentAllocation G) parentBankValue

/-- Patrimonio pre-salida especifico del tipo, incluyendo la cara heredada. -/
theorem parent_bankTypePreExitEquity (G : ℝ) (t : ℕ)
    (h : History LocalBridgePhase t) :
    bankTypePreExitEquity (primitives G) (inheritedState G) (parentAllocation G)
        (commonBankPlan G) t h = ProposedStationaryBank.loanRate * bankEquity := by
  cases t with
  | zero =>
      change bankEquity / (bankRenewalFactor (primitives G) *
        (parentAllocation G).inflation 0 h) = _
      rw [parent_inflation, bankRenewalFactor_eq
        (primitives G) (stationary_parameters G)]
      field_simp [ne_of_gt loanRate_pos] <;> ring
  | succ n =>
      change expectedBankGrossReturn (primitives G) (parentAllocation G)
        (commonBankPlan G) n (previousHistory h) /
          (parentAllocation G).inflation (n + 1) h = _
      rw [commonBankPlan_expectedGrossReturn, parent_inflation, div_one]

theorem parent_bankTypeRenewalFlows (G : ℝ) :
    BankTypeRenewalFlows (primitives G) (inheritedState G) (parentAllocation G)
      (commonBankPlan G) := by
  intro t h _hh
  change (parentAllocation G).bankEquity t h =
    bankRenewalFactor (primitives G) *
      bankTypePreExitEquity (primitives G) (inheritedState G) (parentAllocation G)
        (commonBankPlan G) t h
  rw [parent_bankEquity, parent_bankTypePreExitEquity,
    bankRenewalFactor_eq (primitives G) (stationary_parameters G)]
  field_simp [ne_of_gt loanRate_pos] <;> ring

theorem parent_bankTypeOwnerIncome (G : ℝ) (t : ℕ)
    (h : History LocalBridgePhase t) :
    bankTypeOwnerIncome (primitives G) (inheritedState G) (parentAllocation G)
        (commonBankPlan G) t h =
      (ProposedStationaryBank.loanRate - 1) * bankEquity := by
  unfold bankTypeOwnerIncome
  rw [parent_bankTypePreExitEquity]
  change 0 + (1 / 10 : ℝ) * (1 - seedShare) *
    (ProposedStationaryBank.loanRate * bankEquity) = _
  unfold seedShare
  field_simp [ne_of_gt loanRate_pos] <;> ring

/-- La completacion real/fiscal y el cambio del dual empresarial no alteran
los campos que generan el flujo individual de facilidad. Es transporte
definicional al calculo conservado, no una igualdad agregada asumida. -/
theorem parent_commonBankPlan_expectedFacility (G : ℝ) (t : ℕ)
    (h : History LocalBridgePhase t) :
    finiteSupportExpectation (primitives G).paymentSupport
        (primitives G).paymentProbability
        (fun omega ↦ (commonBankPlan G).facility omega t h) = facilityBorrowing := by
  change localSlackExpectedFacility (primitives G) (fun _ ↦ dateData) t h = _
  exact expectedFacility_eq (primitives G) (stationary_parameters G)
    0 1 (binary_payment_law G) t h rfl

theorem parent_commonBankPlan_expectedPostReserves (G : ℝ) (t : ℕ)
    (h : History LocalBridgePhase t) :
    finiteSupportExpectation (primitives G).paymentSupport
        (primitives G).paymentProbability
        (fun omega ↦ (commonBankPlan G).reservesPost omega t h) = reservesPost := by
  change localSlackExpectedPostReserves (primitives G) (fun _ ↦ dateData) t h = _
  exact expectedPostReserves_eq (primitives G) (stationary_parameters G)
    0 1 (binary_payment_law G) t h rfl

theorem parent_commonBankPlan_expectedInterbank (G : ℝ) (t : ℕ)
    (h : History LocalBridgePhase t) :
    finiteSupportExpectation (primitives G).paymentSupport
        (primitives G).paymentProbability
        (fun omega ↦ (commonBankPlan G).interbank omega t h) = 0 := by
  change localSlackExpectedInterbank (primitives G) (fun _ ↦ dateData) t h = 0
  exact stationary_expectedInterbank_eq_zero
    (primitives G) 0 1 (binary_payment_law G) t h rfl

noncomputable def parentBankDeficitSupply (G : ℝ) (t : ℕ)
    (h : History LocalBridgePhase t) : ℝ :=
  bankDeficitSupplyAt (primitives G) (parentAllocation G) t h
    (parentBankPopulation G).mass
    (fun j ↦ ((parentBankPopulation G).plan j).reservesPre t h)
    (fun j ↦ ((parentBankPopulation G).plan j).deposits t h)
    (fun j ↦ ((parentBankPopulation G).paymentLaw j).support)
    (fun j ↦ ((parentBankPopulation G).paymentLaw j).probability)
    (fun j ↦ ((parentBankPopulation G).paymentLaw j).shock)

noncomputable def parentBankSurplusSupply (G : ℝ) (t : ℕ)
    (h : History LocalBridgePhase t) : ℝ :=
  bankSurplusSupplyAt (primitives G) (parentAllocation G) t h
    (parentBankPopulation G).mass
    (fun j ↦ ((parentBankPopulation G).plan j).reservesPre t h)
    (fun j ↦ ((parentBankPopulation G).plan j).deposits t h)
    (fun j ↦ ((parentBankPopulation G).paymentLaw j).support)
    (fun j ↦ ((parentBankPopulation G).paymentLaw j).probability)
    (fun j ↦ ((parentBankPopulation G).paymentLaw j).shock)

theorem parent_bankDeficitSupply_eq (G : ℝ) (t : ℕ)
    (h : History LocalBridgePhase t) :
    parentBankDeficitSupply G t h = 2 * facilityBorrowing := by
  classical
  change (∑ _j : Fin 1, (1 : ℝ) *
    finiteSupportExpectation (primitives G).paymentSupport
      (primitives G).paymentProbability (fun omega ↦
        max (-bankSettlementSurplus ((parentAllocation G).reservesPrePayment t h)
          ((primitives G).reserveRequirementPath t h)
          ((parentAllocation G).depositRate t h / (parentAllocation G).reserveRate t h)
          ((parentAllocation G).bankDeposits t h) ((primitives G).paymentShock omega)) 0)) = _
  simp only [Finset.univ_unique, Finset.sum_singleton, one_mul]
  rw [finiteSupportExpectation_eq_average_of_binarySymmetric
    (primitives G) 0 1 (1 / 5) (binary_payment_law G)]
  simp only [parent_reservesPrePayment, parent_depositRate, parent_reserveRate,
    parent_bankDeposits]
  change (max (-bankSettlementSurplus reservesPre (1 / 10)
      (ProposedStationaryBank.depositRate / ProposedStationaryBank.reserveRate)
      bankDeposits (-(1 / 5))) 0 +
    max (-bankSettlementSurplus reservesPre (1 / 10)
      (ProposedStationaryBank.depositRate / ProposedStationaryBank.reserveRate)
      bankDeposits (1 / 5)) 0) / 2 = _
  rw [settlementSurplus_minus, settlementSurplus_plus]
  have hw := facilityBorrowing_pos
  rw [max_eq_left (by linarith : 0 ≤ -(-4 * facilityBorrowing)),
    max_eq_right (by linarith : -(8 * facilityBorrowing) ≤ 0)]
  ring

theorem parent_bankSurplusSupply_eq (G : ℝ) (t : ℕ)
    (h : History LocalBridgePhase t) :
    parentBankSurplusSupply G t h = 4 * facilityBorrowing := by
  classical
  change (∑ _j : Fin 1, (1 : ℝ) *
    finiteSupportExpectation (primitives G).paymentSupport
      (primitives G).paymentProbability (fun omega ↦
        max (bankSettlementSurplus ((parentAllocation G).reservesPrePayment t h)
          ((primitives G).reserveRequirementPath t h)
          ((parentAllocation G).depositRate t h / (parentAllocation G).reserveRate t h)
          ((parentAllocation G).bankDeposits t h) ((primitives G).paymentShock omega)) 0)) = _
  simp only [Finset.univ_unique, Finset.sum_singleton, one_mul]
  rw [finiteSupportExpectation_eq_average_of_binarySymmetric
    (primitives G) 0 1 (1 / 5) (binary_payment_law G)]
  simp only [parent_reservesPrePayment, parent_depositRate, parent_reserveRate,
    parent_bankDeposits]
  change (max (bankSettlementSurplus reservesPre (1 / 10)
      (ProposedStationaryBank.depositRate / ProposedStationaryBank.reserveRate)
      bankDeposits (-(1 / 5))) 0 +
    max (bankSettlementSurplus reservesPre (1 / 10)
      (ProposedStationaryBank.depositRate / ProposedStationaryBank.reserveRate)
      bankDeposits (1 / 5)) 0) / 2 = _
  rw [settlementSurplus_minus, settlementSurplus_plus]
  have hw := facilityBorrowing_pos
  rw [max_eq_right (by linarith : -4 * facilityBorrowing ≤ 0),
    max_eq_left (by linarith : 0 ≤ 8 * facilityBorrowing)]
  ring

/-- Se selecciona la rama bilateral por sus cantidades estrictamente
positivas, conservando la disyuncion fuente completa como conclusion. -/
theorem parent_bankPopulationOTCRegime (G : ℝ) (t : ℕ)
    (h : History LocalBridgePhase t) :
    BankPopulationOTCRegimeAt (primitives G) (parentAllocation G)
      (parentBankPopulation G) t h := by
  apply Or.inl
  refine ⟨?_, ?_, ?_⟩
  · change BilateralOTCActivity (parentBankDeficitSupply G t h)
      (parentBankSurplusSupply G t h) ((parentAllocation G).bankTightness t h)
    rw [parent_bankDeficitSupply_eq, parent_bankSurplusSupply_eq, parent_bankTightness]
    have hw := facilityBorrowing_pos
    refine ⟨by positivity, by positivity, ?_⟩
    field_simp [ne_of_gt hw] <;> ring
  · intro j
    change BankCandidateOTCFlowsAt
      ((primitives G).withBankPaymentLaw (primitives G).primitiveBankPaymentLaw)
      (parentAllocation G) (commonBankPlan G) t h
      ((parentAllocation G).bankTightness t h)
    rw [Primitives.with_primitiveBankPaymentLaw]
    exact fullRetentionCommonBankPlan_candidateFlows
      (primitives G) (parentAllocation G) t h
  · rw [parent_interbankRate, parent_reserveRate, parent_facilityRate,
      parent_bankTightness] <;> rfl

theorem parent_bankPopulation_settlementBridges (G : ℝ) (t : ℕ)
    (h : History LocalBridgePhase t) :
    expectedFacilityBorrowing (primitives G) (parentAllocation G) t h =
        bankPopulationExpectedFacilityAt (parentBankPopulation G) t h ∧
      expectedPostReserves (primitives G) (parentAllocation G) t h =
        bankPopulationExpectedPostReservesAt (parentBankPopulation G) t h ∧
      (parentAllocation G).interbankPosition t h =
        bankPopulationExpectedInterbankAt (parentBankPopulation G) t h := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · change (parentAllocation G).facilityBorrowing t h =
      ∑ _j : Fin 1, (1 : ℝ) *
        finiteSupportExpectation (primitives G).paymentSupport
          (primitives G).paymentProbability
          (fun omega ↦ (commonBankPlan G).facility omega t h)
    simp only [parent_facilityBorrowing, Finset.univ_unique, Finset.sum_singleton, one_mul]
    exact (parent_commonBankPlan_expectedFacility G t h).symm
  · change (parentAllocation G).reservesPostPayment t h =
      ∑ _j : Fin 1, (1 : ℝ) *
        finiteSupportExpectation (primitives G).paymentSupport
          (primitives G).paymentProbability
          (fun omega ↦ (commonBankPlan G).reservesPost omega t h)
    simp only [parent_reservesPostPayment, Finset.univ_unique, Finset.sum_singleton, one_mul]
    exact (parent_commonBankPlan_expectedPostReserves G t h).symm
  · change (parentAllocation G).interbankPosition t h =
      ∑ _j : Fin 1, (1 : ℝ) *
        finiteSupportExpectation (primitives G).paymentSupport
          (primitives G).paymentProbability
          (fun omega ↦ (commonBankPlan G).interbank omega t h)
    simp only [parent_interbankPosition, Finset.univ_unique, Finset.sum_singleton, one_mul]
    exact (parent_commonBankPlan_expectedInterbank G t h).symm

/-- Los ocho bloques del predicado de poblacion se verifican por separado;
la existencia de un banco optimo no se toma como sustituto de agregacion. -/
theorem parent_bankPopulationEquilibriumFor (G : ℝ) :
    BankPopulationEquilibriumFor (primitives G) (inheritedState G)
      (parentAllocation G) (parentBankPopulation G) := by
  classical
  have hI : (inheritedState G).withBankFace bankEquity = inheritedState G := rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j
    change 0 < (1 : ℝ) ∧ 0 < bankEquity
    exact ⟨by norm_num, bank_scale_pos.1⟩
  · exact massOneFullRetentionBankPopulation_initialFace
      (primitives G) (inheritedState G) (parentAllocation G) parentBankValue
  · intro j
    change BankOptimalWithValue
      ((primitives G).withBankPaymentLaw (primitives G).primitiveBankPaymentLaw)
      ((inheritedState G).withBankFace bankEquity)
      (parentAllocation G) (commonBankPlan G) parentBankValue
    rw [Primitives.with_primitiveBankPaymentLaw, hI]
    exact parent_bankOptimalWithValue G
  · intro j
    change BankTypeRenewalFlows
      ((primitives G).withBankPaymentLaw (primitives G).primitiveBankPaymentLaw)
      ((inheritedState G).withBankFace bankEquity)
      (parentAllocation G) (commonBankPlan G)
    rw [Primitives.with_primitiveBankPaymentLaw, hI]
    exact parent_bankTypeRenewalFlows G
  · intro t h _hh
    exact massOneFullRetentionBankPopulation_aggregates
      (primitives G) (inheritedState G) (parentAllocation G) parentBankValue t h
      (parent_bankDividend G t h)
      (by rw [parent_bankRetainedEquity, parent_bankEquity])
  · intro t h _hh
    change (parentAllocation G).bankNetIncome t h =
      ∑ _j : Fin 1, (1 : ℝ) * bankTypeOwnerIncome
        ((primitives G).withBankPaymentLaw (primitives G).primitiveBankPaymentLaw)
        ((inheritedState G).withBankFace bankEquity)
        (parentAllocation G) (commonBankPlan G) t h
    rw [Primitives.with_primitiveBankPaymentLaw, hI]
    simp only [Finset.univ_unique, Finset.sum_singleton, one_mul,
      parent_bankNetIncome, parent_bankTypeOwnerIncome]
  · intro t h _hh
    exact parent_bankPopulationOTCRegime G t h
  · intro t h _hh
    exact parent_bankPopulation_settlementBridges G t h

/-- Existencial fuente con un tipo (n=0, Fin(n+1)=Fin 1). -/
theorem parent_bankPopulationEquilibrium (G : ℝ) :
    BankPopulationEquilibrium (primitives G) (inheritedState G)
      (parentAllocation G) := by
  exact ⟨0, parentBankPopulation G, parent_bankPopulationEquilibriumFor G⟩

end ProposedStationaryEquilibrium
end Ventura26LiquidityAllocation
