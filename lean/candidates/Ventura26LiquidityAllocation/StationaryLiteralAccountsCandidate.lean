import Ventura26LiquidityAllocation.StationaryInheritedStateCandidate

/-!
# Campos y cuentas literales del padre: PROPUESTA SIN COMPILAR

Proyecto: alejandroventuraventurameza-tech/ai-project.
Rama: work/chat-continuity.
Commit: 16e24fe828a5a0002ef13bb82bae9e295f190f86.
Base AppliedModelingLib: 194edcc95df74806a39b961d10dedddc6e730cce.
Lean previsto: leanprover/lean4:v4.30.0-rc2.
Mathlib: 5450b53e5ddc75d46418fabb605edbf36bd0beb6.
Destino: papers/Ventura26LiquidityAllocation/StationaryLiteralAccountsCandidate.lean.
SHA256 del modulo importado:
931c1c325d902d6f6531011789414783d4dbd481fc0f2df1ce72e708dd529e8a

Identifica los campos de parentAllocation G con los niveles ya construidos.
Las cuentas fuente utilizan capital heredado en t=0 y el de la historia
anterior despues. Ambos se comprueban, sin asumir produccion o ingresos.
Se obtiene I=K/40, Gamma=161K/6400, ingreso minorista Y/6, ingreso del
productor de capital K/6400 e ingreso bancario (RL-1)E.

Estas identidades sirven para demostrar presupuestos y factibilidad en
un modulo posterior. No afirman optimalidad, terminalidad ni equilibrio.
Todos los modulos de la cadena son candidatos sin compilar. No se han
ejecutado Lean ni simulaciones; revision estatica no sustituye kernel,
inspeccion de axiomas o auditoria semantica. Se conservan S y B.
-/

namespace Ventura26LiquidityAllocation
namespace ProposedStationaryLiteralAccounts

open ProposedStationaryRealScale
open ProposedStationaryProductionBridge
open ProposedStationaryReducedSystem
open ProposedStationaryPrimitives
open ProposedStationaryInheritedState
open scoped BigOperators

noncomputable def wealth (i : FirmType) : ℝ :=
  profit i + (39 / 40) * capitalPrice * capital i - firmFace i

@[simp] theorem parent_firmConsumption (G : ℝ) (i : FirmType)
    (t : ℕ) (h : History LocalBridgePhase t) :
    (parentAllocation G).firmConsumption i t h = firmConsumption i := by
  change localPrefixFirmConsumption controls i = firmConsumption i
  exact firmConsumption_field i

@[simp] theorem parent_capital (G : ℝ) (i : FirmType)
    (t : ℕ) (h : History LocalBridgePhase t) :
    (parentAllocation G).capital i t h = capital i := rfl

@[simp] theorem parent_labor (G : ℝ) (i : FirmType)
    (t : ℕ) (h : History LocalBridgePhase t) :
    (parentAllocation G).labor i t h = labor i := by
  exact localPrefixLabor_eq (primitives G)
    (stationary_parameters G).toStationaryRealParameters i

@[simp] theorem parent_loan (G : ℝ) (i : FirmType)
    (t : ℕ) (h : History LocalBridgePhase t) :
    (parentAllocation G).loan i t h = loan i := rfl

@[simp] theorem parent_firmDeposit (G : ℝ) (i : FirmType)
    (t : ℕ) (h : History LocalBridgePhase t) :
    (parentAllocation G).firmDeposit i t h = 0 := rfl

@[simp] theorem parent_firmFace (G : ℝ) (i : FirmType)
    (t : ℕ) (h : History LocalBridgePhase t) :
    (parentAllocation G).firmFace i t h = firmFace i := rfl

@[simp] theorem parent_firmWealth (G : ℝ) (i : FirmType)
    (t : ℕ) (h : History LocalBridgePhase t) :
    (parentAllocation G).firmWealth i t h = wealth i := by
  exact firmWealth_eq (primitives G)
    (stationary_parameters G).toStationaryRealParameters i

@[simp] theorem parent_workerConsumption (G : ℝ) (t : ℕ)
    (h : History LocalBridgePhase t) :
    (parentAllocation G).workerConsumption t h = workerConsumption := rfl

@[simp] theorem parent_workerLabor (G : ℝ) (t : ℕ)
    (h : History LocalBridgePhase t) :
    (parentAllocation G).workerLabor t h = aggregateLabor := by
  exact localPrefixAggregateLabor_eq (primitives G)
    (stationary_parameters G).toStationaryRealParameters

@[simp] theorem parent_inputPrice (G : ℝ) (t : ℕ)
    (h : History LocalBridgePhase t) :
    (parentAllocation G).inputPrice t h = 5 / 6 := rfl

@[simp] theorem parent_wage (G : ℝ) (t : ℕ)
    (h : History LocalBridgePhase t) :
    (parentAllocation G).wage t h = wage := rfl

@[simp] theorem parent_inflation (G : ℝ) (t : ℕ)
    (h : History LocalBridgePhase t) :
    (parentAllocation G).inflation t h = 1 := rfl

@[simp] theorem parent_capitalPrice (G : ℝ) (t : ℕ)
    (h : History LocalBridgePhase t) :
    (parentAllocation G).capitalPrice t h = capitalPrice := rfl

@[simp] theorem parent_loanRate (G : ℝ) (t : ℕ)
    (h : History LocalBridgePhase t) :
    (parentAllocation G).loanRate t h = ProposedStationaryBank.loanRate := rfl

@[simp] theorem parent_depositRate (G : ℝ) (t : ℕ)
    (h : History LocalBridgePhase t) :
    (parentAllocation G).depositRate t h = ProposedStationaryBank.depositRate := rfl

@[simp] theorem parent_reserveRate (G : ℝ) (t : ℕ)
    (h : History LocalBridgePhase t) :
    (parentAllocation G).reserveRate t h = ProposedStationaryBank.reserveRate := rfl

@[simp] theorem parent_facilityRate (G : ℝ) (t : ℕ)
    (h : History LocalBridgePhase t) :
    (parentAllocation G).facilityRate t h = facilityRate := rfl

@[simp] theorem parent_interbankRate (G : ℝ) (t : ℕ)
    (h : History LocalBridgePhase t) :
    (parentAllocation G).interbankRate t h =
      otcNegotiatedRate ProposedStationaryBank.reserveRate
        (ProposedStationaryBank.reserveRate + 1 / 50) (Real.log 2) (1 / 2) := rfl

@[simp] theorem parent_bankTightness (G : ℝ) (t : ℕ)
    (h : History LocalBridgePhase t) :
    (parentAllocation G).bankTightness t h = 1 / 2 := rfl

@[simp] theorem parent_bankEquity (G : ℝ) (t : ℕ)
    (h : History LocalBridgePhase t) :
    (parentAllocation G).bankEquity t h = bankEquity := by
  change bankEquity / 1 = bankEquity
  exact div_one bankEquity

@[simp] theorem parent_bankRetainedEquity (G : ℝ) (t : ℕ)
    (h : History LocalBridgePhase t) :
    (parentAllocation G).bankRetainedEquity t h = bankEquity := by
  change bankEquity / 1 = bankEquity
  exact div_one bankEquity

@[simp] theorem parent_bankDividend (G : ℝ) (t : ℕ)
    (h : History LocalBridgePhase t) :
    (parentAllocation G).bankDividend t h = 0 := rfl

@[simp] theorem parent_bankLoans (G : ℝ) (t : ℕ)
    (h : History LocalBridgePhase t) :
    (parentAllocation G).bankLoans t h = aggregateCredit := by
  exact reducedBankLoans_eq (primitives G) (stationary_parameters G).mass_eq

@[simp] theorem parent_bankDeposits (G : ℝ) (t : ℕ)
    (h : History LocalBridgePhase t) :
    (parentAllocation G).bankDeposits t h = bankDeposits := by
  exact reducedBankDeposits_eq (primitives G) 0 1 (binary_payment_law G)

@[simp] theorem parent_householdDeposits (G : ℝ) (t : ℕ)
    (h : History LocalBridgePhase t) :
    (parentAllocation G).householdDeposits t h = bankDeposits := by
  exact reducedBankDeposits_eq (primitives G) 0 1 (binary_payment_law G)

@[simp] theorem parent_householdBonds (G : ℝ) (t : ℕ)
    (h : History LocalBridgePhase t) :
    (parentAllocation G).householdBonds t h = G - reservesPre := rfl

@[simp] theorem parent_governmentBondRate (G : ℝ) (t : ℕ)
    (h : History LocalBridgePhase t) :
    (parentAllocation G).governmentBondRate t h = ProposedStationaryBank.depositRate := rfl

@[simp] theorem parent_reservesPrePayment (G : ℝ) (t : ℕ)
    (h : History LocalBridgePhase t) :
    (parentAllocation G).reservesPrePayment t h = reservesPre := rfl

@[simp] theorem parent_reservesPostPayment (G : ℝ) (t : ℕ)
    (h : History LocalBridgePhase t) :
    (parentAllocation G).reservesPostPayment t h = reservesPost := by
  exact parentSettlementCarrier_postReserves G t h

@[simp] theorem parent_facilityBorrowing (G : ℝ) (t : ℕ)
    (h : History LocalBridgePhase t) :
    (parentAllocation G).facilityBorrowing t h = facilityBorrowing := by
  exact parentSettlementCarrier_facility G t h

@[simp] theorem parent_interbankPosition (G : ℝ) (t : ℕ)
    (h : History LocalBridgePhase t) :
    (parentAllocation G).interbankPosition t h = 0 := by
  exact parentSettlementCarrier_interbank G t h

@[simp] theorem parent_bankNetIncome (G : ℝ) (t : ℕ)
    (h : History LocalBridgePhase t) :
    (parentAllocation G).bankNetIncome t h =
      (ProposedStationaryBank.loanRate - 1) * bankEquity := by
  change (primitives G).bankExit * (1 - (primitives G).bankSeedShare) *
    (bankEquity / (bankRenewalFactor (primitives G) * 1)) = _
  rw [(stationary_parameters G).bankExit_eq,
    (stationary_parameters G).bankSeedShare_eq,
    bankRenewalFactor_eq (primitives G) (stationary_parameters G)]
  unfold seedShare
  field_simp [ne_of_gt loanRate_pos] <;> ring

@[simp] theorem parent_grossReturn (G : ℝ) (t : ℕ)
    (h : History LocalBridgePhase t) :
    aggregateBankGrossReturn (primitives G) (parentAllocation G) t h =
      ProposedStationaryBank.loanRate * bankEquity := by
  exact parentSettlementCarrier_grossReturn G t h

@[simp] theorem parent_aggregateCapital (G : ℝ) (t : ℕ)
    (h : History LocalBridgePhase t) :
    (parentAllocation G).aggregateCapital t h = aggregateCapital := by
  change sourceAggregateCapital (primitives G) (inheritedState G)
    (parentSettlementCarrier G) t h = aggregateCapital
  cases t with
  | zero =>
      change localPrefixAggregateCapital (primitives G) capital = aggregateCapital
      exact localPrefixAggregateCapital_eq (primitives G)
        (stationary_parameters G).toStationaryRealParameters
  | succ n =>
      change localPrefixAggregateCapital (primitives G) capital = aggregateCapital
      exact localPrefixAggregateCapital_eq (primitives G)
        (stationary_parameters G).toStationaryRealParameters

@[simp] theorem parent_output (G : ℝ) (t : ℕ)
    (h : History LocalBridgePhase t) :
    (parentAllocation G).output t h = aggregateOutput := by
  change sourceAggregateOutput (primitives G) (inheritedState G)
    (parentSettlementCarrier G) t h = aggregateOutput
  cases t with
  | zero =>
      change localPrefixAggregateOutput (primitives G) dateData = aggregateOutput
      exact localPrefixAggregateOutput_eq (primitives G)
        (stationary_parameters G).toStationaryRealParameters
  | succ n =>
      change localPrefixAggregateOutput (primitives G) dateData = aggregateOutput
      exact localPrefixAggregateOutput_eq (primitives G)
        (stationary_parameters G).toStationaryRealParameters

@[simp] theorem parent_investment (G : ℝ) (t : ℕ)
    (h : History LocalBridgePhase t) :
    (parentAllocation G).investment t h = aggregateCapital / 40 := by
  change localPrefixAggregateCapital (primitives G) capital -
    (1 - (primitives G).depreciation) * (parentAllocation G).aggregateCapital t h = _
  rw [localPrefixAggregateCapital_eq (primitives G)
      (stationary_parameters G).toStationaryRealParameters,
    (stationary_parameters G).depreciation_eq, parent_aggregateCapital]
  ring

@[simp] theorem parent_capitalCreationCost (G : ℝ) (t : ℕ)
    (h : History LocalBridgePhase t) :
    (parentAllocation G).capitalCreationCost t h =
      (161 / 6400) * aggregateCapital := by
  change capitalCreationTechnology (primitives G)
    ((parentAllocation G).investment t h)
    ((parentAllocation G).aggregateCapital t h) = _
  rw [parent_investment, parent_aggregateCapital]
  unfold capitalCreationTechnology
  rw [(stationary_parameters G).capitalAdjustmentCost_eq]
  field_simp [ne_of_gt aggregates_pos.1] <;> ring

@[simp] theorem parent_priceAdjustmentResourceCost (G : ℝ) (t : ℕ)
    (h : History LocalBridgePhase t) :
    (parentAllocation G).priceAdjustmentResourceCost t h = 0 := by
  change (primitives G).priceAdjustmentCost / 2 *
    ((parentAllocation G).inflation t h - 1) ^ 2 * (parentAllocation G).output t h = 0
  rw [parent_inflation]
  ring

@[simp] theorem parent_retailerNetIncome (G : ℝ) (t : ℕ)
    (h : History LocalBridgePhase t) :
    (parentAllocation G).retailerNetIncome t h = aggregateOutput / 6 := by
  change (1 - (parentAllocation G).inputPrice t h) * (parentAllocation G).output t h -
    (parentAllocation G).priceAdjustmentResourceCost t h = aggregateOutput / 6
  rw [parent_inputPrice, parent_output, parent_priceAdjustmentResourceCost]
  ring

@[simp] theorem parent_capitalProducerNetIncome (G : ℝ) (t : ℕ)
    (h : History LocalBridgePhase t) :
    (parentAllocation G).capitalProducerNetIncome t h = aggregateCapital / 6400 := by
  change (parentAllocation G).capitalPrice t h * (parentAllocation G).investment t h -
    (parentAllocation G).capitalCreationCost t h = aggregateCapital / 6400
  rw [parent_capitalPrice, parent_investment, parent_capitalCreationCost]
  unfold capitalPrice
  ring

@[simp] theorem parent_tax (G : ℝ) (t : ℕ)
    (h : History LocalBridgePhase t) :
    (parentAllocation G).tax t h = fiscalTax G :=
  parentAllocation_tax_eq G t h

theorem parent_resourceClears (G : ℝ) :
    ResourceClears (primitives G) (parentAllocation G) := by
  intro t h _hadmissible
  simp only [parent_workerConsumption, parent_firmConsumption,
    parent_capitalCreationCost, parent_priceAdjustmentResourceCost,
    parent_output, (stationary_parameters G).mass_eq]
  rw [sum_firmType_eq_H_add_L]
  unfold workerConsumption average
  ring

theorem parent_bankBalance (G : ℝ) :
    BankBalance (primitives G) (parentAllocation G) := by
  intro t h _hadmissible
  simpa only [parent_bankLoans, parent_reservesPrePayment,
    parent_bankDeposits, parent_bankRetainedEquity, add_comm] using bank_balance

theorem parent_creditClears (G : ℝ) :
    CreditClears (primitives G) (parentAllocation G) := by
  intro t h _hadmissible
  simp only [parent_bankLoans, parent_loan, (stationary_parameters G).mass_eq]
  rw [sum_firmType_eq_H_add_L]
  unfold aggregateCredit average
  ring

theorem parent_depositsClear (G : ℝ) :
    DepositsClear (primitives G) (parentAllocation G) := by
  intro t h _hadmissible
  simp only [parent_bankDeposits, parent_householdDeposits,
    parent_firmDeposit, mul_zero, Finset.sum_const_zero, add_zero]

theorem parent_laborClears (G : ℝ) :
    LaborClears (primitives G) (parentAllocation G) := by
  intro t h _hadmissible
  simp only [parent_workerLabor, parent_labor, (stationary_parameters G).mass_eq]
  rw [sum_firmType_eq_H_add_L]
  unfold aggregateLabor average
  ring

theorem parent_settlementClears (G : ℝ) :
    SettlementClears (primitives G) (parentAllocation G) := by
  intro t h _hadmissible
  refine ⟨parent_interbankPosition G t h, ?_, ?_⟩
  · rw [parent_facilityBorrowing]
    exact facilityBorrowing_pos.le
  · rw [parent_reservesPostPayment, parent_reservesPrePayment,
      parent_interbankPosition, parent_facilityBorrowing]
    unfold reservesPost
    ring

end ProposedStationaryLiteralAccounts
end Ventura26LiquidityAllocation
