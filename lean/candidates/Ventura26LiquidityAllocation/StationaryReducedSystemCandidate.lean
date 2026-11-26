import Ventura26LiquidityAllocation.StationaryProductionBridgeCandidate

/-!
# Renovacion y reglas del padre: PROPUESTA SIN COMPILAR

Proyecto: alejandroventuraventurameza-tech/ai-project.
Rama: work/chat-continuity.
Commit: 16e24fe828a5a0002ef13bb82bae9e295f190f86.
Base AppliedModelingLib: 194edcc95df74806a39b961d10dedddc6e730cce.
Lean previsto: leanprover/lean4:v4.30.0-rc2.
Mathlib fijado: 5450b53e5ddc75d46418fabb605edbf36bd0beb6.
Destino propuesto:
papers/Ventura26LiquidityAllocation/StationaryReducedSystemCandidate.lean.

Depende de los tres candidatos previos, todos SIN COMPILAR.
SHA256 de StationaryProductionBridgeCandidate.lean utilizado:
a1aad1b5775e13b0bbe642fb955828e0edbc5f887dc3c3a5accb60f436249488

Fuente: EconomicModel.lean, bankRenewalFactor y
localReducedRemainingResidual, filas 0, 6 y 7; paper/paper.tex,
testigo estacionario con captacion holgada de sec:v0m_source_25.

Argumento matematico anterior al ensamblaje:
  100/99 < R < 25/24 implica 24/25 < 1/R < 99/100.
  eta=1/10 y psi=10/R-9 dan 3/5<psi<9/10 y
  a_B=1-eta+eta*psi=1/R.
  E>0 y Pi=1 hacen que E-a_B*R*E=0 equivalga a a_B*R=1.
  RRbar=RR, Mbar=Mpre y Yref=Y>0, con innovaciones cero,
  anulan las reglas: log(1)=0 y p*log(x)+(1-p)*log(x)=log(x).
No se necesita restringir p ni los coeficientes de respuesta para esta
identidad estacionaria; tampoco se infiere estabilidad dinamica.

StationaryParameters contiene unicamente igualdades de primitivas.
La ley de pagos binaria se mantiene explicita. No se recibe ninguna
ecuacion de equilibrio ni residual nulo como hipotesis.

ALCANCE: 11 filas comunes y 3 ecuaciones por cada firma (17 igualdades)
sobre dateData; identificacion de la promesa comun; transporte a la
secuencia recurrente constante bajo las entradas recurrentes explicitas.
Esto no construye un Primitives completo ni un InheritedState, no prueba
LocalReducedPrefixEquationsHold para un prefijo y no reconstruye una
Allocation con optimalidad, cierre fiscal, terminalidad o respuestas a
intervenciones. Las ramas S y B permanecen separadas.

No se modifica el checkpoint ni el repositorio remoto. Revision estatica
no significa elaboracion, verificacion por el kernel, inspeccion de
axiomas ni aprobacion de la auditoria semantica de AppliedModelingLib.
-/

namespace Ventura26LiquidityAllocation
namespace ProposedStationaryReducedSystem

open ProposedStationaryRealScale
open ProposedStationaryProductionBridge

variable {S : Type*} [Fintype S]

noncomputable def seedShare : ℝ :=
  10 / ProposedStationaryBank.loanRate - 9

theorem inverse_loanRate_bounds :
    (24 / 25 : ℝ) < 1 / ProposedStationaryBank.loanRate ∧
      1 / ProposedStationaryBank.loanRate < 99 / 100 := by
  rcases ProposedStationaryBank.bank_margins_and_pricing with
    ⟨_hxi0, _hxiupper, _hrlo, _hrhi, _hpricing, hRlo, hRhi⟩
  have hRpos := loanRate_pos
  norm_num [ProposedStationaryBank.depositRate] at hRlo
  constructor
  · apply (lt_div_iff₀ hRpos).2
    nlinarith
  · apply (div_lt_iff₀ hRpos).2
    nlinarith

theorem seedShare_bounds :
    (3 / 5 : ℝ) < seedShare ∧ seedShare < 9 / 10 := by
  rcases inverse_loanRate_bounds with ⟨hlo, hhi⟩
  have hid : seedShare =
      10 * (1 / ProposedStationaryBank.loanRate) - 9 := by
    unfold seedShare
    ring
  rw [hid]
  constructor <;> linarith

/-- Dominios de las dos primitivas bancarias, derivados de las cotas de R. -/
theorem bank_entry_parameters_admissible :
    (0 < (1 / 10 : ℝ) ∧ (1 / 10 : ℝ) < 1) ∧
      (0 < seedShare ∧ seedShare < 1) := by
  rcases seedShare_bounds with ⟨hlo, hhi⟩
  constructor
  · norm_num
  · constructor <;> linarith

theorem renewalFactor_identity :
    1 - (1 / 10 : ℝ) + (1 / 10 : ℝ) * seedShare =
      1 / ProposedStationaryBank.loanRate := by
  unfold seedShare
  ring

/-- Un solo P para los bloques reales, bancarios y monetarios. Son
igualdades de parametros; la existencia de un P completo queda pendiente. -/
structure StationaryParameters (P : Primitives S) : Prop
    extends StationaryRealParameters P where
  bankExit_eq : P.bankExit = 1 / 10
  bankSeedShare_eq : P.bankSeedShare = seedShare
  matchingIntensity_eq : P.matchingIntensity = Real.log 2
  reserveRateSteady_eq : P.reserveRateSteady = ProposedStationaryBank.reserveRate
  reserveQuantitySteady_eq : P.reserveQuantitySteady = reservesPre
  outputReference_eq : P.outputReference = aggregateOutput

theorem bankRenewalFactor_eq
    (P : Primitives S) (H : StationaryParameters P) :
    bankRenewalFactor P = 1 / ProposedStationaryBank.loanRate := by
  unfold bankRenewalFactor
  rw [H.bankExit_eq, H.bankSeedShare_eq]
  exact renewalFactor_identity

/-- El factor total de renovacion tambien tiene un margen estricto;
no se identifica con la fraccion retenida por un banco que continua. -/
theorem bankRenewalFactor_bounds
    (P : Primitives S) (H : StationaryParameters P) :
    (24 / 25 : ℝ) < bankRenewalFactor P ∧ bankRenewalFactor P < 99 / 100 := by
  rw [bankRenewalFactor_eq P H]
  exact inverse_loanRate_bounds

/-- Las referencias del logaritmo son positivas. Esto no es el dominio
monetario completo, que tambien habla de deuda publica y estado heredado. -/
theorem monetary_references_pos
    (P : Primitives S) (H : StationaryParameters P) :
    0 < P.reserveRateSteady ∧ 0 < P.reserveQuantitySteady ∧
      0 < P.outputReference := by
  rw [H.reserveRateSteady_eq, H.reserveQuantitySteady_eq, H.outputReference_eq]
  have hRR := ProposedStationaryBank.reserveRate_spec.1
  exact ⟨by linarith, bank_scale_pos.2.2, aggregates_pos.2.1⟩

theorem bankRenewal_row_eq_zero
    (P : Primitives S) (H : StationaryParameters P) :
    localReducedRemainingResidual P dateData 0 = 0 := by
  change bankEquity - bankRenewalFactor P * ProposedStationaryBank.loanRate *
    bankEquity / 1 = 0
  rw [bankRenewalFactor_eq P H]
  field_simp [ne_of_gt loanRate_pos] <;> ring

theorem reserveRateRule_row_eq_zero
    (P : Primitives S) (H : StationaryParameters P) :
    localReducedRemainingResidual P dateData 6 = 0 := by
  change Real.log ProposedStationaryBank.reserveRate -
    (P.reserveRatePersistence * Real.log ProposedStationaryBank.reserveRate +
      (1 - P.reserveRatePersistence) *
        (Real.log P.reserveRateSteady + P.inflationResponse * Real.log 1 +
          P.outputResponse *
            Real.log (localPrefixAggregateOutput P dateData / P.outputReference)) +
      0) = 0
  rw [localPrefixAggregateOutput_eq P H.toStationaryRealParameters,
    H.reserveRateSteady_eq, H.outputReference_eq]
  simp only [div_self (ne_of_gt aggregates_pos.2.1), Real.log_one,
    mul_zero, add_zero]
  ring

theorem reserveQuantityRule_row_eq_zero
    (P : Primitives S) (H : StationaryParameters P) :
    localReducedRemainingResidual P dateData 7 = 0 := by
  change Real.log reservesPre -
    (P.reserveQuantityPersistence * Real.log reservesPre +
      (1 - P.reserveQuantityPersistence) * Real.log P.reserveQuantitySteady +
      0) = 0
  rw [H.reserveQuantitySteady_eq]
  ring

theorem renewal_and_policy_rows
    (P : Primitives S) (H : StationaryParameters P) :
    localReducedRemainingResidual P dateData 0 = 0 ∧
      localReducedRemainingResidual P dateData 6 = 0 ∧
      localReducedRemainingResidual P dateData 7 = 0 :=
  ⟨bankRenewal_row_eq_zero P H, reserveRateRule_row_eq_zero P H,
    reserveQuantityRule_row_eq_zero P H⟩

/-- Se reutilizan los bloques previos; no se vuelven a suponer sus filas. -/
theorem all_remaining_rows
    (P : Primitives S) (H : StationaryParameters P)
    (paymentMinus paymentPlus : BankPayment)
    (hbinary : BinarySymmetricPaymentLaw P paymentMinus paymentPlus (1 / 5)) :
    ∀ row : Fin 11, localReducedRemainingResidual P dateData row = 0 := by
  rcases real_remaining_rows P H.toStationaryRealParameters with
    ⟨h1, h2, h3, h4, h5⟩
  rcases ProposedStationaryBank.localPrefix_bank_pricing_rows
      P dateData paymentMinus paymentPlus hbinary H.matchingIntensity_eq
      rfl rfl rfl rfl rfl rfl with ⟨h8, h9⟩
  have h0 := bankRenewal_row_eq_zero P H
  have h6 := reserveRateRule_row_eq_zero P H
  have h7 := reserveQuantityRule_row_eq_zero P H
  have h10 := reduced_bank_balance_row P paymentMinus paymentPlus hbinary H.mass_eq
  intro row
  fin_cases row
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4
  · exact h5
  · exact h6
  · exact h7
  · exact h8
  · exact h9
  · exact h10

/-- Las 17 igualdades de una fecha del padre vinculante. No se denomina
LocalReducedPrefixEquationsHold, que exige otro portador y 33 etiquetas. -/
theorem stationary_reduced_system
    (P : Primitives S) (H : StationaryParameters P)
    (paymentMinus paymentPlus : BankPayment)
    (hbinary : BinarySymmetricPaymentLaw P paymentMinus paymentPlus (1 / 5)) :
    (∀ row : Fin 11, localReducedRemainingResidual P dateData row = 0) ∧
      (∀ i, localReducedFirmBudgetResidual P dateData i = 0 ∧
        localReducedFirmCapitalEulerResidual .binding P dateData i = 0 ∧
        localReducedFirmRegimeResidual .binding P dateData i = 0) := by
  exact ⟨all_remaining_rows P H paymentMinus paymentPlus hbinary,
    binding_firm_rows P H.toStationaryRealParameters⟩

/-- La coordenada de promesa comun tiene el significado economico usado
por los portadores; no representa por si sola el prefijo de dos fechas. -/
theorem commonPledge_stationary_identity
    (P : Primitives S) (H : StationaryParameters P) :
    stateSix.commonPledgeValue =
      (1 - P.depreciation) * controls.inflation * controls.capitalPrice := by
  change liquidationValue = (1 - P.depreciation) * 1 * capitalPrice
  rw [H.depreciation_eq]
  unfold liquidationValue
  ring

/-- Entradas del constructor recurrente. No se imponen residuales como
premisas, ni se identifica una historia inicial S con el padre vinculante. -/
structure StationaryRecurrentInputs (P : Primitives LocalBridgePhase) : Prop where
  productivity_eq : P.aggregateProductivity .recurrent = 1
  rateInnovation_eq : P.reserveRateInnovation .recurrent = 0
  quantityInnovation_eq : P.reserveQuantityInnovation .recurrent = 0
  requirement_eq : ∀ n,
    P.reserveRequirementPath (n + 2) (localBridgeHistory (n + 2)) = 1 / 10
  width_eq : ∀ n,
    P.corridorWidthPath (n + 2) (localBridgeHistory (n + 2)) = 1 / 50

/-- Transporte a la secuencia constante dentro del constructor conservado.
No prueba una continuacion exacta desde prefijos intervenidos S o B. -/
theorem constant_recurrent_reduced_system
    (P : Primitives LocalBridgePhase) (H : StationaryParameters P)
    (J : StationaryRecurrentInputs P)
    (paymentMinus paymentPlus : BankPayment)
    (hbinary : BinarySymmetricPaymentLaw P paymentMinus paymentPlus (1 / 5)) :
    ∀ n,
      (∀ row : Fin 11,
        localReducedRemainingResidual P
          (localRecurrentDateData P (fun _ ↦ stateSix) (fun _ ↦ controls) n) row = 0) ∧
      (∀ i,
        localReducedFirmBudgetResidual P
          (localRecurrentDateData P (fun _ ↦ stateSix) (fun _ ↦ controls) n) i = 0 ∧
        localReducedFirmCapitalEulerResidual .binding P
          (localRecurrentDateData P (fun _ ↦ stateSix) (fun _ ↦ controls) n) i = 0 ∧
        localReducedFirmRegimeResidual .binding P
          (localRecurrentDateData P (fun _ ↦ stateSix) (fun _ ↦ controls) n) i = 0) := by
  intro n
  rw [recurrent_dateData_eq P H.pledgeability_eq J.productivity_eq
    J.rateInnovation_eq J.quantityInnovation_eq n (J.requirement_eq n) (J.width_eq n)]
  exact stationary_reduced_system P H paymentMinus paymentPlus hbinary

end ProposedStationaryReducedSystem
end Ventura26LiquidityAllocation
