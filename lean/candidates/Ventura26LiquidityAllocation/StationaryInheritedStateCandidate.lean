import Ventura26LiquidityAllocation.StationaryPrimitivesCandidate

/-!
# Estado heredado y cuentas del padre: PROPUESTA SIN COMPILAR

Proyecto: alejandroventuraventurameza-tech/ai-project.
Rama: work/chat-continuity.
Commit: 16e24fe828a5a0002ef13bb82bae9e295f190f86.
Base AppliedModelingLib: 194edcc95df74806a39b961d10dedddc6e730cce.
Lean previsto: leanprover/lean4:v4.30.0-rc2.
Mathlib fijado: 5450b53e5ddc75d46418fabb605edbf36bd0beb6.
Destino propuesto:
papers/Ventura26LiquidityAllocation/StationaryInheritedStateCandidate.lean.
SHA256 de StationaryPrimitivesCandidate.lean utilizado:
6b70756799e3237bdf51f5744a9d6baa56873cf6872780f7dff21c3a35bb0e74

Todos los modulos propuestos de esta cadena estan SIN COMPILAR.
La lectura y revision estatica no acreditan elaboracion, kernel,
inspeccion de axiomas ni aprobacion semantica de AppliedModelingLib.
No se ha modificado el checkpoint, el import raiz ni el repositorio remoto.

Argumento matematico:
  W=(RD/RR-1/10)*D/30>0; sMinus=-4W y sPlus=8W.
  El matching literal produce facilidad 2W y 0, con promedio W.
  El interbancario esperado es cero y Mpost=Mpre+W.
  La FOC de depositos y el balance dan grossReturn=RL*E.
  Con a_B=1/RL, la promesa heredada bancaria es E.
  Se construyen las doce entradas de InheritedState, conservando
  householdBonds=G-Mpre y distinguiendo Mpre de Mpost.
  La identidad nominal se prueba por sustitucion; G se cancela.
  G>=Mpre garantiza bonos no negativos y el dominio monetario;
  G>Mpre es necesario para la interioridad estricta de esos bonos.
  El impuesto residual es
    T=(RD-1)*(G-Mpre)+(RR-1)*Mpre-(1/50)*W.

Se utiliza el constructor de liquidacion conservado solo despues de
identificar sus importes desde el plan de matching. Se reemplaza de forma
explicita su dual L de fecha cero por el dual vinculante del padre.
El estado se define sin depender de un Allocation; posteriormente se
prueba su igualdad con sourcePredecessorStateAt del portador construido.
Las cuentas reales y fiscales se completan mediante las funciones fuente.

ALCANCE: primitivas explicitas, estado heredado, consistencia nominal,
dominio monetario, liquidacion agregada y cierre fiscal contable.
Construir un termino Allocation y FiscalClosure no acredita factibilidad
privada completa, optimalidad, distribucion bancaria estacionaria,
terminalidad, el prefijo de 33 ecuaciones ni su continuacion intervenida.
El padre vinculante no se identifica con el impacto S. Se conservan S y B.
-/

namespace Ventura26LiquidityAllocation
namespace ProposedStationaryInheritedState

open ProposedStationaryRealScale
open ProposedStationaryProductionBridge
open ProposedStationaryReducedSystem

noncomputable def facilityBorrowing : ℝ :=
  (ProposedStationaryBank.depositRate / ProposedStationaryBank.reserveRate -
    1 / 10) * bankDeposits / 30

noncomputable def reservesPost : ℝ := reservesPre + facilityBorrowing

noncomputable def facilityRate : ℝ :=
  ProposedStationaryBank.reserveRate + 1 / 50

theorem facilityBorrowing_pos : 0 < facilityBorrowing := by
  have hxi := ProposedStationaryBank.bank_margins_and_pricing.1
  have hgap : 0 < ProposedStationaryBank.depositRate /
      ProposedStationaryBank.reserveRate - 1 / 10 := by
    linarith
  exact div_pos (mul_pos hgap bank_scale_pos.2.1) (by norm_num)

theorem reservesPost_pos : 0 < reservesPost :=
  add_pos bank_scale_pos.2.2 facilityBorrowing_pos

theorem facilityRate_pos : 0 < facilityRate := by
  have hreserve := ProposedStationaryBank.reserveRate_spec.1
  unfold facilityRate
  linarith

theorem settlementSurplus_minus :
    bankSettlementSurplus reservesPre (1 / 10)
      (ProposedStationaryBank.depositRate / ProposedStationaryBank.reserveRate)
      bankDeposits (-(1 / 5)) = -4 * facilityBorrowing := by
  dsimp only [bankSettlementSurplus, reservesPre, facilityBorrowing,
    bankDeposits, ProposedStationaryBank.reserveDepositRatio]
  ring

theorem settlementSurplus_plus :
    bankSettlementSurplus reservesPre (1 / 10)
      (ProposedStationaryBank.depositRate / ProposedStationaryBank.reserveRate)
      bankDeposits (1 / 5) = 8 * facilityBorrowing := by
  dsimp only [bankSettlementSurplus, reservesPre, facilityBorrowing,
    bankDeposits, ProposedStationaryBank.reserveDepositRatio]
  ring

/-- El promedio se calcula desde bankFacilityBorrowingAt; no se usa el
placeholder facilityBorrowing=0 del constructor privado. -/
theorem expectedFacility_eq
    (P : Primitives LocalBridgePhase) (H : StationaryParameters P)
    (paymentMinus paymentPlus : BankPayment)
    (hbinary : BinarySymmetricPaymentLaw P paymentMinus paymentPlus (1 / 5))
    (t : ℕ) (h : History LocalBridgePhase t)
    (hrequirement : P.reserveRequirementPath t h = 1 / 10) :
    localSlackExpectedFacility P (fun _ ↦ dateData) t h =
      facilityBorrowing := by
  have hlawParts := hbinary
  rcases hlawParts with ⟨_hne, _hsize, _hsupport, _hprobMinus, _hprobPlus,
    hshockMinus, hshockPlus⟩
  have hdeposits := reducedBankDeposits_eq P paymentMinus paymentPlus hbinary
  have hminusFraction :
      otcDeficitMatchFraction P.matchingIntensity (1 / 2) = 1 / 2 := by
    rw [H.matchingIntensity_eq]
    exact (ProposedStationaryBank.matching_specialization
      ProposedStationaryBank.reserveRate).2.1
  have hW := facilityBorrowing_pos
  have hminus : -4 * facilityBorrowing < 0 := by nlinarith
  have hplus : ¬8 * facilityBorrowing < 0 := by nlinarith
  change finiteSupportExpectation P.paymentSupport P.paymentProbability
    (fun omega ↦
      let surplus := bankSettlementSurplus reservesPre
        (P.reserveRequirementPath t h)
        (ProposedStationaryBank.depositRate / ProposedStationaryBank.reserveRate)
        (localPrefixReducedBankDeposits P dateData) (P.paymentShock omega)
      if surplus < 0 then
        -(1 - otcDeficitMatchFraction P.matchingIntensity (1 / 2)) * surplus
      else 0) = facilityBorrowing
  rw [hdeposits,
    finiteSupportExpectation_eq_average_of_binarySymmetric
      P paymentMinus paymentPlus (1 / 5) hbinary]
  simp only [hrequirement, hshockMinus, hshockPlus,
    settlementSurplus_minus, settlementSurplus_plus,
    if_pos hminus, if_neg hplus, hminusFraction]
  ring

theorem expectedPostReserves_eq
    (P : Primitives LocalBridgePhase) (H : StationaryParameters P)
    (paymentMinus paymentPlus : BankPayment)
    (hbinary : BinarySymmetricPaymentLaw P paymentMinus paymentPlus (1 / 5))
    (t : ℕ) (h : History LocalBridgePhase t)
    (hrequirement : P.reserveRequirementPath t h = 1 / 10) :
    localSlackExpectedPostReserves P (fun _ ↦ dateData) t h =
      reservesPost := by
  rw [Ventura26LiquidityAllocation.localSlackExpectedPostReserves_eq,
    stationary_expectedInterbank_eq_zero
      P paymentMinus paymentPlus hbinary t h hrequirement,
    expectedFacility_eq
      P H paymentMinus paymentPlus hbinary t h hrequirement]
  change reservesPre + 0 + facilityBorrowing = reservesPost
  unfold reservesPost
  ring

open ProposedStationaryPrimitives
open scoped BigOperators

theorem reservesPre_eq_ratio_deposits :
    reservesPre = ProposedStationaryBank.reserveDepositRatio * bankDeposits := by
  unfold reservesPre bankDeposits
  ring

/-- El precio del deposito y las pendientes OTC financian exactamente
el coste de la facilidad. Es una identidad, no optimalidad de cartera. -/
theorem deposit_funding_coefficient_eq_zero :
    ProposedStationaryBank.loanRate - ProposedStationaryBank.depositRate -
      (ProposedStationaryBank.loanRate - ProposedStationaryBank.reserveRate) *
        ProposedStationaryBank.reserveDepositRatio -
      (1 / 50 : ℝ) *
        (ProposedStationaryBank.depositRate / ProposedStationaryBank.reserveRate -
          1 / 10) / 30 = 0 := by
  rcases ProposedStationaryBank.bank_margins_and_pricing with
    ⟨_hxi0, _hxi1, _hr0, _hr1, hpricing, _hR0, _hR1⟩
  calc
    _ = ProposedStationaryBank.depositPricingResidual := by
      unfold ProposedStationaryBank.loanRate
        ProposedStationaryBank.reserveDepositRatio
        ProposedStationaryBank.depositPricingResidual
        ProposedStationaryBank.meanSlope ProposedStationaryBank.slopeGap
      ring
    _ = 0 := hpricing

theorem scalar_bank_gross_return :
    ProposedStationaryBank.loanRate * aggregateCredit +
      ProposedStationaryBank.reserveRate * reservesPost -
      ProposedStationaryBank.depositRate * bankDeposits -
      facilityRate * facilityBorrowing =
        ProposedStationaryBank.loanRate * bankEquity := by
  have hB : aggregateCredit = bankEquity + bankDeposits - reservesPre := by
    have hbalance := bank_balance
    linarith
  apply sub_eq_zero.mp
  calc
    _ = bankDeposits *
        (ProposedStationaryBank.loanRate - ProposedStationaryBank.depositRate -
          (ProposedStationaryBank.loanRate - ProposedStationaryBank.reserveRate) *
            ProposedStationaryBank.reserveDepositRatio -
          (1 / 50 : ℝ) *
            (ProposedStationaryBank.depositRate / ProposedStationaryBank.reserveRate -
              1 / 10) / 30) := by
      unfold reservesPost facilityRate facilityBorrowing
      rw [hB, reservesPre_eq_ratio_deposits]
      ring
    _ = 0 := by rw [deposit_funding_coefficient_eq_zero, mul_zero]

theorem aggregate_firmFace_eq (G : ℝ) :
    (∑ i, (primitives G).mass i * firmFace i) =
      ProposedStationaryBank.loanRate * aggregateCredit := by
  rw [sum_firmType_eq_H_add_L]
  simp only [(stationary_parameters G).mass_eq]
  unfold aggregateCredit average loan
  field_simp [ne_of_gt loanRate_pos] <;> ring

/-- Las doce posiciones heredadas. G permanece simbolico. Las reservas
posteriores incluyen la facilidad positiva; los bonos domesticos son G-Mpre. -/
noncomputable def inheritedState (G : ℝ) : InheritedState where
  capital := capital
  firmFace := firmFace
  bankFace := bankEquity
  householdDeposits := bankDeposits
  householdBonds := G - reservesPre
  depositRateLag := ProposedStationaryBank.depositRate
  governmentBondRateLag := ProposedStationaryBank.depositRate
  reserveRateLag := ProposedStationaryBank.reserveRate
  reservesPreLag := reservesPre
  reservesLag := reservesPost
  facilityRateLag := facilityRate
  facilityBorrowingLag := facilityBorrowing

theorem inherited_financial_positions
    (G : ℝ) (hG : reservesPre ≤ G) :
    0 ≤ (inheritedState G).householdBonds ∧
      0 < (inheritedState G).householdDeposits ∧
      0 < (inheritedState G).facilityBorrowingLag ∧
      (inheritedState G).reservesLag =
        (inheritedState G).reservesPreLag + (inheritedState G).facilityBorrowingLag ∧
      (inheritedState G).householdBonds + (inheritedState G).reservesPreLag = G := by
  change 0 ≤ G - reservesPre ∧ 0 < bankDeposits ∧ 0 < facilityBorrowing ∧
    reservesPost = reservesPre + facilityBorrowing ∧ G - reservesPre + reservesPre = G
  exact ⟨sub_nonneg.mpr hG, bank_scale_pos.2.1, facilityBorrowing_pos, rfl, by ring⟩

theorem inherited_householdBonds_pos_iff (G : ℝ) :
    0 < (inheritedState G).householdBonds ↔ reservesPre < G := by
  change 0 < G - reservesPre ↔ reservesPre < G
  exact sub_pos

theorem inherited_postReserves_gt_preReserves (G : ℝ) :
    (inheritedState G).reservesPreLag < (inheritedState G).reservesLag := by
  change reservesPre < reservesPre + facilityBorrowing
  exact lt_add_of_pos_right reservesPre facilityBorrowing_pos

theorem inherited_state_matches (G : ℝ) :
    LocalContinuationInheritedStateMatches (primitives G) stateSix
      (inheritedState G) := by
  have hcapital : localPrefixStateSixCapital stateSix = capital := by
    funext i
    cases i <;> rfl
  have hfaces := stateSix_faces (primitives G) (stationary_parameters G).pledgeability_eq
  exact ⟨hcapital.symm, hfaces.symm, rfl, rfl, rfl⟩

theorem inherited_nominalFaceConsistency (G : ℝ) :
    InheritedNominalFaceConsistency (primitives G) (inheritedState G) := by
  have hfactor := bankRenewalFactor_eq (primitives G) (stationary_parameters G)
  have hfactorBounds := bankRenewalFactor_bounds (primitives G) (stationary_parameters G)
  constructor
  · linarith [hfactorBounds.1]
  · change ProposedStationaryBank.depositRate * bankDeposits +
        ProposedStationaryBank.depositRate * (G - reservesPre) =
      (∑ i, (primitives G).mass i * firmFace i) +
        (ProposedStationaryBank.depositRate * (G - reservesPre) +
          ProposedStationaryBank.reserveRate * reservesPost -
          facilityRate * facilityBorrowing) -
        bankEquity / bankRenewalFactor (primitives G)
    rw [aggregate_firmFace_eq G, hfactor]
    have hquotient : bankEquity / (1 / ProposedStationaryBank.loanRate) =
        ProposedStationaryBank.loanRate * bankEquity := by
      field_simp [ne_of_gt loanRate_pos] <;> ring
    rw [hquotient]
    have hreturn := scalar_bank_gross_return
    linarith

theorem inherited_monetary_domain
    (G : ℝ) (hG : reservesPre ≤ G) :
    MonetaryPolicyPrimitiveDomain (primitives G) (inheritedState G) := by
  have hRR : 0 < ProposedStationaryBank.reserveRate := by
    have h := ProposedStationaryBank.reserveRate_spec.1
    linarith
  have hM := bank_scale_pos.2.2
  have hGpos : 0 < G := lt_of_lt_of_le hM hG
  change 0 < ProposedStationaryBank.reserveRate ∧ 0 < reservesPre ∧
    0 < aggregateOutput ∧ 0 < G ∧ 0 < ProposedStationaryBank.reserveRate ∧
    0 < reservesPre
  exact ⟨hRR, hM, aggregates_pos.2.1, hGpos, hRR, hM⟩

/-- Portador con liquidacion literal y dual empresarial vinculante en
ambos tipos y todas las fechas. Sus cuentas reales/fiscales se completan
por separado. Un termino de tipo Allocation no acredita equilibrio. -/
noncomputable def parentSettlementCarrier (G : ℝ) : Allocation LocalBridgePhase :=
  { localSlackSettlementAllocation (primitives G) (fun _ ↦ dateData) with
    collateralDual := fun _i _t _h ↦ collateralMultiplier }

theorem parentSettlementCarrier_interbank (G : ℝ) (t : ℕ)
    (h : History LocalBridgePhase t) :
    (parentSettlementCarrier G).interbankPosition t h = 0 := by
  exact stationary_expectedInterbank_eq_zero
    (primitives G) 0 1 (binary_payment_law G) t h rfl

theorem parentSettlementCarrier_facility (G : ℝ) (t : ℕ)
    (h : History LocalBridgePhase t) :
    (parentSettlementCarrier G).facilityBorrowing t h = facilityBorrowing := by
  exact expectedFacility_eq (primitives G) (stationary_parameters G)
    0 1 (binary_payment_law G) t h rfl

theorem parentSettlementCarrier_postReserves (G : ℝ) (t : ℕ)
    (h : History LocalBridgePhase t) :
    (parentSettlementCarrier G).reservesPostPayment t h = reservesPost := by
  exact expectedPostReserves_eq (primitives G) (stationary_parameters G)
    0 1 (binary_payment_law G) t h rfl

theorem parentSettlementCarrier_settlementClears (G : ℝ) :
    SettlementClears (primitives G) (parentSettlementCarrier G) := by
  intro t h _hadmissible
  refine ⟨parentSettlementCarrier_interbank G t h, ?_, ?_⟩
  · rw [parentSettlementCarrier_facility]
    exact facilityBorrowing_pos.le
  · rw [parentSettlementCarrier_postReserves, parentSettlementCarrier_interbank,
      parentSettlementCarrier_facility]
    change reservesPost = reservesPre + 0 + facilityBorrowing
    unfold reservesPost
    ring

theorem parentSettlementCarrier_grossReturn (G : ℝ) (t : ℕ)
    (h : History LocalBridgePhase t) :
    aggregateBankGrossReturn (primitives G) (parentSettlementCarrier G) t h =
      ProposedStationaryBank.loanRate * bankEquity := by
  have hB := reducedBankLoans_eq (primitives G) (stationary_parameters G).mass_eq
  have hD := reducedBankDeposits_eq (primitives G) 0 1 (binary_payment_law G)
  change ProposedStationaryBank.loanRate *
      localPrefixReducedBankLoans (primitives G) dateData +
    ProposedStationaryBank.reserveRate * (parentSettlementCarrier G).reservesPostPayment t h -
    ProposedStationaryBank.depositRate * localPrefixReducedBankDeposits (primitives G) dateData -
    (parentSettlementCarrier G).interbankRate t h *
      (parentSettlementCarrier G).interbankPosition t h -
    facilityRate * (parentSettlementCarrier G).facilityBorrowing t h = _
  rw [hB, hD, parentSettlementCarrier_postReserves,
    parentSettlementCarrier_interbank, parentSettlementCarrier_facility]
  simpa only [mul_zero, sub_zero] using scalar_bank_gross_return

/-- El estado explicito coincide con el constructor de predecesor
conservado. La igualdad se deriva despues de construir los flujos. -/
theorem sourcePredecessorStateAt_eq (G : ℝ) (t : ℕ)
    (h : History LocalBridgePhase t) :
    sourcePredecessorStateAt (primitives G) (parentSettlementCarrier G) t h =
      inheritedState G := by
  have hD := reducedBankDeposits_eq (primitives G) 0 1 (binary_payment_law G)
  have hface : bankRenewalFactor (primitives G) *
      aggregateBankGrossReturn (primitives G) (parentSettlementCarrier G) t h =
        bankEquity := by
    rw [parentSettlementCarrier_grossReturn,
      bankRenewalFactor_eq (primitives G) (stationary_parameters G)]
    field_simp [ne_of_gt loanRate_pos] <;> ring
  change
    ({ capital := capital, firmFace := firmFace,
        bankFace := bankRenewalFactor (primitives G) *
          aggregateBankGrossReturn (primitives G) (parentSettlementCarrier G) t h,
        householdDeposits := localPrefixReducedBankDeposits (primitives G) dateData,
        householdBonds := G - reservesPre,
        depositRateLag := ProposedStationaryBank.depositRate,
        governmentBondRateLag := ProposedStationaryBank.depositRate,
        reserveRateLag := ProposedStationaryBank.reserveRate,
        reservesPreLag := reservesPre,
        reservesLag := (parentSettlementCarrier G).reservesPostPayment t h,
        facilityRateLag := facilityRate,
        facilityBorrowingLag := (parentSettlementCarrier G).facilityBorrowing t h }
      : InheritedState) = inheritedState G
  rw [hface, hD, parentSettlementCarrier_postReserves,
    parentSettlementCarrier_facility] <;> rfl

noncomputable def fiscalTax (G : ℝ) : ℝ :=
  (ProposedStationaryBank.depositRate - 1) * (G - reservesPre) +
    (ProposedStationaryBank.reserveRate - 1) * reservesPre -
    (1 / 50 : ℝ) * facilityBorrowing

/-- El impuesto es el residual fiscal de la fuente; su signo no se impone. -/
theorem fiscal_balance (G : ℝ) :
    fiscalTax G + (G - reservesPre) + reservesPost - facilityBorrowing =
      ProposedStationaryBank.depositRate * (G - reservesPre) +
        ProposedStationaryBank.reserveRate * reservesPost -
        facilityRate * facilityBorrowing := by
  unfold fiscalTax reservesPost facilityRate
  ring

theorem sourceFiscalTax_eq (G : ℝ) (t : ℕ)
    (h : History LocalBridgePhase t) :
    sourceFiscalTax (primitives G) (inheritedState G) (parentSettlementCarrier G) t h =
      fiscalTax G := by
  cases t with
  | zero =>
      change
        (ProposedStationaryBank.depositRate * (G - reservesPre) +
          ProposedStationaryBank.reserveRate * reservesPost -
          facilityRate * facilityBorrowing) / 1 -
          (G - reservesPre) - (parentSettlementCarrier G).reservesPostPayment 0 h +
          (parentSettlementCarrier G).facilityBorrowing 0 h = _
      rw [parentSettlementCarrier_postReserves, parentSettlementCarrier_facility]
      unfold fiscalTax reservesPost facilityRate
      ring
  | succ n =>
      change
        (ProposedStationaryBank.depositRate * (G - reservesPre) +
          ProposedStationaryBank.reserveRate *
            (parentSettlementCarrier G).reservesPostPayment n (previousHistory h) -
          facilityRate * (parentSettlementCarrier G).facilityBorrowing n (previousHistory h)) / 1 -
          (G - reservesPre) - (parentSettlementCarrier G).reservesPostPayment (n + 1) h +
          (parentSettlementCarrier G).facilityBorrowing (n + 1) h = _
      simp only [parentSettlementCarrier_postReserves, parentSettlementCarrier_facility]
      unfold fiscalTax reservesPost facilityRate
      ring

/-- Registro completo mediante las cuentas conservadas. Su construccion no
es una prueba de factibilidad privada, optimalidad ni equilibrio completo. -/
noncomputable def parentAllocation (G : ℝ) : Allocation LocalBridgePhase :=
  withSourceAccountingCompletion (primitives G) (inheritedState G)
    (parentSettlementCarrier G)

theorem parentAllocation_fiscalClosure (G : ℝ) :
    FiscalClosure (primitives G) (inheritedState G) (parentAllocation G) := by
  exact withSourceAccountingCompletion_fiscalClosure
    (primitives G) (inheritedState G) (parentSettlementCarrier G)
    (parentSettlementCarrier_settlementClears G)

theorem parentAllocation_collateralDual_pos (G : ℝ) (i : FirmType)
    (t : ℕ) (h : History LocalBridgePhase t) :
    0 < (parentAllocation G).collateralDual i t h := by
  exact collateralMultiplier_pos

theorem parentAllocation_tax_eq (G : ℝ) (t : ℕ)
    (h : History LocalBridgePhase t) :
    (parentAllocation G).tax t h = fiscalTax G := by
  cases t with
  | zero => exact sourceFiscalTax_eq G 0 h
  | succ n => exact sourceFiscalTax_eq G (n + 1) h

end ProposedStationaryInheritedState
end Ventura26LiquidityAllocation
