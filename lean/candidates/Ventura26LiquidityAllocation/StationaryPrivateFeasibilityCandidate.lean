import Ventura26LiquidityAllocation.StationaryLiteralAccountsCandidate

/-!
# Presupuestos y factibilidad privada del padre: PROPUESTA SIN COMPILAR

Proyecto: alejandroventuraventurameza-tech/ai-project.
Rama: work/chat-continuity.
Commit: 16e24fe828a5a0002ef13bb82bae9e295f190f86.
Base AppliedModelingLib: 194edcc95df74806a39b961d10dedddc6e730cce.
Lean previsto: leanprover/lean4:v4.30.0-rc2.
Mathlib: 5450b53e5ddc75d46418fabb605edbf36bd0beb6.
Destino: papers/Ventura26LiquidityAllocation/StationaryPrivateFeasibilityCandidate.lean.
SHA256 de StationaryLiteralAccountsCandidate.lean utilizado:
d07ca6f74d80056938060c36d071a06945913d5db99ef9657ac9095716d9868d

Todos los modulos propuestos de la cadena siguen SIN COMPILAR. Se han
consultado las definiciones conservadas y revisado algebra e interfaces;
no se han ejecutado Lean ni simulaciones. Esta revision no acredita kernel,
inspeccion de axiomas ni aprobacion de la auditoria semantica.

Argumento matematico previo al ensamblaje:
- Empresas: b_i=F_i/R, depositos cero y c_i+q*k_i=wealth_i+b_i.
  wealth_i es beneficio mas capital no depreciado menos F_i/1.
  La garantia se cumple por igualdad en todo hijo posible.
- Hogar: w*L=5Y/12; ingresos minorista Y/6, capital K/6400 y
  banco (R-1)E. Tras sustituir T(G), el residual de su presupuesto es
  el residual del rendimiento bancario menos el residual de balance.
  G>=Mpre aporta la no negatividad de bonos; el presupuesto no exige ese signo.
- Banco: con v=weight, la desviacion del retorno respecto de R*E es
  spread=(1/50)*(1+2v)*W. Se demuestra 0<spread<E/375 y
  g_minus=R*E-spread>(374/375)E>0, g_plus=R*E+spread>0.
  Se comprueban limites, liquidacion, encaje, cara inicial y solvencia
  de cada pago. Los retornos individuales no se sustituyen por su promedio.
- La renovacion agregada utiliza preExit=R*E, a_B=1/R y el ingreso
  neto (R-1)E. Es una identidad contable separada de BankFeasible.

ALCANCE: FirmBudgetFlows, HouseholdBudgetFlows, BankRenewalFlows y
FirmFeasible, HouseholdFeasible, BankFeasible para los planes especificos
extraidos o construidos desde parentAllocation G. No se recibe ninguna de
esas conclusiones como premisa. El plan bancario comun no constituye una
prueba de distribucion estacionaria de patrimonios individuales.
No se demuestra optimalidad, convergencia de objetivos, terminalidad,
el prefijo de 33 ecuaciones, continuacion intervenida ni equilibrio completo.
G queda simbolico. El padre vinculante y el impacto S permanecen separados.
-/

namespace Ventura26LiquidityAllocation
namespace ProposedStationaryPrivateFeasibility

/-! ## Empresas -/

open ProposedStationaryRealScale
open ProposedStationaryProductionBridge
open ProposedStationaryPrimitives
open ProposedStationaryInheritedState
open ProposedStationaryLiteralAccounts

/-- Beneficio literal a los precios del testigo, usando el puente de
produccion ya demostrado; no se repite la prueba de potencias reales. -/
theorem firm_operatingProfit_eq (i : FirmType) :
    operatingProfit (5 / 6) (technology i) (capital i) (labor i)
      (2 / 5) (1 / 2) wage = profit i := by
  unfold operatingProfit operatingOutput
  rw [production_identity i]
  unfold profit output labor
  field_simp [ne_of_gt wage_pos] <;> ring

theorem firm_loan_face_identity (i : FirmType) :
    ProposedStationaryBank.loanRate * loan i = firmFace i := by
  unfold loan
  field_simp [ne_of_gt loanRate_pos] <;> ring

theorem firm_budget_identity (i : FirmType) :
    firmConsumption i + capitalPrice * capital i = wealth i + loan i := by
  unfold wealth firmConsumption loan
  field_simp [ne_of_gt loanRate_pos] <;> ring

/-- La identidad usa la cara nominal completa F_i en el reembolso,
y no el principal del prestamo F_i/R. Es valida en cada fase del arbol. -/
theorem firm_wealth_flow_identity (G : ℝ) (i : FirmType)
    (phase : LocalBridgePhase) :
    wealth i =
      operatingProfit (5 / 6)
        ((primitives G).aggregateProductivity phase * (primitives G).productivity i)
        (capital i) (labor i) (primitives G).alpha (primitives G).beta wage +
        capitalPrice * (1 - (primitives G).depreciation) * capital i -
        realRepayment (firmFace i) 1 := by
  change wealth i =
    operatingProfit (5 / 6) (1 * technology i) (capital i) (labor i)
      (2 / 5) (1 / 2) wage +
      capitalPrice * (1 - (1 / 40 : ℝ)) * capital i - realRepayment (firmFace i) 1
  rw [one_mul, firm_operatingProfit_eq i]
  unfold wealth realRepayment
  ring

theorem firm_collateral_identity (i : FirmType) :
    ProposedStationaryBank.loanRate * loan i =
      pledgeability i * (1 - (1 / 40 : ℝ)) * (1 * capitalPrice) * capital i := by
  rw [firm_loan_face_identity i]
  unfold firmFace liquidationValue
  ring

/-- Presupuesto actual y riqueza con el timing literal, tanto en fecha
cero como en cada sucesor. No se reciben esas identidades como premisas. -/
theorem parent_firmBudgetFlows (G : ℝ) :
    FirmBudgetFlows (primitives G) (inheritedState G) (parentAllocation G) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i t h _hadmissible
    simpa only [parent_firmConsumption, parent_capitalPrice, parent_capital,
      parent_firmDeposit, parent_firmWealth, parent_loan, add_zero] using
        firm_budget_identity i
  · intro i h _hadmissible
    simpa only [parent_firmWealth, parent_inputPrice, parent_labor, parent_wage,
      parent_capitalPrice, parent_inflation, inheritedState] using
        firm_wealth_flow_identity G i (currentState h)
  · intro i t h s _hadmissible
    simpa only [parent_firmWealth, parent_inputPrice, parent_capital, parent_labor,
      parent_wage, parent_capitalPrice, parent_inflation, parent_firmFace] using
        firm_wealth_flow_identity G i s

/-- Factibilidad del plan empresarial literal en ambos tipos. La igualdad
de garantia vale para cada hijo; no se selecciona un hijo conveniente. -/
theorem parent_firmFeasible (G : ℝ) (i : FirmType) :
    FirmFeasible (primitives G) (inheritedState G) (parentAllocation G) i
      (firmPlanOfAllocation (parentAllocation G) i) := by
  have hflows := parent_firmBudgetFlows G
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro t h _hadmissible
    simpa only [firmPlanOfAllocation, parent_firmConsumption, parent_capital,
      parent_labor, parent_loan, parent_firmDeposit] using
      (show 0 < firmConsumption i ∧ 0 ≤ capital i ∧ 0 ≤ labor i ∧
          0 ≤ loan i ∧ 0 ≤ (0 : ℝ) from
        ⟨firmConsumption_pos i, (capital_pos i).le, (labor_pos i).le,
          (loan_pos i).le, le_rfl⟩)
  · intro t h _hadmissible
    change (parentAllocation G).firmFace i t h =
      signedFace ((parentAllocation G).loanRate t h) ((parentAllocation G).loan i t h)
        ((parentAllocation G).depositRate t h) ((parentAllocation G).firmDeposit i t h)
    rw [parent_firmFace, parent_loanRate, parent_loan, parent_depositRate,
      parent_firmDeposit]
    unfold signedFace
    rw [firm_loan_face_identity i] <;> ring
  · intro t h hadmissible
    exact hflows.1 i t h hadmissible
  · intro t h _hadmissible
    intro s _hpossible
    change (parentAllocation G).loanRate t h * (parentAllocation G).loan i t h ≤
      (primitives G).pledgeability i * (1 - (primitives G).depreciation) *
        ((parentAllocation G).inflation (t + 1) (childHistory h s) *
          (parentAllocation G).capitalPrice (t + 1) (childHistory h s)) *
        (parentAllocation G).capital i t h
    rw [parent_loanRate, parent_loan, parent_inflation, parent_capitalPrice,
      parent_capital]
    change ProposedStationaryBank.loanRate * loan i ≤
      pledgeability i * (1 - (1 / 40 : ℝ)) * (1 * capitalPrice) * capital i
    exact (firm_collateral_identity i).le
  · intro h hadmissible
    exact hflows.2.1 i h hadmissible
  · intro t h s hadmissible
    exact hflows.2.2 i t h s hadmissible


/-! ## Hogar -/

open ProposedStationaryRealScale
open ProposedStationaryProductionBridge
open ProposedStationaryReducedSystem
open ProposedStationaryPrimitives
open ProposedStationaryInheritedState
open ProposedStationaryLiteralAccounts

/-- La masa salarial se identifica a partir de las formulas reales,
sin usar una condicion de optimalidad del hogar. -/
theorem stationary_wage_bill :
    wage * aggregateLabor = (5 / 12 : ℝ) * aggregateOutput := by
  unfold aggregateLabor aggregateOutput average labor output
  field_simp [ne_of_gt wage_pos] <;> ring

/-- Identidad escalar que mantiene separados los tres ingresos de propiedad.
No requiere signo de G ni de su impuesto residual. -/
theorem scalar_household_budget (G : ℝ) :
    workerConsumption + bankDeposits + (G - reservesPre) =
      wage * aggregateLabor +
        (ProposedStationaryBank.depositRate * bankDeposits +
          ProposedStationaryBank.depositRate * (G - reservesPre)) +
        aggregateOutput / 6 + aggregateCapital / 6400 +
        (ProposedStationaryBank.loanRate - 1) * bankEquity - fiscalTax G := by
  have hbalance := bank_balance
  have hgross := scalar_bank_gross_return
  unfold reservesPost facilityRate at hgross
  rw [workerConsumption_resource_identity, stationary_wage_bill]
  unfold fiscalTax
  nlinarith [hbalance, hgross]

/-- Fecha cero: los rendimientos nominales proceden de inheritedState G. -/
theorem parent_householdBudget_dateZero (G : ℝ)
    (h : History LocalBridgePhase 0) :
    (parentAllocation G).workerConsumption 0 h +
        (parentAllocation G).householdDeposits 0 h +
        (parentAllocation G).householdBonds 0 h =
      (parentAllocation G).wage 0 h * (parentAllocation G).workerLabor 0 h +
        ((inheritedState G).depositRateLag *
            (inheritedState G).householdDeposits +
          (inheritedState G).governmentBondRateLag *
            (inheritedState G).householdBonds) /
          (parentAllocation G).inflation 0 h +
        (parentAllocation G).retailerNetIncome 0 h +
        (parentAllocation G).capitalProducerNetIncome 0 h +
        (parentAllocation G).bankNetIncome 0 h -
        (parentAllocation G).tax 0 h := by
  simpa only [parent_workerConsumption, parent_householdDeposits,
    parent_householdBonds, parent_wage, parent_workerLabor, parent_inflation,
    parent_retailerNetIncome, parent_capitalProducerNetIncome,
    parent_bankNetIncome, parent_tax, inheritedState, div_one] using
    scalar_household_budget G

/-- Sucesor: repagan las tenencias y tasas de la historia progenitora.
La igualdad es literal para todas las historias del portador constante. -/
theorem parent_householdBudget_successor (G : ℝ) (t : ℕ)
    (h : History LocalBridgePhase t) (s : LocalBridgePhase) :
    (parentAllocation G).workerConsumption (t + 1) (childHistory h s) +
        (parentAllocation G).householdDeposits (t + 1) (childHistory h s) +
        (parentAllocation G).householdBonds (t + 1) (childHistory h s) =
      (parentAllocation G).wage (t + 1) (childHistory h s) *
          (parentAllocation G).workerLabor (t + 1) (childHistory h s) +
        ((parentAllocation G).depositRate t h *
            (parentAllocation G).householdDeposits t h +
          (parentAllocation G).governmentBondRate t h *
            (parentAllocation G).householdBonds t h) /
          (parentAllocation G).inflation (t + 1) (childHistory h s) +
        (parentAllocation G).retailerNetIncome (t + 1) (childHistory h s) +
        (parentAllocation G).capitalProducerNetIncome (t + 1) (childHistory h s) +
        (parentAllocation G).bankNetIncome (t + 1) (childHistory h s) -
        (parentAllocation G).tax (t + 1) (childHistory h s) := by
  simpa only [parent_workerConsumption, parent_householdDeposits,
    parent_householdBonds, parent_wage, parent_workerLabor, parent_inflation,
    parent_depositRate, parent_governmentBondRate, parent_retailerNetIncome,
    parent_capitalProducerNetIncome, parent_bankNetIncome, parent_tax,
    div_one] using scalar_household_budget G

/-- Los dos casos temporales satisfacen HouseholdBudgetFlows sin presuponer
factibilidad, optimalidad ni cierre presupuestario del propio hogar. -/
theorem parent_householdBudgetFlows (G : ℝ) :
    HouseholdBudgetFlows (primitives G) (inheritedState G) (parentAllocation G) := by
  constructor
  · intro h _hadmissible
    exact parent_householdBudget_dateZero G h
  · intro t h s _hadmissible
    exact parent_householdBudget_successor G t h s

/-- Factibilidad del plan extraido de parentAllocation. La unica hipotesis
adicional es la no negatividad de los bonos publicos en manos del hogar. -/
theorem parent_householdFeasible (G : ℝ) (hG : reservesPre ≤ G) :
    HouseholdFeasible (primitives G) (inheritedState G) (parentAllocation G)
      (householdPlanOfAllocation (parentAllocation G)) := by
  refine ⟨?_, (parent_householdBudgetFlows G).1,
    (parent_householdBudgetFlows G).2⟩
  intro t h _hadmissible
  simpa only [householdPlanOfAllocation, parent_workerConsumption,
    parent_workerLabor, parent_householdDeposits, parent_householdBonds] using
    (show 0 < workerConsumption ∧ 0 ≤ aggregateLabor ∧
        0 ≤ bankDeposits ∧ 0 ≤ G - reservesPre from
      ⟨workerConsumption_pos, aggregates_pos.2.2.1.le,
        bank_scale_pos.2.1.le, sub_nonneg.mpr hG⟩)


/-! ## Banco y renovacion -/

open ProposedStationaryRealScale
open ProposedStationaryProductionBridge
open ProposedStationaryReducedSystem
open ProposedStationaryPrimitives
open ProposedStationaryInheritedState
open ProposedStationaryLiteralAccounts

noncomputable def commonBankPlan (G : ℝ) : BankPlan LocalBridgePhase :=
  fullRetentionCommonBankPlan (primitives G) (parentAllocation G)

noncomputable def bankPaymentSpread : ℝ :=
  (1 / 50) * (1 + 2 * ProposedStationaryBank.weight) * facilityBorrowing

theorem facilityBorrowing_lt_equity_div_fifteen :
    facilityBorrowing < bankEquity / 15 := by
  have hxi := ProposedStationaryBank.bank_margins_and_pricing.2.1
  have hbound := mul_lt_mul_of_pos_right hxi bank_scale_pos.1
  dsimp only [facilityBorrowing, bankDeposits]
  nlinarith only [hbound]

theorem bankPaymentSpread_bounds :
    0 < bankPaymentSpread ∧ bankPaymentSpread < bankEquity / 375 := by
  rcases ProposedStationaryBank.weight_bounds with ⟨hv0, hv1⟩
  have hfactor : 0 < (1 / 50 : ℝ) * (1 + 2 * ProposedStationaryBank.weight) :=
    mul_pos (by norm_num) (by linarith)
  have hfactorUpper :
      (1 / 50 : ℝ) * (1 + 2 * ProposedStationaryBank.weight) < 1 / 25 := by
    linarith
  constructor
  · exact mul_pos hfactor facilityBorrowing_pos
  · change (1 / 50 : ℝ) * (1 + 2 * ProposedStationaryBank.weight) *
      facilityBorrowing < bankEquity / 375
    calc
      _ < (1 / 25 : ℝ) * facilityBorrowing :=
        mul_lt_mul_of_pos_right hfactorUpper facilityBorrowing_pos
      _ < (1 / 25 : ℝ) * (bankEquity / 15) :=
        mul_lt_mul_of_pos_left facilityBorrowing_lt_equity_div_fifteen (by norm_num)
      _ = bankEquity / 375 := by ring

theorem bankPaymentReturn_minus_lower_bound :
    (374 / 375 : ℝ) * bankEquity <
      ProposedStationaryBank.loanRate * bankEquity - bankPaymentSpread := by
  have hreturn : bankEquity < ProposedStationaryBank.loanRate * bankEquity := by
    simpa only [one_mul] using
      mul_lt_mul_of_pos_right loanRate_gt_one bank_scale_pos.1
  have hspread := bankPaymentSpread_bounds.2
  linarith

theorem bankPaymentReturns_pos :
    0 < ProposedStationaryBank.loanRate * bankEquity - bankPaymentSpread ∧
      0 < ProposedStationaryBank.loanRate * bankEquity + bankPaymentSpread := by
  constructor
  · have hfloor : 0 < (374 / 375 : ℝ) * bankEquity :=
      mul_pos (by norm_num) bank_scale_pos.1
    exact lt_trans hfloor bankPaymentReturn_minus_lower_bound
  · exact add_pos (mul_pos loanRate_pos bank_scale_pos.1) bankPaymentSpread_bounds.1

theorem bank_caps_strict :
    bankDeposits < 4 * bankEquity ∧ aggregateCredit < 6 * bankEquity := by
  have hdeposits : bankDeposits = 2 * bankEquity := rfl
  have hequity := bank_scale_pos.1
  have hreserves := bank_scale_pos.2.2
  have hbalance := bank_balance
  constructor <;> linarith

/-- El promedio ya calculado permite aislar la parte del retorno anterior
al coste OTC/facilidad; no se igualan los dos retornos individuales. -/
theorem bank_base_return :
    ProposedStationaryBank.loanRate * aggregateCredit +
      ProposedStationaryBank.reserveRate * reservesPre -
      ProposedStationaryBank.depositRate * bankDeposits =
        ProposedStationaryBank.loanRate * bankEquity +
          (1 / 50 : ℝ) * facilityBorrowing := by
  calc
    _ = (ProposedStationaryBank.loanRate * aggregateCredit +
          ProposedStationaryBank.reserveRate * reservesPost -
          ProposedStationaryBank.depositRate * bankDeposits -
          facilityRate * facilityBorrowing) + (1 / 50 : ℝ) * facilityBorrowing := by
      unfold reservesPost facilityRate
      ring
    _ = _ := by rw [scalar_bank_gross_return]

theorem parent_bankOTCSlopes (G : ℝ) (t : ℕ)
    (h : History LocalBridgePhase t) :
    bankOTCDeficitSlopeAt (primitives G) (parentAllocation G) t h (1 / 2) =
        (1 + ProposedStationaryBank.weight) / 100 ∧
      bankOTCSurplusSlopeAt (primitives G) (parentAllocation G) t h (1 / 2) =
        ProposedStationaryBank.weight / 200 := by
  simp only [bankOTCDeficitSlopeAt, bankOTCSurplusSlopeAt,
    parent_reserveRate, parent_interbankRate, parent_facilityRate]
  change otcDeficitSlope ProposedStationaryBank.reserveRate
      (otcNegotiatedRate ProposedStationaryBank.reserveRate
        (ProposedStationaryBank.reserveRate + 1 / 50) (Real.log 2) (1 / 2))
      (ProposedStationaryBank.reserveRate + 1 / 50) (Real.log 2) (1 / 2) =
        (1 + ProposedStationaryBank.weight) / 100 ∧
    otcSurplusSlope ProposedStationaryBank.reserveRate
      (otcNegotiatedRate ProposedStationaryBank.reserveRate
        (ProposedStationaryBank.reserveRate + 1 / 50) (Real.log 2) (1 / 2))
      (Real.log 2) (1 / 2) = ProposedStationaryBank.weight / 200
  exact (ProposedStationaryBank.matching_specialization
    ProposedStationaryBank.reserveRate).2.2.2

theorem commonBankPlan_grossReturn_minus (G : ℝ) (t : ℕ)
    (h : History LocalBridgePhase t) :
    bankGrossReturn (primitives G) (parentAllocation G) (commonBankPlan G) 0 t h =
      ProposedStationaryBank.loanRate * bankEquity - bankPaymentSpread := by
  have hmem : (0 : BankPayment) ∈ (primitives G).paymentSupport := by
    change (0 : BankPayment) ∈ binarySupport
    norm_num [binarySupport]
  have hRR : 0 < ProposedStationaryBank.reserveRate := by
    have hr := ProposedStationaryBank.reserveRate_spec.1
    linarith
  have hreserve : (parentAllocation G).reserveRate t h ≠ 0 := by
    rw [parent_reserveRate]
    exact ne_of_gt hRR
  have hminus : -4 * facilityBorrowing < 0 := by
    have hW := facilityBorrowing_pos
    linarith
  change bankGrossReturn (primitives G) (parentAllocation G)
    (fullRetentionCommonBankPlan (primitives G) (parentAllocation G)) 0 t h = _
  rw [fullRetentionCommonBankPlan_grossReturn_eq_detailed
    (primitives G) (parentAllocation G) t h 0 hmem]
  rw [parent_bankTightness, parent_bankLoans, parent_reservesPrePayment,
    parent_bankDeposits]
  rw [bankDetailedPortfolioReturn_eq_reduced
    (primitives G) (parentAllocation G) t h (1 / 2) aggregateCredit reservesPre
      bankDeposits 0 hreserve]
  rw [(parent_bankOTCSlopes G t h).1, (parent_bankOTCSlopes G t h).2]
  change ProposedStationaryBank.loanRate * aggregateCredit +
      ProposedStationaryBank.reserveRate * reservesPre -
      ProposedStationaryBank.depositRate * bankDeposits +
      otcLiquidityPayoff ((1 + ProposedStationaryBank.weight) / 100)
        (ProposedStationaryBank.weight / 200)
        (bankSettlementSurplus reservesPre (1 / 10)
          (ProposedStationaryBank.depositRate / ProposedStationaryBank.reserveRate)
          bankDeposits (-(1 / 5))) = _
  rw [settlementSurplus_minus, otcLiquidityPayoff, if_pos hminus, bank_base_return]
  unfold bankPaymentSpread
  ring

theorem commonBankPlan_grossReturn_plus (G : ℝ) (t : ℕ)
    (h : History LocalBridgePhase t) :
    bankGrossReturn (primitives G) (parentAllocation G) (commonBankPlan G) 1 t h =
      ProposedStationaryBank.loanRate * bankEquity + bankPaymentSpread := by
  have hmem : (1 : BankPayment) ∈ (primitives G).paymentSupport := by
    change (1 : BankPayment) ∈ binarySupport
    norm_num [binarySupport]
  have hRR : 0 < ProposedStationaryBank.reserveRate := by
    have hr := ProposedStationaryBank.reserveRate_spec.1
    linarith
  have hreserve : (parentAllocation G).reserveRate t h ≠ 0 := by
    rw [parent_reserveRate]
    exact ne_of_gt hRR
  have hplus : ¬8 * facilityBorrowing < 0 := by
    have hW := facilityBorrowing_pos
    linarith
  change bankGrossReturn (primitives G) (parentAllocation G)
    (fullRetentionCommonBankPlan (primitives G) (parentAllocation G)) 1 t h = _
  rw [fullRetentionCommonBankPlan_grossReturn_eq_detailed
    (primitives G) (parentAllocation G) t h 1 hmem]
  rw [parent_bankTightness, parent_bankLoans, parent_reservesPrePayment,
    parent_bankDeposits]
  rw [bankDetailedPortfolioReturn_eq_reduced
    (primitives G) (parentAllocation G) t h (1 / 2) aggregateCredit reservesPre
      bankDeposits 1 hreserve]
  rw [(parent_bankOTCSlopes G t h).1, (parent_bankOTCSlopes G t h).2]
  change ProposedStationaryBank.loanRate * aggregateCredit +
      ProposedStationaryBank.reserveRate * reservesPre -
      ProposedStationaryBank.depositRate * bankDeposits +
      otcLiquidityPayoff ((1 + ProposedStationaryBank.weight) / 100)
        (ProposedStationaryBank.weight / 200)
        (bankSettlementSurplus reservesPre (1 / 10)
          (ProposedStationaryBank.depositRate / ProposedStationaryBank.reserveRate)
          bankDeposits (1 / 5)) = _
  rw [settlementSurplus_plus, otcLiquidityPayoff, if_neg hplus, bank_base_return]
  unfold bankPaymentSpread
  ring

theorem commonBankPlan_grossReturn_pos (G : ℝ) (t : ℕ)
    (h : History LocalBridgePhase t) (omega : BankPayment)
    (hmem : omega ∈ (primitives G).paymentSupport) :
    0 < bankGrossReturn (primitives G) (parentAllocation G)
      (commonBankPlan G) omega t h := by
  change omega ∈ binarySupport at hmem
  rcases (mem_binarySupport omega).mp hmem with hzero | hone
  · subst omega
    rw [commonBankPlan_grossReturn_minus]
    exact bankPaymentReturns_pos.1
  · subst omega
    rw [commonBankPlan_grossReturn_plus]
    exact bankPaymentReturns_pos.2

theorem commonBankPlan_expectedGrossReturn (G : ℝ) (t : ℕ)
    (h : History LocalBridgePhase t) :
    expectedBankGrossReturn (primitives G) (parentAllocation G)
      (commonBankPlan G) t h = ProposedStationaryBank.loanRate * bankEquity := by
  change finiteSupportExpectation (primitives G).paymentSupport
    (primitives G).paymentProbability (fun omega ↦
      bankGrossReturn (primitives G) (parentAllocation G)
        (commonBankPlan G) omega t h) = _
  rw [finiteSupportExpectation_eq_average_of_binarySymmetric
    (primitives G) 0 1 (1 / 5) (binary_payment_law G),
    commonBankPlan_grossReturn_minus, commonBankPlan_grossReturn_plus]
  ring

/-- Las condiciones del lema generico conservado se verifican aqui sobre
el portador con dual B. Se reutilizan los lemas fuente de facilidad no
negativa y margen posterior, y se exponen las siete condiciones del registro. -/
theorem commonBankPlan_feasible (G : ℝ) :
    BankFeasible (primitives G) (inheritedState G) (parentAllocation G)
      (commonBankPlan G) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro t h _hadmissible
    change 0 < (parentAllocation G).bankEquity t h ∧ 0 ≤ (0 : ℝ) ∧
      0 < (parentAllocation G).bankEquity t h ∧
      0 ≤ (parentAllocation G).bankLoans t h ∧
      0 ≤ (parentAllocation G).reservesPrePayment t h ∧
      0 ≤ (parentAllocation G).bankDeposits t h
    rw [parent_bankEquity, parent_bankLoans, parent_reservesPrePayment,
      parent_bankDeposits]
    exact ⟨bank_scale_pos.1, by norm_num, bank_scale_pos.1,
      aggregates_pos.2.2.2.le, bank_scale_pos.2.2.le, bank_scale_pos.2.1.le⟩
  · intro t h _hadmissible
    change (parentAllocation G).bankEquity t h =
      (parentAllocation G).bankEquity t h - 0
    ring
  · intro t h _hadmissible
    change (parentAllocation G).bankLoans t h +
        (parentAllocation G).reservesPrePayment t h =
      (parentAllocation G).bankDeposits t h + (parentAllocation G).bankEquity t h
    rw [parent_bankLoans, parent_reservesPrePayment, parent_bankDeposits,
      parent_bankEquity]
    linarith [bank_balance]
  · intro t h _hadmissible
    change (parentAllocation G).bankDeposits t h ≤
        (primitives G).bankDepositCap * (parentAllocation G).bankEquity t h ∧
      (parentAllocation G).bankLoans t h ≤
        (primitives G).bankLoanCap * (parentAllocation G).bankEquity t h
    rw [parent_bankDeposits, parent_bankLoans, parent_bankEquity]
    change bankDeposits ≤ 4 * bankEquity ∧ aggregateCredit ≤ 6 * bankEquity
    exact ⟨bank_caps_strict.1.le, bank_caps_strict.2.le⟩
  · intro t h _hadmissible omega _hmem
    have htightness : 0 < (parentAllocation G).bankTightness t h := by
      rw [parent_bankTightness]
      norm_num
    exact ⟨bankFacilityBorrowingAt_nonneg (primitives G) (parentAllocation G)
      t h ((parentAllocation G).bankTightness t h)
      ((parentAllocation G).reservesPrePayment t h)
      ((parentAllocation G).bankDeposits t h) htightness omega,
      rfl,
      bankPostSettlementReservesAt_ge_requirement (primitives G) (parentAllocation G)
        t h ((parentAllocation G).bankTightness t h)
        ((parentAllocation G).reservesPrePayment t h)
        ((parentAllocation G).bankDeposits t h) htightness omega⟩
  · intro h _hadmissible
    change (parentAllocation G).bankEquity 0 h =
      (inheritedState G).bankFace / (parentAllocation G).inflation 0 h
    rw [parent_bankEquity, parent_inflation]
    change bankEquity = bankEquity / 1
    ring
  · intro t h _hadmissible omega hmem s _htransition
    simpa only [parent_inflation, div_one] using
      (commonBankPlan_grossReturn_pos G t h omega hmem).le

theorem parent_bankPreExitEquity (G : ℝ) (t : ℕ)
    (h : History LocalBridgePhase t) :
    bankPreExitEquity (primitives G) (inheritedState G) (parentAllocation G) t h =
      ProposedStationaryBank.loanRate * bankEquity := by
  cases t with
  | zero =>
      change bankEquity / (bankRenewalFactor (primitives G) *
        (parentAllocation G).inflation 0 h) = _
      rw [parent_inflation, bankRenewalFactor_eq
        (primitives G) (stationary_parameters G)]
      field_simp [ne_of_gt loanRate_pos] <;> ring
  | succ n =>
      change aggregateBankGrossReturn (primitives G) (parentAllocation G)
        n (previousHistory h) / (parentAllocation G).inflation (n + 1) h = _
      rw [parent_grossReturn, parent_inflation, div_one]

theorem parent_bankRenewalFlows (G : ℝ) :
    BankRenewalFlows (primitives G) (inheritedState G) (parentAllocation G) := by
  refine ⟨?_, ?_, ?_⟩
  · intro t h _hadmissible
    rw [parent_bankRetainedEquity, parent_bankEquity, parent_bankDividend]
    ring
  · intro t h _hadmissible
    rw [parent_bankEquity, parent_bankPreExitEquity,
      bankRenewalFactor_eq (primitives G) (stationary_parameters G)]
    field_simp [ne_of_gt loanRate_pos] <;> ring
  · intro t h _hadmissible
    rw [parent_bankNetIncome, parent_bankDividend, parent_bankPreExitEquity]
    change (ProposedStationaryBank.loanRate - 1) * bankEquity =
      0 + (1 / 10 : ℝ) * (1 - seedShare) *
        (ProposedStationaryBank.loanRate * bankEquity)
    unfold seedShare
    field_simp [ne_of_gt loanRate_pos] <;> ring


/-! ## Paquetes explicitos de resultados -/

/-- Las tres clases de identidades de flujo se derivan por separado. -/
theorem parent_flow_identities (G : ℝ) :
    FirmBudgetFlows (primitives G) (inheritedState G) (parentAllocation G) ∧
      HouseholdBudgetFlows (primitives G) (inheritedState G) (parentAllocation G) ∧
      BankRenewalFlows (primitives G) (inheritedState G) (parentAllocation G) :=
  ⟨parent_firmBudgetFlows G, parent_householdBudgetFlows G, parent_bankRenewalFlows G⟩

/-- Factibilidad de los planes de los dos empresarios, el hogar y el banco
comun. El signo de G solo interviene en las tenencias publicas del hogar. -/
theorem parent_feasible_plans (G : ℝ) (hG : reservesPre ≤ G) :
    (∀ i, FirmFeasible (primitives G) (inheritedState G) (parentAllocation G) i
      (firmPlanOfAllocation (parentAllocation G) i)) ∧
    HouseholdFeasible (primitives G) (inheritedState G) (parentAllocation G)
      (householdPlanOfAllocation (parentAllocation G)) ∧
    BankFeasible (primitives G) (inheritedState G) (parentAllocation G)
      (commonBankPlan G) :=
  ⟨parent_firmFeasible G, parent_householdFeasible G hG, commonBankPlan_feasible G⟩

end ProposedStationaryPrivateFeasibility
end Ventura26LiquidityAllocation
