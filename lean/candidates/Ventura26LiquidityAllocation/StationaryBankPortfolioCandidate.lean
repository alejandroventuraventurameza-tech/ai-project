import Ventura26LiquidityAllocation.StationaryFirmOptimalityCandidate

/-!
# Soporte global y valor local del banco: PROPUESTA SIN COMPILAR

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

Destino propuesto: papers/Ventura26LiquidityAllocation/StationaryBankPortfolioCandidate.lean.
SHA256 de StationaryFirmOptimalityCandidate.lean utilizado:
1424cb92ff9c48d5cc4dcbea83535a28595ab7130c367d625d341d4ffc66dcb4

Argumento matematico previo al codigo:
1. Las pendientes de liquidez del padre son a=(1+v)/100 y b=v/200,
   donde v es el peso de negociacion conservado. Se tiene b<=a. Para todo
   saldo z, chi(z)<=a*z y chi(z)<=b*z, incluso en el quiebre z=0.
2. Aplicar el primer soporte al pago negativo y el segundo al positivo,
   ambos de probabilidad 1/2, acota el retorno detallado esperado por una
   forma lineal. Las identidades de precios la reducen a R*(L+M-D).
3. El balance L+M=D+x implica E[g]<=R*x. No se exige a una desviacion
   repetir los signos de liquidacion del candidato, ni interioridad de
   sus controles, ni solvencia estricta. El candidato alcanza R*E.
4. Con beta=99/100 y eta=1/10, aB=beta*(1-eta)*R esta entre cero y uno.
   La pendiente de valor vB=beta*eta*R/(1-aB) es mayor que uno porque
   beta*R>1. Satisface vB=beta*((1-eta)*vB+eta)*R.
5. V(t,e,h)=vB*e es homogeneo. Se verifican directamente los nueve
   componentes de BankBellmanLocalEnvironmentAt, usando la factibilidad
   ya construida y el soporte global, no una optimalidad supuesta.

ALCANCE: soporte de cartera y entorno local Bellman. La comparacion
infinita y el pago alcanzado por el candidato se demuestran en el modulo
siguiente. No se afirma unicidad de la cartera optima.
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

noncomputable def stationaryDeficitSlope : ℝ :=
  (1 + ProposedStationaryBank.weight) / 100

noncomputable def stationarySurplusSlope : ℝ :=
  ProposedStationaryBank.weight / 200

theorem stationary_bank_slopes_ordered :
    stationarySurplusSlope ≤ stationaryDeficitSlope := by
  have hv := ProposedStationaryBank.weight_bounds.1
  unfold stationarySurplusSlope stationaryDeficitSlope
  linarith

/-- Cada pendiente extrema da un soporte global de la funcion concava,
incluido el quiebre y cualquiera de los signos de una desviacion. -/
theorem liquidityPayoff_le_deficit_support (a b s : ℝ) (hab : b ≤ a) :
    otcLiquidityPayoff a b s ≤ a * s := by
  by_cases hs : s < 0
  · simp only [otcLiquidityPayoff, if_pos hs, le_refl]
  · rw [otcLiquidityPayoff, if_neg hs]
    exact mul_le_mul_of_nonneg_right hab (le_of_not_gt hs)

theorem liquidityPayoff_le_surplus_support (a b s : ℝ) (hab : b ≤ a) :
    otcLiquidityPayoff a b s ≤ b * s := by
  by_cases hs : s < 0
  · rw [otcLiquidityPayoff, if_pos hs]
    exact mul_le_mul_of_nonpos_right hab hs.le
  · simp only [otcLiquidityPayoff, if_neg hs, le_refl]

theorem stationary_bank_mean_slope :
    (stationaryDeficitSlope + stationarySurplusSlope) / 2 =
      ProposedStationaryBank.meanSlope := by
  unfold stationaryDeficitSlope stationarySurplusSlope
    ProposedStationaryBank.meanSlope
  ring

theorem stationary_bank_slope_gap :
    stationaryDeficitSlope - stationarySurplusSlope =
      ProposedStationaryBank.slopeGap := by
  unfold stationaryDeficitSlope stationarySurplusSlope
    ProposedStationaryBank.slopeGap
  ring

/-- La identidad de precios de depositos se usa en su forma exacta,
sin aproximar la raiz que define la tasa de reservas. -/
theorem stationary_bank_deposit_pricing :
    ProposedStationaryBank.depositRate +
        (1 / 10 : ℝ) * ProposedStationaryBank.meanSlope +
        (ProposedStationaryBank.depositRate / ProposedStationaryBank.reserveRate -
          1 / 10) * (1 / 5) * ProposedStationaryBank.slopeGap / 2 =
      ProposedStationaryBank.loanRate := by
  have hp := ProposedStationaryBank.bank_margins_and_pricing.2.2.2.2.1
  unfold ProposedStationaryBank.depositPricingResidual at hp
  unfold ProposedStationaryBank.loanRate
  linarith

/-- Forma lineal resultante de los dos soportes, valida para cualquier
triple real de controles; el balance se utiliza despues. -/
theorem stationary_bank_linear_envelope_identity
    (loans reserves deposits : ℝ) :
    ((ProposedStationaryBank.loanRate * loans +
          ProposedStationaryBank.reserveRate * reserves -
          ProposedStationaryBank.depositRate * deposits +
          stationaryDeficitSlope *
            bankSettlementSurplus reserves (1 / 10)
              (ProposedStationaryBank.depositRate / ProposedStationaryBank.reserveRate)
              deposits (-(1 / 5))) +
        (ProposedStationaryBank.loanRate * loans +
          ProposedStationaryBank.reserveRate * reserves -
          ProposedStationaryBank.depositRate * deposits +
          stationarySurplusSlope *
            bankSettlementSurplus reserves (1 / 10)
              (ProposedStationaryBank.depositRate / ProposedStationaryBank.reserveRate)
              deposits (1 / 5))) / 2 =
      ProposedStationaryBank.loanRate * (loans + reserves - deposits) := by
  calc
    _ = ProposedStationaryBank.loanRate * loans +
        (ProposedStationaryBank.reserveRate + ProposedStationaryBank.meanSlope) *
          reserves -
        (ProposedStationaryBank.depositRate +
          (1 / 10 : ℝ) * ProposedStationaryBank.meanSlope +
          (ProposedStationaryBank.depositRate / ProposedStationaryBank.reserveRate -
            1 / 10) * (1 / 5) * ProposedStationaryBank.slopeGap / 2) * deposits := by
        unfold bankSettlementSurplus stationaryDeficitSlope stationarySurplusSlope
          ProposedStationaryBank.meanSlope ProposedStationaryBank.slopeGap
        ring
    _ = _ := by
        rw [stationary_bank_deposit_pricing]
        change ProposedStationaryBank.loanRate * loans +
          ProposedStationaryBank.loanRate * reserves -
          ProposedStationaryBank.loanRate * deposits = _
        ring

/-- El retorno detallado de cualquier desviacion se identifica con la
funcion reducida usando el lema del checkpoint, antes de tomar esperanzas. -/
theorem parent_bankStaticPayoff_eq_expectedDetailed (G : ℝ) (t : ℕ)
    (h : History LocalBridgePhase t) (loans reserves deposits : ℝ) :
    bankStaticPortfolioPayoffAt (primitives G) (parentAllocation G) t h
        stationaryDeficitSlope stationarySurplusSlope loans reserves deposits =
      finiteSupportExpectation (primitives G).paymentSupport
        (primitives G).paymentProbability (fun omega ↦
          bankDetailedPortfolioReturnAt (primitives G) (parentAllocation G) t h
            ((parentAllocation G).bankTightness t h) loans reserves deposits omega) := by
  have hr : (parentAllocation G).reserveRate t h ≠ 0 := by
    rw [parent_reserveRate]
    have hr1 := ProposedStationaryBank.reserveRate_spec.1
    linarith
  unfold bankStaticPortfolioPayoffAt finiteSupportExpectation
  apply Finset.sum_congr rfl
  intro omega _hmem
  apply congrArg (fun z : ℝ ↦ (primitives G).paymentProbability omega * z)
  simpa only [parent_bankTightness, (parent_bankOTCSlopes G t h).1,
    (parent_bankOTCSlopes G t h).2, stationaryDeficitSlope,
    stationarySurplusSlope] using
      (bankDetailedPortfolioReturn_eq_reduced
        (primitives G) (parentAllocation G) t h (1 / 2)
        loans reserves deposits omega hr).symm

/-- Soporte global del retorno esperado. No se asume factibilidad,
signo de saldos, ni interioridad de los controles alternativos. -/
theorem parent_bankStaticPayoff_upper (G : ℝ) (t : ℕ)
    (h : History LocalBridgePhase t) (loans reserves deposits : ℝ) :
    bankStaticPortfolioPayoffAt (primitives G) (parentAllocation G) t h
        stationaryDeficitSlope stationarySurplusSlope loans reserves deposits ≤
      ProposedStationaryBank.loanRate * (loans + reserves - deposits) := by
  unfold bankStaticPortfolioPayoffAt
  rw [finiteSupportExpectation_eq_average_of_binarySymmetric
    (primitives G) 0 1 (1 / 5) (binary_payment_law G)]
  change
    ((ProposedStationaryBank.loanRate * loans +
          ProposedStationaryBank.reserveRate * reserves -
          ProposedStationaryBank.depositRate * deposits +
          otcLiquidityPayoff stationaryDeficitSlope stationarySurplusSlope
            (bankSettlementSurplus reserves (1 / 10)
              (ProposedStationaryBank.depositRate / ProposedStationaryBank.reserveRate)
              deposits (-(1 / 5)))) +
        (ProposedStationaryBank.loanRate * loans +
          ProposedStationaryBank.reserveRate * reserves -
          ProposedStationaryBank.depositRate * deposits +
          otcLiquidityPayoff stationaryDeficitSlope stationarySurplusSlope
            (bankSettlementSurplus reserves (1 / 10)
              (ProposedStationaryBank.depositRate / ProposedStationaryBank.reserveRate)
              deposits (1 / 5)))) / 2 ≤ _
  have hm := liquidityPayoff_le_deficit_support
    stationaryDeficitSlope stationarySurplusSlope
    (bankSettlementSurplus reserves (1 / 10)
      (ProposedStationaryBank.depositRate / ProposedStationaryBank.reserveRate)
      deposits (-(1 / 5))) stationary_bank_slopes_ordered
  have hp := liquidityPayoff_le_surplus_support
    stationaryDeficitSlope stationarySurplusSlope
    (bankSettlementSurplus reserves (1 / 10)
      (ProposedStationaryBank.depositRate / ProposedStationaryBank.reserveRate)
      deposits (1 / 5)) stationary_bank_slopes_ordered
  have hlinear := stationary_bank_linear_envelope_identity loans reserves deposits
  linarith

theorem parent_bankStaticPayoff_le_retained (G : ℝ) (t : ℕ)
    (h : History LocalBridgePhase t) (retained loans reserves deposits : ℝ)
    (hbalance : loans + reserves = deposits + retained) :
    bankStaticPortfolioPayoffAt (primitives G) (parentAllocation G) t h
        stationaryDeficitSlope stationarySurplusSlope loans reserves deposits ≤
      ProposedStationaryBank.loanRate * retained := by
  have heq : loans + reserves - deposits = retained := by linarith
  simpa only [heq] using
    parent_bankStaticPayoff_upper G t h loans reserves deposits

theorem parent_bankExpectedDetailed_upper (G : ℝ) (t : ℕ)
    (h : History LocalBridgePhase t) (loans reserves deposits : ℝ) :
    finiteSupportExpectation (primitives G).paymentSupport
        (primitives G).paymentProbability (fun omega ↦
          bankDetailedPortfolioReturnAt (primitives G) (parentAllocation G) t h
            ((parentAllocation G).bankTightness t h) loans reserves deposits omega) ≤
      ProposedStationaryBank.loanRate * (loans + reserves - deposits) := by
  rw [← parent_bankStaticPayoff_eq_expectedDetailed G t h loans reserves deposits]
  exact parent_bankStaticPayoff_upper G t h loans reserves deposits

/-- Forma que entra en la desigualdad dinamica: el rendimiento esperado
es a lo sumo R veces el patrimonio retenido literal del balance. -/
theorem parent_bankExpectedDetailed_le_retained (G : ℝ) (t : ℕ)
    (h : History LocalBridgePhase t) (retained loans reserves deposits : ℝ)
    (hbalance : loans + reserves = deposits + retained) :
    finiteSupportExpectation (primitives G).paymentSupport
        (primitives G).paymentProbability (fun omega ↦
          bankDetailedPortfolioReturnAt (primitives G) (parentAllocation G) t h
            ((parentAllocation G).bankTightness t h) loans reserves deposits omega) ≤
      ProposedStationaryBank.loanRate * retained := by
  have heq : loans + reserves - deposits = retained := by linarith
  simpa only [heq] using
    parent_bankExpectedDetailed_upper G t h loans reserves deposits

/-- El candidato alcanza el soporte. Se reutiliza el retorno detallado
por pago; no se reemplaza la riqueza individual por su esperanza. -/
theorem parent_bankStaticPayoff_candidate (G : ℝ) (t : ℕ)
    (h : History LocalBridgePhase t) :
    bankStaticPortfolioPayoffAt (primitives G) (parentAllocation G) t h
        stationaryDeficitSlope stationarySurplusSlope
        aggregateCredit reservesPre bankDeposits =
      ProposedStationaryBank.loanRate * bankEquity := by
  rw [parent_bankStaticPayoff_eq_expectedDetailed]
  calc
    _ = expectedBankGrossReturn (primitives G) (parentAllocation G)
        (commonBankPlan G) t h := by
      unfold finiteSupportExpectation expectedBankGrossReturn
      apply Finset.sum_congr rfl
      intro omega hmem
      apply congrArg (fun z : ℝ ↦ (primitives G).paymentProbability omega * z)
      symm
      simpa only [commonBankPlan, parent_bankLoans, parent_reservesPrePayment,
        parent_bankDeposits] using
          fullRetentionCommonBankPlan_grossReturn_eq_detailed
            (primitives G) (parentAllocation G) t h omega hmem
    _ = _ := commonBankPlan_expectedGrossReturn G t h

theorem parent_bankExpectedDetailed_candidate (G : ℝ) (t : ℕ)
    (h : History LocalBridgePhase t) :
    finiteSupportExpectation (primitives G).paymentSupport
        (primitives G).paymentProbability (fun omega ↦
          bankDetailedPortfolioReturnAt (primitives G) (parentAllocation G) t h
            ((parentAllocation G).bankTightness t h)
            aggregateCredit reservesPre bankDeposits omega) =
      ProposedStationaryBank.loanRate * bankEquity := by
  rw [← parent_bankStaticPayoff_eq_expectedDetailed]
  exact parent_bankStaticPayoff_candidate G t h

/-- Optimalidad estatica literal ante toda cartera del dominio fuente,
incluidos limites activos, saldo cero y solvencia no estricta. -/
theorem parent_bankStaticPortfolioOptimal (G : ℝ) (t : ℕ)
    (h : History LocalBridgePhase t) :
    BankStaticPortfolioOptimalAt (primitives G) (parentAllocation G) t h
      stationaryDeficitSlope stationarySurplusSlope bankEquity
      aggregateCredit reservesPre bankDeposits := by
  intro loans reserves deposits hp
  have hb : loans + reserves = deposits + bankEquity := hp.2.2.2.1
  have heq : loans + reserves - deposits = bankEquity := by linarith
  rw [parent_bankStaticPayoff_candidate]
  simpa only [heq] using
    parent_bankStaticPayoff_upper G t h loans reserves deposits

open ProposedStationaryRealScale
open ProposedStationaryPrimitives
open ProposedStationaryInheritedState
open ProposedStationaryLiteralAccounts
open ProposedStationaryPrivateFeasibility
open ProposedStationaryTerminal

noncomputable def bankValueSlope : ℝ :=
  ((99 / 100 : ℝ) * (1 / 10) * ProposedStationaryBank.loanRate) /
    (1 - (99 / 100 : ℝ) * (9 / 10) * ProposedStationaryBank.loanRate)

theorem bank_discounted_survival_return_bounds :
    0 < (99 / 100 : ℝ) * (9 / 10) * ProposedStationaryBank.loanRate ∧
      (99 / 100 : ℝ) * (9 / 10) * ProposedStationaryBank.loanRate < 1 := by
  have hR0 := loanRate_pos
  have hRupper := ProposedStationaryBank.bank_margins_and_pricing.2.2.2.2.2.2
  constructor <;> nlinarith

theorem bankValueSlope_den_pos :
    0 < 1 - (99 / 100 : ℝ) * (9 / 10) * ProposedStationaryBank.loanRate :=
  sub_pos.mpr bank_discounted_survival_return_bounds.2

theorem bankValueSlope_gt_one : 1 < bankValueSlope := by
  have hRlower := ProposedStationaryBank.bank_margins_and_pricing.2.2.2.2.2.1
  norm_num [ProposedStationaryBank.depositRate] at hRlower
  unfold bankValueSlope
  apply (lt_div_iff₀ bankValueSlope_den_pos).2
  nlinarith

theorem bankValueSlope_pos : 0 < bankValueSlope :=
  lt_trans (by norm_num) bankValueSlope_gt_one

theorem bankValueSlope_identity :
    bankValueSlope = (99 / 100 : ℝ) *
      ((9 / 10) * bankValueSlope + 1 / 10) * ProposedStationaryBank.loanRate := by
  have hden := bankValueSlope_den_pos.ne'
  have hdenScaled :
      (1000 - ProposedStationaryBank.loanRate * 891 : ℝ) ≠ 0 := by
    intro hzero
    apply hden
    nlinarith only [hzero]
  unfold bankValueSlope
  field_simp [hden, hdenScaled] <;> ring

theorem bank_continuation_weight_pos :
    0 < (99 / 100 : ℝ) * ((9 / 10) * bankValueSlope + 1 / 10) := by
  have hv := bankValueSlope_pos
  positivity

noncomputable def parentBankValue : BankValueProcess LocalBridgePhase :=
  fun _t equity _h ↦ bankValueSlope * equity

theorem parent_bankValue_homogeneous (G : ℝ) (t : ℕ)
    (h : History LocalBridgePhase t) :
    BankValueHomogeneousAt (primitives G) t h parentBankValue := by
  intro c equity s _hc _hequity _hs
  simp only [parentBankValue]
  ring

theorem parent_bankStochasticDiscount_eq (G : ℝ) (t : ℕ)
    (h : History LocalBridgePhase t) (s : LocalBridgePhase) :
    bankStochasticDiscountAt (primitives G) (parentAllocation G) t h s =
      (99 / 100 : ℝ) := by
  have hpower : workerConsumption ^ (-(1 : ℝ)) ≠ 0 :=
    (Real.rpow_pos_of_pos workerConsumption_pos (-(1 : ℝ))).ne'
  unfold bankStochasticDiscountAt
  simp only [parent_workerConsumption]
  change (99 / 100 : ℝ) * workerConsumption ^ (-(1 : ℝ)) /
      workerConsumption ^ (-(1 : ℝ)) = (99 / 100 : ℝ)
  field_simp [hpower] <;> ring

theorem parent_bankBellmanWeight (G : ℝ) (t : ℕ)
    (h : History LocalBridgePhase t) :
    bankBellmanContinuationWeightAt (primitives G) (parentAllocation G) t h
        (parentBankValue (t + 1)) =
      (99 / 100 : ℝ) * ((9 / 10) * bankValueSlope + 1 / 10) := by
  unfold bankBellmanContinuationWeightAt
  simp only [parent_bankStochasticDiscount_eq, parent_inflation,
    parentBankValue, mul_one, div_one]
  change (∑ s, (primitives G).tree.transition (currentState h) s *
      (99 / 100 : ℝ) * ((1 - (1 / 10 : ℝ)) * bankValueSlope + 1 / 10)) = _
  calc
    _ = (∑ s, (primitives G).tree.transition (currentState h) s) *
        ((99 / 100 : ℝ) * ((9 / 10) * bankValueSlope + 1 / 10)) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro s _hs
      ring
    _ = _ := by
      rw [(primitives G).tree.transition_sum_one]
      ring

theorem parent_bankDeficitSlope (G : ℝ) (t : ℕ)
    (h : History LocalBridgePhase t) :
    bankOTCDeficitSlopeAt (primitives G) (parentAllocation G) t h
        ((parentAllocation G).bankTightness t h) = stationaryDeficitSlope := by
  rw [parent_bankTightness]
  exact (parent_bankOTCSlopes G t h).1

theorem parent_bankSurplusSlope (G : ℝ) (t : ℕ)
    (h : History LocalBridgePhase t) :
    bankOTCSurplusSlopeAt (primitives G) (parentAllocation G) t h
        ((parentAllocation G).bankTightness t h) = stationarySurplusSlope := by
  rw [parent_bankTightness]
  exact (parent_bankOTCSlopes G t h).2

/-- La factibilidad estatica se extrae de la continuacion literal ya
construida, utilizando el lema fuente y sus seis coincidencias iniciales. -/
theorem parent_bankStaticFeasible (G : ℝ) (t : ℕ)
    (h : History LocalBridgePhase t)
    (hh : FirmHistoryAdmissible (primitives G) t h) :
    BankStaticPortfolioFeasibleAt (primitives G) (parentAllocation G) t h
      (bankOTCDeficitSlopeAt (primitives G) (parentAllocation G) t h
        ((parentAllocation G).bankTightness t h))
      (bankOTCSurplusSlopeAt (primitives G) (parentAllocation G) t h
        ((parentAllocation G).bankTightness t h))
      ((commonBankPlan G).retainedEquity t h) ((commonBankPlan G).loans t h)
      ((commonBankPlan G).reservesPre t h) ((commonBankPlan G).deposits t h) := by
  apply continuationCandidate_staticFeasibleAt (primitives G) (parentAllocation G)
    (commonBankPlan G) t h (parentBankContinuation G t h)
  · have hequity : (commonBankPlan G).equity t h = bankEquity :=
      parent_bankEquity G t h
    simpa only [hequity] using parent_bankContinuation_feasible G t h hh
  · exact parent_bankContinuation_startsWithPlanAt G t h

/-- Comparacion Bellman ante cualquier triple factible, con riqueza
retenida arbitraria. La funcion de valor es explicitamente lineal. -/
theorem parent_bankBellmanContinuation_le (G : ℝ) (t : ℕ)
    (h : History LocalBridgePhase t) (retained loans reserves deposits : ℝ)
    (hfeasible : BankStaticPortfolioFeasibleAt (primitives G) (parentAllocation G) t h
      (bankOTCDeficitSlopeAt (primitives G) (parentAllocation G) t h
        ((parentAllocation G).bankTightness t h))
      (bankOTCSurplusSlopeAt (primitives G) (parentAllocation G) t h
        ((parentAllocation G).bankTightness t h))
      retained loans reserves deposits) :
    bankBellmanContinuationAt (primitives G) (parentAllocation G) t h
      (bankOTCDeficitSlopeAt (primitives G) (parentAllocation G) t h
        ((parentAllocation G).bankTightness t h))
      (bankOTCSurplusSlopeAt (primitives G) (parentAllocation G) t h
        ((parentAllocation G).bankTightness t h))
      loans reserves deposits (parentBankValue (t + 1)) ≤
      bankValueSlope * retained := by
  rw [bankBellmanContinuation_eq_weight_mul_payoff (primitives G) (parentAllocation G)
    t h _ _ retained loans reserves deposits parentBankValue
    (parent_bankValue_homogeneous G t h) hfeasible, parent_bankBellmanWeight]
  rw [parent_bankDeficitSlope, parent_bankSurplusSlope]
  have hbalance : loans + reserves = deposits + retained := hfeasible.2.2.2.1
  calc
    _ ≤ ((99 / 100 : ℝ) * ((9 / 10) * bankValueSlope + 1 / 10)) *
        (ProposedStationaryBank.loanRate * retained) :=
      mul_le_mul_of_nonneg_left
        (parent_bankStaticPayoff_le_retained G t h retained loans reserves deposits
          hbalance) bank_continuation_weight_pos.le
    _ = bankValueSlope * retained := by
      rw [← mul_assoc, ← bankValueSlope_identity]

/-- Todas las condiciones locales de Bellman quedan demostradas para V=v*e.
La igualdad de este V con el pago infinito del candidato es otro teorema. -/
theorem parent_bankBellmanLocalEnvironment (G : ℝ) (t : ℕ)
    (h : History LocalBridgePhase t)
    (hh : FirmHistoryAdmissible (primitives G) t h) :
    BankBellmanLocalEnvironmentAt (primitives G) (parentAllocation G) t h
      (commonBankPlan G) ((parentAllocation G).bankTightness t h) parentBankValue := by
  have hfeasible := parent_bankStaticFeasible G t h hh
  have hequity : (commonBankPlan G).equity t h = bankEquity :=
    parent_bankEquity G t h
  have hretained : (commonBankPlan G).retainedEquity t h = bankEquity :=
    parent_bankEquity G t h
  have hdividend : (commonBankPlan G).dividend t h = 0 := rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, hfeasible, ?_, ?_, ?_⟩
  · simpa only [parent_workerConsumption] using workerConsumption_pos
  · intro s _hs
    simpa only [parent_workerConsumption] using workerConsumption_pos
  · intro s _hs
    rw [parent_bankStochasticDiscount_eq]
    norm_num
  · simpa only [hdividend] using (le_refl (0 : ℝ))
  · rw [hretained, hequity, hdividend, sub_zero]
  · rw [bankBellmanContinuation_eq_weight_mul_payoff (primitives G)
      (parentAllocation G) t h _ _ ((commonBankPlan G).retainedEquity t h)
      ((commonBankPlan G).loans t h) ((commonBankPlan G).reservesPre t h)
      ((commonBankPlan G).deposits t h) parentBankValue
      (parent_bankValue_homogeneous G t h) hfeasible,
      parent_bankBellmanWeight, parent_bankDeficitSlope, parent_bankSurplusSlope]
    have hloans : (commonBankPlan G).loans t h = aggregateCredit :=
      parent_bankLoans G t h
    have hreserves : (commonBankPlan G).reservesPre t h = reservesPre :=
      parent_reservesPrePayment G t h
    have hdeposits : (commonBankPlan G).deposits t h = bankDeposits :=
      parent_bankDeposits G t h
    rw [hloans, hreserves, hdeposits, parent_bankStaticPayoff_candidate,
      hdividend, zero_add]
    change bankValueSlope * ((commonBankPlan G).equity t h) = _
    rw [hequity, ← mul_assoc, ← bankValueSlope_identity]
  · intro loans reserves deposits hdeviation
    have hbound := parent_bankBellmanContinuation_le G t h
      ((commonBankPlan G).retainedEquity t h) loans reserves deposits hdeviation
    simpa only [hdividend, zero_add, hretained, parentBankValue, hequity] using hbound
  · rw [parent_bankBellmanWeight]
    exact bank_continuation_weight_pos

end ProposedStationaryBankOptimality
end Ventura26LiquidityAllocation
