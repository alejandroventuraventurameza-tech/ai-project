import Ventura26LiquidityAllocation.StationaryTerminalFoundationCandidate

/-!
# Objetivos y condiciones terminales del padre: PROPUESTA SIN COMPILAR

Proyecto: alejandroventuraventurameza-tech/ai-project.
Rama: work/chat-continuity.
Commit: 16e24fe828a5a0002ef13bb82bae9e295f190f86.
Base AppliedModelingLib: 194edcc95df74806a39b961d10dedddc6e730cce.
Lean previsto: leanprover/lean4:v4.30.0-rc2.
Mathlib: 5450b53e5ddc75d46418fabb605edbf36bd0beb6.
Destino propuesto: papers/Ventura26LiquidityAllocation/StationaryObjectiveTerminalCandidate.lean.
SHA256 de StationaryTerminalFoundationCandidate.lean utilizado:
d380abf2733c5d6523de99e903947ceace7fe8c38f667a99ef5f39b457c9832b

Todos los modulos propuestos de la cadena siguen SIN COMPILAR. Se han
consultado las definiciones conservadas y revisado algebra e interfaces;
no se han ejecutado Lean ni simulaciones. Esta revision no acredita kernel,
inspeccion de axiomas ni aprobacion de la auditoria semantica.

Argumento matematico previo al codigo:
- Las cantidades de empresas y hogar son constantes. La expectativa
  literal del calendario se evalua en la historia canonica, de peso uno.
  Las utilidades son coeficientes reales fijos multiplicados por beta^t,
  con betaE=24/25 y betaW=99/100. No se exige signo a esos coeficientes.
- El termino terminal empresarial usa c_i^(-1)*(q*k_i-b_i), con deposito
  cero: b_i es el principal, distinto de la cara F_i. El del hogar usa
  CW^(-1)*(D+G-Mpre). El descuento de cada coeficiente converge a cero.
- La continuacion bancaria es bankContinuationPolicyFromPlan, con el
  historial completo de pagos. Su patrimonio e_n no se sustituye por E.
  La homogeneidad fuente y los retornos de cada pago dan
  e_(n+1)=(e_n/E)*g_omega, con 0<g_omega<(21/20)*E.
  Induccion: 0<e_n<=E*(21/20)^n.
- El SDF acumulado es (99/100)^n y la supervivencia es (9/10)^n.
  La normalizacion de los pesos y la cota puntual dan
  0<=survivingTerm_n<=E*(18711/20000)^n, con 18711/20000<1.
- El dividendo es cero; el objetivo conserva los pagos de salida.
  payoff_0=0 y payoff_(n+1)=survivingTerm_(n+1)/9.
  La envolvente del payoff tiene coeficiente E/9 y la misma tasa.
  El lema conservado de envolventes descarga objetivo y TVC por separado.

ALCANCE: objetivos bien definidos y condiciones terminales fuente para
los planes construidos de H, L, hogar y continuacion bancaria. Se prueba
ademas factibilidad de la continuacion en historias actuales admisibles
y coincidencia de sus seis campos iniciales con el plan comun.
No se recibe SourceAdmissible, terminalidad u optimalidad como premisa.
La TVC bancaria fuente depende de equity, no de un proceso de valor V.
No se afirma dominancia sobre planes alternativos, BankOptimal, equilibrio
completo, distribucion bancaria estacionaria ni continuacion perturbada.
Las convergencias valen para todo G real. La factibilidad economica del
hogar sigue requiriendo G>=Mpre, demostrado por separado en el modulo
previo. G permanece simbolico; las ramas macroeconomicas S y B se conservan.
-/

open scoped BigOperators
open Filter

namespace Ventura26LiquidityAllocation
namespace ProposedStationaryTerminal

/-! ## Empresas y hogar: los terminos literales son geometricos -/

open ProposedStationaryRealScale
open ProposedStationaryPrimitives
open ProposedStationaryInheritedState
open ProposedStationaryLiteralAccounts
open ProposedStationaryTerminalFoundation

/-- Utilidad empresarial de una fecha, anterior al descuento. No se
necesita convertir CRRA en logaritmo para demostrar sumabilidad. -/
noncomputable def firmUtilityCoefficient (i : FirmType) : ℝ :=
  crraUtility 1 (firmConsumption i)

/-- Utilidad neta del hogar por fecha, con curvatura y escala laboral uno. -/
noncomputable def householdUtilityCoefficient : ℝ :=
  crraUtility 1 workerConsumption - aggregateLabor ^ (2 : ℝ) / 2

/-- Marginal empresarial por la cartera valorada a precios corrientes. -/
noncomputable def firmTerminalCoefficient (i : FirmType) : ℝ :=
  firmConsumption i ^ (-1 : ℝ) * (capitalPrice * capital i - loan i)

/-- Marginal del hogar por sus depositos y bonos; G permanece simbolico. -/
noncomputable def householdTerminalCoefficient (G : ℝ) : ℝ :=
  workerConsumption ^ (-1 : ℝ) * (bankDeposits + (G - reservesPre))

/-- Identidad del termino literal de utilidad, incluida su expectativa. -/
theorem parent_firmUtilityTerm (G : ℝ) (i : FirmType) (t : ℕ) :
    firmUtilityTerm (primitives G) (firmPlanOfAllocation (parentAllocation G) i) t =
      (24 / 25 : ℝ) ^ t * firmUtilityCoefficient i := by
  unfold firmUtilityTerm
  rw [primitives_expectationAt_eq]
  change (24 / 25 : ℝ) ^ t *
    crraUtility 1 ((parentAllocation G).firmConsumption i t (localBridgeHistory t)) = _
  simp only [parent_firmConsumption, firmUtilityCoefficient]

/-- La desutilidad laboral es constante, al igual que el consumo del hogar. -/
theorem parent_householdUtilityTerm (G : ℝ) (t : ℕ) :
    householdUtilityTerm (primitives G)
        (householdPlanOfAllocation (parentAllocation G)) t =
      (99 / 100 : ℝ) ^ t * householdUtilityCoefficient := by
  unfold householdUtilityTerm
  rw [primitives_expectationAt_eq]
  change (99 / 100 : ℝ) ^ t *
    (crraUtility 1 ((parentAllocation G).workerConsumption t (localBridgeHistory t)) -
      (1 : ℝ) * ((parentAllocation G).workerLabor t (localBridgeHistory t)) ^
        (1 + (1 : ℝ)) / (1 + (1 : ℝ))) = _
  rw [parent_workerConsumption, parent_workerLabor]
  norm_num [householdUtilityCoefficient]

/-- Identidad de la condicion fuente: capital al precio q, principal
del prestamo y deposito empresarial cero. -/
theorem parent_firmTerminalTerm (G : ℝ) (i : FirmType) (t : ℕ) :
    firmTerminalTerm (primitives G) (parentAllocation G)
        (firmPlanOfAllocation (parentAllocation G) i) t =
      (24 / 25 : ℝ) ^ t * firmTerminalCoefficient i := by
  unfold firmTerminalTerm
  rw [primitives_expectationAt_eq]
  change (24 / 25 : ℝ) ^ t *
    (((parentAllocation G).firmConsumption i t (localBridgeHistory t)) ^ (-1 : ℝ) *
      ((parentAllocation G).capitalPrice t (localBridgeHistory t) *
          (parentAllocation G).capital i t (localBridgeHistory t) -
        (parentAllocation G).loan i t (localBridgeHistory t) +
        (parentAllocation G).firmDeposit i t (localBridgeHistory t))) = _
  simp only [parent_firmConsumption, parent_capitalPrice, parent_capital,
    parent_loan, parent_firmDeposit, add_zero, firmTerminalCoefficient]

/-- La condicion fuente del hogar usa D+GH, sin incluir el ingreso bancario
como si fuera un activo adicional de su plan. -/
theorem parent_householdTerminalTerm (G : ℝ) (t : ℕ) :
    householdTerminalTerm (primitives G)
        (householdPlanOfAllocation (parentAllocation G)) t =
      (99 / 100 : ℝ) ^ t * householdTerminalCoefficient G := by
  unfold householdTerminalTerm
  rw [primitives_expectationAt_eq]
  change (99 / 100 : ℝ) ^ t *
    (((parentAllocation G).workerConsumption t (localBridgeHistory t)) ^ (-1 : ℝ) *
      ((parentAllocation G).householdDeposits t (localBridgeHistory t) +
        (parentAllocation G).householdBonds t (localBridgeHistory t))) = _
  simp only [parent_workerConsumption, parent_householdDeposits,
    parent_householdBonds, householdTerminalCoefficient]

/-- Objetivo empresarial bien definido por sumabilidad geometrica literal. -/
theorem parent_firmObjectiveWellDefined (G : ℝ) (i : FirmType) :
    FirmObjectiveWellDefined (primitives G)
      (firmPlanOfAllocation (parentAllocation G) i) := by
  change Summable (fun t : ℕ ↦
    firmUtilityTerm (primitives G) (firmPlanOfAllocation (parentAllocation G) i) t)
  simpa only [parent_firmUtilityTerm] using
    (fixed_beta_geometric (24 / 25 : ℝ) (firmUtilityCoefficient i)
      (by norm_num) (by norm_num)).1

/-- Objetivo del hogar bien definido, sin restriccion sobre G. -/
theorem parent_householdObjectiveWellDefined (G : ℝ) :
    HouseholdObjectiveWellDefined (primitives G)
      (householdPlanOfAllocation (parentAllocation G)) := by
  change Summable (fun t : ℕ ↦ householdUtilityTerm (primitives G)
    (householdPlanOfAllocation (parentAllocation G)) t)
  simpa only [parent_householdUtilityTerm] using
    (fixed_beta_geometric (99 / 100 : ℝ) householdUtilityCoefficient
      (by norm_num) (by norm_num)).1

/-- Terminalidad empresarial de la cartera construida, sin usar optimalidad. -/
theorem parent_firmSourceTerminalCondition (G : ℝ) (i : FirmType) :
    FirmSourceTerminalCondition (primitives G) (parentAllocation G)
      (firmPlanOfAllocation (parentAllocation G) i) := by
  change Tendsto (fun t : ℕ ↦ firmTerminalTerm (primitives G) (parentAllocation G)
    (firmPlanOfAllocation (parentAllocation G) i) t) atTop (nhds 0)
  simpa only [parent_firmTerminalTerm] using
    (fixed_beta_geometric (24 / 25 : ℝ) (firmTerminalCoefficient i)
      (by norm_num) (by norm_num)).2

/-- El coeficiente terminal puede tener cualquier signo para G arbitrario;
su descuento sigue convergiendo a cero. Factibilidad requiere aparte G>=Mpre. -/
theorem parent_householdSourceTerminalCondition (G : ℝ) :
    HouseholdSourceTerminalCondition (primitives G)
      (householdPlanOfAllocation (parentAllocation G)) := by
  change Tendsto (fun t : ℕ ↦ householdTerminalTerm (primitives G)
    (householdPlanOfAllocation (parentAllocation G)) t) atTop (nhds 0)
  simpa only [parent_householdTerminalTerm] using
    (fixed_beta_geometric (99 / 100 : ℝ) (householdTerminalCoefficient G)
      (by norm_num) (by norm_num)).2


/-! ## Banco: continuacion con riqueza individual por historial de pagos -/

open ProposedStationaryRealScale
open ProposedStationaryProductionBridge
open ProposedStationaryReducedSystem
open ProposedStationaryPrimitives
open ProposedStationaryInheritedState
open ProposedStationaryLiteralAccounts
open ProposedStationaryPrivateFeasibility
open ProposedStationaryTerminalFoundation

noncomputable def parentBankContinuation (G : ℝ) (t : ℕ)
    (h : History LocalBridgePhase t) :
    BankContinuationPolicy LocalBridgePhase (primitives G).paymentSupport :=
  bankContinuationPolicyFromPlan (primitives G) (parentAllocation G)
    (commonBankPlan G) t h

theorem commonBankPlan_grossReturn_upper (G : ℝ) (t : ℕ)
    (h : History LocalBridgePhase t) (omega : BankPayment)
    (hmem : omega ∈ (primitives G).paymentSupport) :
    bankGrossReturn (primitives G) (parentAllocation G)
      (commonBankPlan G) omega t h < (21 / 20 : ℝ) * bankEquity := by
  rcases ProposedStationaryBank.bank_margins_and_pricing with
    ⟨_hxi0, _hxi1, _hr0, _hr1, _hpricing, _hR0, hR1⟩
  have hreturn := mul_lt_mul_of_pos_right hR1 bank_scale_pos.1
  have hspread0 := bankPaymentSpread_bounds.1
  have hspread1 := bankPaymentSpread_bounds.2
  have hequity := bank_scale_pos.1
  change omega ∈ binarySupport at hmem
  rcases (mem_binarySupport omega).mp hmem with hzero | hone
  · subst omega
    rw [commonBankPlan_grossReturn_minus]
    linarith
  · subst omega
    rw [commonBankPlan_grossReturn_plus]
    linarith

/-- La prueba usa la misma recursion fuente que genera la riqueza real
individual. La positividad se establece antes de aplicar homogeneidad. -/
theorem parent_bankContinuation_equity_bounds
    (G : ℝ) (t : ℕ) (h : History LocalBridgePhase t) (n : ℕ)
    (future : Fin n → LocalBridgePhase)
    (payments : Fin n → (primitives G).paymentSupport) :
    0 < (parentBankContinuation G t h).equity n future payments ∧
      (parentBankContinuation G t h).equity n future payments ≤
        bankEquity * (21 / 20 : ℝ) ^ n := by
  induction n generalizing future payments with
  | zero =>
      change 0 < (parentAllocation G).bankEquity t h ∧
        (parentAllocation G).bankEquity t h ≤ bankEquity * (21 / 20 : ℝ) ^ 0
      rw [parent_bankEquity, pow_zero, mul_one]
      exact ⟨bank_scale_pos.1, le_rfl⟩
  | succ n ih =>
      let previousFuture : Fin n → LocalBridgePhase := fun j ↦ future j.succ
      let previousPayments : Fin n → (primitives G).paymentSupport :=
        fun j ↦ payments j.succ
      let H : History LocalBridgePhase (t + n) := continuationHistory h previousFuture
      let e := (parentBankContinuation G t h).equity n previousFuture previousPayments
      have hprevious := ih previousFuture previousPayments
      have he0 : 0 < e := hprevious.1
      have heUpper : e ≤ bankEquity * (21 / 20 : ℝ) ^ n := hprevious.2
      have hscale : 0 < e / bankEquity := div_pos he0 bank_scale_pos.1
      have hchild :
          (parentBankContinuation G t h).equity (n + 1) future payments =
            (e / bankEquity) * bankGrossReturn (primitives G) (parentAllocation G)
              (commonBankPlan G) (payments 0) (t + n) H := by
        change bankDetailedPortfolioReturnAt (primitives G) (parentAllocation G)
            (t + n) H ((parentAllocation G).bankTightness (t + n) H)
            ((e / (parentAllocation G).bankEquity (t + n) H) *
              (parentAllocation G).bankLoans (t + n) H)
            ((e / (parentAllocation G).bankEquity (t + n) H) *
              (parentAllocation G).reservesPrePayment (t + n) H)
            ((e / (parentAllocation G).bankEquity (t + n) H) *
              (parentAllocation G).bankDeposits (t + n) H) (payments 0) /
            (parentAllocation G).inflation (t + n + 1)
              (childHistory H (future 0)) = _
        rw [parent_bankEquity, parent_inflation, div_one]
        rw [bankDetailedPortfolioReturnAt_scale (primitives G) (parentAllocation G)
          (t + n) H ((parentAllocation G).bankTightness (t + n) H)
          ((parentAllocation G).bankLoans (t + n) H)
          ((parentAllocation G).reservesPrePayment (t + n) H)
          ((parentAllocation G).bankDeposits (t + n) H)
          (e / bankEquity) hscale (payments 0)]
        rw [← fullRetentionCommonBankPlan_grossReturn_eq_detailed
          (primitives G) (parentAllocation G) (t + n) H
          (payments 0) (payments 0).property]
      have hg0 := commonBankPlan_grossReturn_pos G (t + n) H
        (payments 0) (payments 0).property
      have hgUpper := commonBankPlan_grossReturn_upper G (t + n) H
        (payments 0) (payments 0).property
      rw [hchild]
      constructor
      · exact mul_pos hscale hg0
      · calc
          (e / bankEquity) * bankGrossReturn (primitives G) (parentAllocation G)
              (commonBankPlan G) (payments 0) (t + n) H ≤
              (e / bankEquity) * ((21 / 20 : ℝ) * bankEquity) :=
            mul_le_mul_of_nonneg_left hgUpper.le hscale.le
          _ = e * (21 / 20 : ℝ) := by
            field_simp [ne_of_gt bank_scale_pos.1] <;> ring
          _ ≤ (bankEquity * (21 / 20 : ℝ) ^ n) * (21 / 20 : ℝ) :=
            mul_le_mul_of_nonneg_right heUpper (by norm_num)
          _ = bankEquity * (21 / 20 : ℝ) ^ (n + 1) := by
            rw [pow_succ]
            ring

theorem parent_bankContinuation_dividend_zero
    (G : ℝ) (t : ℕ) (h : History LocalBridgePhase t) (n : ℕ)
    (future : Fin n → LocalBridgePhase)
    (payments : Fin n → (primitives G).paymentSupport) :
    (parentBankContinuation G t h).dividend n future payments = 0 := by
  change bankContinuationPlanScaleAt (primitives G) (parentAllocation G)
      (commonBankPlan G) t h n future payments * 0 = 0
  ring

/-- El SDF es de consumo real; no se incorpora otra inflacion ni la
renovacion a_B en el descuento de supervivencia. -/
theorem parent_bankCumulativeSDF (G : ℝ) (t : ℕ)
    (h : History LocalBridgePhase t) (n : ℕ)
    (future : Fin n → LocalBridgePhase) :
    bankCumulativeSDFAt (primitives G) (parentAllocation G) t h future =
      (99 / 100 : ℝ) ^ n := by
  have hpower : workerConsumption ^ (-(1 : ℝ)) ≠ 0 :=
    (Real.rpow_pos_of_pos workerConsumption_pos (-(1 : ℝ))).ne'
  unfold bankCumulativeSDFAt
  simp only [parent_workerConsumption]
  change (99 / 100 : ℝ) ^ n * workerConsumption ^ (-(1 : ℝ)) /
      workerConsumption ^ (-(1 : ℝ)) = (99 / 100 : ℝ) ^ n
  field_simp [hpower] <;> ring

theorem bank_survivalFactor_eq (G : ℝ) :
    1 - (primitives G).bankExit = (9 / 10 : ℝ) := by
  change 1 - (1 / 10 : ℝ) = 9 / 10
  norm_num

theorem parent_bankSurvivingValue_bounds
    (G : ℝ) (t : ℕ) (h : History LocalBridgePhase t) (n : ℕ) :
    0 ≤ bankSurvivingValueTermAt (primitives G) (parentAllocation G) t h
        (parentBankContinuation G t h) n ∧
      bankSurvivingValueTermAt (primitives G) (parentAllocation G) t h
        (parentBankContinuation G t h) n ≤
          bankEquity * (18711 / 20000 : ℝ) ^ n := by
  classical
  have hpoint : ∀ (future : Fin n → LocalBridgePhase)
      (payments : Fin n → (primitives G).paymentSupport),
      0 ≤ ((99 / 100 : ℝ) ^ n * (9 / 10 : ℝ) ^ n) *
          (parentBankContinuation G t h).equity n future payments ∧
      ((99 / 100 : ℝ) ^ n * (9 / 10 : ℝ) ^ n) *
          (parentBankContinuation G t h).equity n future payments ≤
        bankEquity * (18711 / 20000 : ℝ) ^ n := by
    intro future payments
    have he := parent_bankContinuation_equity_bounds G t h n future payments
    have hd : 0 ≤ (99 / 100 : ℝ) ^ n * (9 / 10 : ℝ) ^ n :=
      mul_nonneg (pow_nonneg (by norm_num) _) (pow_nonneg (by norm_num) _)
    constructor
    · exact mul_nonneg hd he.1.le
    · calc
        _ ≤ ((99 / 100 : ℝ) ^ n * (9 / 10 : ℝ) ^ n) *
            (bankEquity * (21 / 20 : ℝ) ^ n) :=
          mul_le_mul_of_nonneg_left he.2 hd
        _ = bankEquity * (18711 / 20000 : ℝ) ^ n := by
          have hproduct : (18711 / 20000 : ℝ) =
              (99 / 100 : ℝ) * (9 / 10 : ℝ) * (21 / 20 : ℝ) := by norm_num
          rw [hproduct, mul_pow, mul_pow]
          ring
  have hsum :
      bankSurvivingValueTermAt (primitives G) (parentAllocation G) t h
          (parentBankContinuation G t h) n =
        ∑ future : Fin n → LocalBridgePhase,
          ∑ payments : Fin n → (primitives G).paymentSupport,
            continuationTransitionWeight (primitives G).tree (currentState h) n future *
              continuationPaymentWeight (primitives G) payments *
              (((99 / 100 : ℝ) ^ n * (9 / 10 : ℝ) ^ n) *
                (parentBankContinuation G t h).equity n future payments) := by
    unfold bankSurvivingValueTermAt
    simp only [parent_bankCumulativeSDF, bank_survivalFactor_eq]
    apply Finset.sum_congr rfl
    intro future _hfuture
    apply Finset.sum_congr rfl
    intro payments _hpayments
    ring
  rw [hsum]
  exact continuationJointWeighted_bounds (primitives G) (currentState h) n
    (fun future payments ↦ ((99 / 100 : ℝ) ^ n * (9 / 10 : ℝ) ^ n) *
      (parentBankContinuation G t h).equity n future payments)
    (bankEquity * (18711 / 20000 : ℝ) ^ n) hpoint

theorem parent_bankPayoffTerm_zero
    (G : ℝ) (t : ℕ) (h : History LocalBridgePhase t) :
    bankContinuationPayoffTermAt (primitives G) (parentAllocation G) t h
      (parentBankContinuation G t h) 0 = 0 := by
  have hconsumption : 0 < (parentAllocation G).workerConsumption t h := by
    rw [parent_workerConsumption]
    exact workerConsumption_pos
  rw [bankContinuationPayoffTermAt_zero (primitives G) (parentAllocation G)
    t h (parentBankContinuation G t h) hconsumption]
  exact parent_bankContinuation_dividend_zero G t h 0 _ _

/-- La salida despues del retorno produce el objetivo positivo incluso
cuando no hay dividendos. Para n+1, eta/(1-eta)=1/9 exactamente. -/
theorem parent_bankPayoffTerm_succ
    (G : ℝ) (t : ℕ) (h : History LocalBridgePhase t) (n : ℕ) :
    bankContinuationPayoffTermAt (primitives G) (parentAllocation G) t h
        (parentBankContinuation G t h) (n + 1) =
      (1 / 9 : ℝ) * bankSurvivingValueTermAt (primitives G)
        (parentAllocation G) t h (parentBankContinuation G t h) (n + 1) := by
  classical
  have hn : n + 1 ≠ 0 := Nat.succ_ne_zero n
  unfold bankContinuationPayoffTermAt bankSurvivingValueTermAt
  simp only [parent_bankContinuation_dividend_zero, mul_zero, zero_add,
    hn, if_false, Nat.add_sub_cancel, bank_survivalFactor_eq]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro future _hfuture
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro payments _hpayments
  change continuationTransitionWeight (primitives G).tree (currentState h)
      (n + 1) future * continuationPaymentWeight (primitives G) payments *
      bankCumulativeSDFAt (primitives G) (parentAllocation G) t h future *
      ((9 / 10 : ℝ) ^ n * (1 / 10 : ℝ) *
        (parentBankContinuation G t h).equity (n + 1) future payments) =
    (1 / 9 : ℝ) *
      (continuationTransitionWeight (primitives G).tree (currentState h)
        (n + 1) future * continuationPaymentWeight (primitives G) payments *
        bankCumulativeSDFAt (primitives G) (parentAllocation G) t h future *
        (9 / 10 : ℝ) ^ (n + 1) *
        (parentBankContinuation G t h).equity (n + 1) future payments)
  rw [pow_succ]
  ring

theorem parent_bankPayoffTerm_bounds
    (G : ℝ) (t : ℕ) (h : History LocalBridgePhase t) (n : ℕ) :
    0 ≤ bankContinuationPayoffTermAt (primitives G) (parentAllocation G) t h
        (parentBankContinuation G t h) n ∧
      bankContinuationPayoffTermAt (primitives G) (parentAllocation G) t h
        (parentBankContinuation G t h) n ≤
          (bankEquity / 9) * (18711 / 20000 : ℝ) ^ n := by
  cases n with
  | zero =>
      rw [parent_bankPayoffTerm_zero, pow_zero, mul_one]
      exact ⟨le_rfl, div_nonneg bank_scale_pos.1.le (by norm_num)⟩
  | succ n =>
      rw [parent_bankPayoffTerm_succ]
      have hterminal := parent_bankSurvivingValue_bounds G t h (n + 1)
      constructor
      · exact mul_nonneg (by norm_num) hterminal.1
      · calc
          _ ≤ (1 / 9 : ℝ) * (bankEquity * (18711 / 20000 : ℝ) ^ (n + 1)) :=
            mul_le_mul_of_nonneg_left hterminal.2 (by norm_num)
          _ = (bankEquity / 9) * (18711 / 20000 : ℝ) ^ (n + 1) := by ring

theorem parent_bankContinuation_objective_and_terminal
    (G : ℝ) (t : ℕ) (h : History LocalBridgePhase t) :
    BankContinuationObjectiveWellDefinedAt (primitives G) (parentAllocation G)
        t h (parentBankContinuation G t h) ∧
      BankContinuationTerminalConditionAt (primitives G) (parentAllocation G)
        t h (parentBankContinuation G t h) := by
  apply bankContinuationObjectiveAndTerminal_of_weightedEnvelopes
    (primitives G) (parentAllocation G) t h (parentBankContinuation G t h)
    (bankEquity / 9) (18711 / 20000 : ℝ)
    bankEquity (18711 / 20000 : ℝ)
    (div_nonneg bank_scale_pos.1.le (by norm_num))
    (by norm_num) (by norm_num) bank_scale_pos.1.le (by norm_num) (by norm_num)
  · intro n
    have hbound := parent_bankPayoffTerm_bounds G t h n
    rw [abs_of_nonneg hbound.1]
    exact hbound.2
  · intro n
    have hbound := parent_bankSurvivingValue_bounds G t h n
    rw [abs_of_nonneg hbound.1]
    exact hbound.2

theorem parent_bankContinuation_feasible
    (G : ℝ) (t : ℕ) (h : History LocalBridgePhase t)
    (hh : FirmHistoryAdmissible (primitives G) t h) :
    BankContinuationFeasibleAt (primitives G) (parentAllocation G) t h bankEquity
      (parentBankContinuation G t h) := by
  have hequity : (commonBankPlan G).equity t h = bankEquity := by
    exact parent_bankEquity G t h
  rw [← hequity]
  apply bankContinuationPolicyFromPlan_feasible (primitives G) (inheritedState G)
    (parentAllocation G) (commonBankPlan G) t h hh (commonBankPlan_feasible G)
  · intro k H _hH
    exact fullRetentionCommonBankPlan_candidateFlows
      (primitives G) (parentAllocation G) k H
  · intro k H _hH
    rw [parent_reserveRate]
    have hRR := ProposedStationaryBank.reserveRate_spec.1
    linarith
  · intro k H _hH
    rw [parent_bankTightness]
    norm_num

theorem parent_bankContinuation_startsWithPlanAt
    (G : ℝ) (t : ℕ) (h : History LocalBridgePhase t) :
    BankContinuationStartsWithPlanAt (commonBankPlan G) t h
      (parentBankContinuation G t h) := by
  apply bankContinuationPolicyFromPlan_startsWithPlanAt
    (primitives G) (parentAllocation G) (commonBankPlan G) t h
  change (parentAllocation G).bankEquity t h ≠ 0
  rw [parent_bankEquity]
  exact ne_of_gt bank_scale_pos.1


/-! ## Resultado conjunto, separado de la comparacion con alternativas -/

/-- Objetivos y condiciones terminales de los tres problemas privados.
No se supone factibilidad para deducir convergencia ni se denomina a esta
conjuncion optimalidad. La factibilidad del hogar conserva su condicion
sobre G en el modulo anterior; la bancaria dinamica conserva hh arriba. -/
theorem parent_objectives_and_terminal (G : ℝ) :
    (∀ i, FirmObjectiveWellDefined (primitives G)
        (firmPlanOfAllocation (parentAllocation G) i) ∧
      FirmSourceTerminalCondition (primitives G) (parentAllocation G)
        (firmPlanOfAllocation (parentAllocation G) i)) ∧
    (HouseholdObjectiveWellDefined (primitives G)
        (householdPlanOfAllocation (parentAllocation G)) ∧
      HouseholdSourceTerminalCondition (primitives G)
        (householdPlanOfAllocation (parentAllocation G))) ∧
    (∀ (t : ℕ) (h : History LocalBridgePhase t),
      BankContinuationObjectiveWellDefinedAt (primitives G) (parentAllocation G)
        t h (parentBankContinuation G t h) ∧
      BankContinuationTerminalConditionAt (primitives G) (parentAllocation G)
        t h (parentBankContinuation G t h)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i
    exact ⟨parent_firmObjectiveWellDefined G i,
      parent_firmSourceTerminalCondition G i⟩
  · exact ⟨parent_householdObjectiveWellDefined G,
      parent_householdSourceTerminalCondition G⟩
  · intro t h
    exact parent_bankContinuation_objective_and_terminal G t h

end ProposedStationaryTerminal
end Ventura26LiquidityAllocation
