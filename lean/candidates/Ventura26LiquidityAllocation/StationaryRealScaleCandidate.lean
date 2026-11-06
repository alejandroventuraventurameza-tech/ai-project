import Ventura26LiquidityAllocation.InterbankCancellationCandidate

/-!
# Escala real del padre estacionario: PROPUESTA SIN COMPILAR

Proyecto: alejandroventuraventurameza-tech/ai-project.
Rama de referencia: work/chat-continuity.
Commit: 16e24fe828a5a0002ef13bb82bae9e295f190f86.
Base AppliedModelingLib: 194edcc95df74806a39b961d10dedddc6e730cce.
Lean previsto: leanprover/lean4:v4.30.0-rc2.
Mathlib fijado: 5450b53e5ddc75d46418fabb605edbf36bd0beb6.

Este modulo depende del candidato InterbankCancellationCandidate.lean,
incluido su namespace ProposedStationaryBank. Ninguno de los dos modulos
ha sido compilado en esta conversacion. Destino propuesto:
papers/Ventura26LiquidityAllocation/StationaryRealScaleCandidate.lean.
No se altera el checkpoint ni su import raiz.
SHA256 de la version utilizada de InterbankCancellationCandidate.lean:
98b9cc394719d54c56da4ad4b10c1e1487d5794c4709d1f03db57550eecf40ed

Fuentes: paper/paper.tex, sec:v0m_source_19 y sec:v0m_source_25;
code/irf/finite_irf.py, steady_case(), lineas 166--229.
Se interpretan las formulas como reales exactos. No se ejecuta Python,
no se identifica un flotante con una igualdad real, y no se repiten IRFs.

Orden matematico:
1. El resultado bancario previo da R=RL>1 y 4/25<rMD<1/6.
2. Para cada firma, g=1-theta*(39/40)/R>0 y
   f=1/40+theta*(39/40)*(1-1/R)>0. El costo de uso cumple
   u=q*(f+g/24)>0, con q=81/80.
3. Los coeficientes al salario unitario son positivos. Se construye
   w=(laborScale*workerConsumptionScale)^(1/12)>0.
4. k=kappa/w^5>0, b=theta*J*k/R>0 y
   c=(u/4+q*g/24)*k>0. J=(39/40)*q=3159/3200.
5. La expresion de consumo trabajador por recursos se reescribe como
   CW=(7/12)*Y+K/6400+(R-1)*B>0.
6. E=B/(3-2*rMD)>0, D=2*E>0 y M=2*rMD*E>0.

Las letras Scale designan coeficientes al salario unitario, no fechas.
profitCoefficient tampoco es consumo empresarial.

Se construyen los portadores exactos stateSix, controls y dateData, y
se demuestra su dominio positivo y la cancelacion bancaria del punto.
No se construye un Primitives completo ni un InheritedState fiscal.
No se afirma que todas las ecuaciones reducidas se anulen, ni que exista
una continuacion, ni optimalidad, terminalidad o equilibrio completo.
El punto padre tiene ambas garantias empresariales activas. No se usa
como sustituto del prefijo S: sus condiciones empresariales son distintas.
Las ramas S y B del proyecto se conservan.
-/

namespace Ventura26LiquidityAllocation
namespace ProposedStationaryRealScale

noncomputable def pledgeability : FirmType → ℝ
  | .H => 3 / 20
  | .L => 2 / 5

noncomputable def technology : FirmType → ℝ
  | .H => 101 / 100
  | .L => 1

noncomputable def capitalPrice : ℝ := 81 / 80

noncomputable def liquidationValue : ℝ := (39 / 40) * capitalPrice

noncomputable def financingFraction (i : FirmType) : ℝ :=
  1 - pledgeability i * (39 / 40) / ProposedStationaryBank.loanRate

noncomputable def expenditurePerCapital (i : FirmType) : ℝ :=
  1 / 40 + pledgeability i * (39 / 40) *
    (1 - 1 / ProposedStationaryBank.loanRate)

noncomputable def userCost (i : FirmType) : ℝ :=
  capitalPrice *
    ((1 - pledgeability i * (39 / 40) / ProposedStationaryBank.loanRate) /
      (24 / 25) - (39 / 40) * (1 - pledgeability i))

noncomputable def profitCoefficient (i : FirmType) : ℝ :=
  ((5 / 6) * technology i) ^ (2 : ℕ) / 4

noncomputable def capitalScale (i : FirmType) : ℝ :=
  ((4 / 5) * profitCoefficient i / userCost i) ^ (5 : ℕ)

noncomputable def average (f : FirmType → ℝ) : ℝ :=
  (f .H + f .L) / 2

noncomputable def outputScale : ℝ :=
  average (fun i ↦ userCost i * capitalScale i / (1 / 3))

noncomputable def laborScale : ℝ :=
  average (fun i ↦ (5 / 4) * userCost i * capitalScale i)

noncomputable def creditScale : ℝ :=
  average (fun i ↦ pledgeability i * liquidationValue * capitalScale i /
    ProposedStationaryBank.loanRate)

noncomputable def workerConsumptionScale : ℝ :=
  (7 / 12) * outputScale + average capitalScale / 6400 +
    (ProposedStationaryBank.loanRate - 1) * creditScale

noncomputable def wage : ℝ :=
  (laborScale * workerConsumptionScale) ^ (1 / 12 : ℝ)

noncomputable def capital (i : FirmType) : ℝ :=
  capitalScale i / wage ^ (5 : ℕ)

noncomputable def output (i : FirmType) : ℝ :=
  userCost i * capital i / (1 / 3)

noncomputable def labor (i : FirmType) : ℝ :=
  (5 / 4) * userCost i * capital i / wage

noncomputable def profit (i : FirmType) : ℝ := (5 / 12) * output i

noncomputable def firmFace (i : FirmType) : ℝ :=
  pledgeability i * liquidationValue * capital i

noncomputable def loan (i : FirmType) : ℝ :=
  firmFace i / ProposedStationaryBank.loanRate

noncomputable def firmConsumption (i : FirmType) : ℝ :=
  profit i - (1 / 40) * capitalPrice * capital i -
    (ProposedStationaryBank.loanRate - 1) * loan i

noncomputable def aggregateCapital : ℝ := average capital

noncomputable def aggregateOutput : ℝ := average output

noncomputable def aggregateLabor : ℝ := average labor

noncomputable def aggregateCredit : ℝ := average loan

/-- La expresion original por recursos, antes de probar su signo. -/
noncomputable def workerConsumption : ℝ :=
  aggregateOutput - average firmConsumption - (161 / 6400) * aggregateCapital

noncomputable def bankEquity : ℝ :=
  aggregateCredit / (3 - 2 * ProposedStationaryBank.reserveDepositRatio)

noncomputable def bankDeposits : ℝ := 2 * bankEquity

noncomputable def reservesPre : ℝ :=
  2 * ProposedStationaryBank.reserveDepositRatio * bankEquity

theorem average_pos (f : FirmType → ℝ) (hf : ∀ i, 0 < f i) :
    0 < average f :=
  div_pos (add_pos (hf .H) (hf .L)) (by norm_num)

theorem pledgeability_bounds (i : FirmType) :
    0 < pledgeability i ∧ pledgeability i < 1 := by
  cases i <;> norm_num [pledgeability]

theorem technology_pos (i : FirmType) : 0 < technology i := by
  cases i <;> norm_num [technology]

theorem loanRate_gt_one : 1 < ProposedStationaryBank.loanRate := by
  rcases ProposedStationaryBank.bank_margins_and_pricing with
    ⟨_hxi0, _hxiupper, _hratio0, _hratio1, _hpricing, hloan, _hloanupper⟩
  norm_num [ProposedStationaryBank.depositRate] at hloan
  linarith

theorem loanRate_pos : 0 < ProposedStationaryBank.loanRate := by
  have h := loanRate_gt_one
  linarith

theorem capitalPrice_pos : 0 < capitalPrice := by norm_num [capitalPrice]

theorem liquidationValue_pos : 0 < liquidationValue := by
  norm_num [liquidationValue, capitalPrice]

/-- PROPUESTO, SIN COMPILAR. La positividad del costo de uso precede a
la eleccion del salario y del capital. -/
theorem financing_and_expenditure_pos (i : FirmType) :
    0 < financingFraction i ∧ 0 < expenditurePerCapital i := by
  rcases pledgeability_bounds i with ⟨htheta0, htheta1⟩
  have hR := loanRate_gt_one
  have hR0 := loanRate_pos
  have hthetaProduct : pledgeability i * (39 / 40) < 1 := by nlinarith
  have hfin : pledgeability i * (39 / 40) / ProposedStationaryBank.loanRate < 1 :=
    (div_lt_one hR0).2 (by linarith)
  have hinv : 1 / ProposedStationaryBank.loanRate < 1 :=
    (div_lt_one hR0).2 hR
  have hinvGap : 0 < 1 - 1 / ProposedStationaryBank.loanRate := by linarith
  constructor
  · unfold financingFraction
    linarith
  · unfold expenditurePerCapital
    positivity

theorem userCost_decomposition (i : FirmType) :
    userCost i = capitalPrice *
      (expenditurePerCapital i + financingFraction i / 24) := by
  unfold userCost expenditurePerCapital financingFraction
  field_simp [ne_of_gt loanRate_pos] <;> ring

theorem userCost_pos (i : FirmType) : 0 < userCost i := by
  rcases financing_and_expenditure_pos i with ⟨hg, hf⟩
  have hq := capitalPrice_pos
  rw [userCost_decomposition]
  positivity

theorem profitCoefficient_pos (i : FirmType) : 0 < profitCoefficient i := by
  have hA := technology_pos i
  unfold profitCoefficient
  positivity

theorem capitalScale_pos (i : FirmType) : 0 < capitalScale i := by
  have hu := userCost_pos i
  have hC := profitCoefficient_pos i
  unfold capitalScale
  positivity

theorem aggregate_scales_pos :
    0 < average capitalScale ∧ 0 < outputScale ∧ 0 < laborScale ∧
    0 < creditScale ∧ 0 < workerConsumptionScale := by
  have hK := average_pos capitalScale capitalScale_pos
  have hY : 0 < outputScale := by
    apply average_pos
    intro i
    have hu := userCost_pos i
    have hk := capitalScale_pos i
    positivity
  have hL : 0 < laborScale := by
    apply average_pos
    intro i
    have hu := userCost_pos i
    have hk := capitalScale_pos i
    positivity
  have hB : 0 < creditScale := by
    apply average_pos
    intro i
    have htheta := (pledgeability_bounds i).1
    have hJ := liquidationValue_pos
    have hk := capitalScale_pos i
    have hR := loanRate_pos
    positivity
  have hC : 0 < workerConsumptionScale := by
    have hR : 0 < ProposedStationaryBank.loanRate - 1 :=
      sub_pos.mpr loanRate_gt_one
    unfold workerConsumptionScale
    positivity
  exact ⟨hK, hY, hL, hB, hC⟩

theorem wage_pos : 0 < wage := by
  rcases aggregate_scales_pos with ⟨_hK, _hY, hL, _hB, hC⟩
  exact Real.rpow_pos_of_pos (mul_pos hL hC) (1 / 12 : ℝ)

/-- PROPUESTO, SIN COMPILAR. La potencia real elegida es una raiz exacta. -/
theorem wage_pow_twelve :
    wage ^ (12 : ℕ) = laborScale * workerConsumptionScale := by
  rcases aggregate_scales_pos with ⟨_hK, _hY, hL, _hB, hC⟩
  have hprod := mul_pos hL hC
  calc
    wage ^ (12 : ℕ) =
        ((laborScale * workerConsumptionScale) ^ (1 / 12 : ℝ)) ^ (12 : ℝ) := by
      exact (Real.rpow_natCast
        ((laborScale * workerConsumptionScale) ^ (1 / 12 : ℝ)) 12).symm
    _ = (laborScale * workerConsumptionScale) ^ ((1 / 12 : ℝ) * 12) :=
      (Real.rpow_mul hprod.le (1 / 12 : ℝ) (12 : ℝ)).symm
    _ = laborScale * workerConsumptionScale := by norm_num

theorem capital_pos (i : FirmType) : 0 < capital i :=
  div_pos (capitalScale_pos i) (pow_pos wage_pos 5)

theorem output_pos (i : FirmType) : 0 < output i := by
  have hu := userCost_pos i
  have hk := capital_pos i
  unfold output
  positivity

theorem labor_pos (i : FirmType) : 0 < labor i := by
  have hu := userCost_pos i
  have hk := capital_pos i
  have hw := wage_pos
  unfold labor
  positivity

theorem firmFace_pos (i : FirmType) : 0 < firmFace i := by
  have htheta := (pledgeability_bounds i).1
  have hJ := liquidationValue_pos
  have hk := capital_pos i
  unfold firmFace
  positivity

theorem loan_pos (i : FirmType) : 0 < loan i :=
  div_pos (firmFace_pos i) loanRate_pos

/-- PROPUESTO, SIN COMPILAR. La expresion original del consumo se
identifica con una suma positiva; no se postula el signo del residual. -/
theorem firmConsumption_decomposition (i : FirmType) :
    firmConsumption i =
      (userCost i / 4 + capitalPrice * financingFraction i / 24) * capital i := by
  unfold firmConsumption profit output loan firmFace liquidationValue
    userCost financingFraction
  field_simp [ne_of_gt loanRate_pos] <;> ring

theorem firmConsumption_pos (i : FirmType) : 0 < firmConsumption i := by
  have hu := userCost_pos i
  have hq := capitalPrice_pos
  have hg := (financing_and_expenditure_pos i).1
  have hk := capital_pos i
  rw [firmConsumption_decomposition]
  positivity

theorem aggregates_pos :
    0 < aggregateCapital ∧ 0 < aggregateOutput ∧
    0 < aggregateLabor ∧ 0 < aggregateCredit :=
  ⟨average_pos capital capital_pos, average_pos output output_pos,
    average_pos labor labor_pos, average_pos loan loan_pos⟩

/-- PROPUESTO, SIN COMPILAR. Mantiene la definicion por recursos del script. -/
theorem workerConsumption_resource_identity :
    workerConsumption = (7 / 12) * aggregateOutput +
      aggregateCapital / 6400 +
      (ProposedStationaryBank.loanRate - 1) * aggregateCredit := by
  unfold workerConsumption aggregateOutput aggregateCapital aggregateCredit
    average firmConsumption profit capitalPrice
  ring

theorem workerConsumption_pos : 0 < workerConsumption := by
  rcases aggregates_pos with ⟨hK, hY, _hL, hB⟩
  have hR : 0 < ProposedStationaryBank.loanRate - 1 :=
    sub_pos.mpr loanRate_gt_one
  rw [workerConsumption_resource_identity]
  positivity

/-- PROPUESTO, SIN COMPILAR. Coeficientes al salario unitario y cantidades
finales coinciden por sus definiciones, sin comparaciones numericas. -/
theorem aggregateCapital_scale :
    aggregateCapital = average capitalScale / wage ^ (5 : ℕ) := by
  unfold aggregateCapital average capital
  ring

theorem aggregateOutput_scale :
    aggregateOutput = outputScale / wage ^ (5 : ℕ) := by
  unfold aggregateOutput outputScale average output capital
  ring

theorem aggregateCredit_scale :
    aggregateCredit = creditScale / wage ^ (5 : ℕ) := by
  unfold aggregateCredit creditScale average loan firmFace capital
  ring

theorem aggregateLabor_scale :
    aggregateLabor = laborScale / wage ^ (6 : ℕ) := by
  unfold aggregateLabor laborScale average labor capital
  field_simp [ne_of_gt wage_pos] <;> ring

theorem workerConsumption_scale :
    workerConsumption = workerConsumptionScale / wage ^ (5 : ℕ) := by
  rw [workerConsumption_resource_identity, aggregateOutput_scale,
    aggregateCapital_scale, aggregateCredit_scale]
  unfold workerConsumptionScale
  ring

/-- PROPUESTO, SIN COMPILAR. Cierre salarial de las formulas escalares.
Su identificacion con localPrefixLabor/Output requiere aun fijar las
primitivas reales y demostrar el puente de produccion correspondiente. -/
theorem worker_labor_equation : wage = workerConsumption * aggregateLabor := by
  symm
  calc
    workerConsumption * aggregateLabor =
        workerConsumptionScale * laborScale / wage ^ (11 : ℕ) := by
      rw [workerConsumption_scale, aggregateLabor_scale]
      field_simp [ne_of_gt wage_pos] <;> ring
    _ = wage := by
      apply (div_eq_iff (pow_ne_zero 11 (ne_of_gt wage_pos))).2
      calc
        workerConsumptionScale * laborScale = wage ^ (12 : ℕ) := by
          rw [wage_pow_twelve]
          ring
        _ = wage * wage ^ (11 : ℕ) := by ring

/-- PROPUESTO, SIN COMPILAR. E y M son cantidades construidas, sin
hipotesis independiente E>0, B>0 ni M>0. -/
theorem bank_scale_pos :
    0 < bankEquity ∧ 0 < bankDeposits ∧ 0 < reservesPre := by
  have hB := aggregates_pos.2.2.2
  rcases ProposedStationaryBank.bank_margins_and_pricing with
    ⟨_hxi0, _hxiupper, hrlo, hrhi, _hpricing, _hloanlo, _hloanhi⟩
  have hr : 0 < ProposedStationaryBank.reserveDepositRatio := by linarith
  have hden : 0 < 3 - 2 * ProposedStationaryBank.reserveDepositRatio := by linarith
  have hE : 0 < bankEquity := div_pos hB hden
  have hD : 0 < bankDeposits := by unfold bankDeposits; positivity
  have hM : 0 < reservesPre := by unfold reservesPre; positivity
  exact ⟨hE, hD, hM⟩

theorem bank_balance : aggregateCredit + reservesPre = bankEquity + bankDeposits := by
  rcases ProposedStationaryBank.bank_margins_and_pricing with
    ⟨_hxi0, _hxiupper, _hrlo, hrhi, _hpricing, _hloanlo, _hloanhi⟩
  have hden : 0 < 3 - 2 * ProposedStationaryBank.reserveDepositRatio := by linarith
  unfold reservesPre bankDeposits bankEquity
  field_simp [ne_of_gt hden] <;> ring

/-- El patrimonio nominal coincide con E porque el control de inflacion
de este punto se fija en uno. No se identifica con patrimonio pre-salida. -/
noncomputable def stateSix : LocalPrefixStateSix where
  capitalH := capital .H
  capitalL := capital .L
  commonPledgeValue := liquidationValue
  bankFace := bankEquity
  reserveRateLag := ProposedStationaryBank.reserveRate
  reservesPreLag := reservesPre

noncomputable def controls : LocalPrefixControlsTen where
  consumptionH := firmConsumption .H
  consumptionL := firmConsumption .L
  workerConsumption := workerConsumption
  wage := wage
  inputPrice := 5 / 6
  inflation := 1
  capitalPrice := capitalPrice
  depositRate := ProposedStationaryBank.depositRate
  loanRate := ProposedStationaryBank.loanRate
  tightness := 1 / 2

/-- Dato de una fecha estacionaria. No es por si mismo una solucion de
LocalReducedPrefixEquationsHold ni una ley de continuacion. -/
noncomputable def dateData : LocalPrefixDateData where
  currentCapital := capital
  inheritedFace := firmFace
  currentBankFace := bankEquity
  lagReserveRate := ProposedStationaryBank.reserveRate
  lagReservesPre := reservesPre
  controls := controls
  nextCapital := capital
  nextFace := firmFace
  nextBankFace := bankEquity
  currentReserveRate := ProposedStationaryBank.reserveRate
  currentReservesPre := reservesPre
  nextControls := controls
  currentAggregateProductivity := 1
  nextAggregateProductivity := 1
  reserveRateInnovation := 0
  reserveQuantityInnovation := 0
  reserveRequirement := 1 / 10
  corridorWidth := 1 / 50

theorem stateSix_positive : LocalPrefixStateSixPositive stateSix := by
  intro j
  have hkH := capital_pos .H
  have hkL := capital_pos .L
  have hJ := liquidationValue_pos
  have hE := bank_scale_pos.1
  have hRR := ProposedStationaryBank.reserveRate_spec.1
  have hM := bank_scale_pos.2.2
  fin_cases j <;> simp only [localPrefixStateSixVector, stateSix] <;> linarith

theorem controls_positive :
    ∀ j, 0 < localPrefixControlsTenVector controls j := by
  intro j
  have hcH := firmConsumption_pos .H
  have hcL := firmConsumption_pos .L
  have hCW := workerConsumption_pos
  have hw := wage_pos
  have hq := capitalPrice_pos
  have hRD : 0 < ProposedStationaryBank.depositRate := by
    norm_num [ProposedStationaryBank.depositRate]
  have hRL := loanRate_pos
  fin_cases j <;> simp only [localPrefixControlsTenVector, controls] <;> norm_num <;>
    linarith

/-- PROPUESTO, SIN COMPILAR. Identifica las promesas del portador conservado
cuando P tiene las garantias del testigo. No afirma realizacion por equilibrio. -/
theorem stateSix_faces
    {S : Type*} [Fintype S] (P : Primitives S)
    (hpledge : ∀ i, P.pledgeability i = pledgeability i) :
    localPrefixStateSixFace P stateSix = firmFace := by
  funext i
  cases i <;> simp [localPrefixStateSixFace, stateSix, firmFace, hpledge]

/-- PROPUESTO, SIN COMPILAR. Encaje del dato explicito con el constructor
recurrente conservado, cuando se fijan sus entradas recurrentes.
La igualdad de constructores no afirma ecuaciones de equilibrio. -/
theorem recurrent_dateData_eq
    (P : Primitives LocalBridgePhase)
    (hpledge : ∀ i, P.pledgeability i = pledgeability i)
    (hproductivity : P.aggregateProductivity .recurrent = 1)
    (hrateInnovation : P.reserveRateInnovation .recurrent = 0)
    (hquantityInnovation : P.reserveQuantityInnovation .recurrent = 0)
    (n : ℕ)
    (hrequirement :
      P.reserveRequirementPath (n + 2) (localBridgeHistory (n + 2)) = 1 / 10)
    (hwidth :
      P.corridorWidthPath (n + 2) (localBridgeHistory (n + 2)) = 1 / 50) :
    localRecurrentDateData P (fun _ ↦ stateSix) (fun _ ↦ controls) n =
      dateData := by
  have hcapital : localPrefixStateSixCapital stateSix = capital := by
    funext i
    cases i <;> rfl
  have hfaces := stateSix_faces P hpledge
  simp only [localRecurrentDateData, hcapital, hfaces, hproductivity,
    hrateInnovation, hquantityInnovation, hrequirement, hwidth, dateData]

/-- PROPUESTO, SIN COMPILAR. La razon eliminada coincide con la razon
exacta del bloque bancario; se utiliza el lema conservado del momento binario. -/
theorem reducedReserveDepositRatio_eq
    {S : Type*} [Fintype S] (P : Primitives S)
    (paymentMinus paymentPlus : BankPayment)
    (hbinary : BinarySymmetricPaymentLaw P paymentMinus paymentPlus (1 / 5)) :
    localPrefixReserveDepositRatio P dateData =
      ProposedStationaryBank.reserveDepositRatio := by
  classical
  rw [localPrefixReserveDepositRatio,
    localPrefixMeanAbsolutePaymentShock_eq_of_binarySymmetric
      P paymentMinus paymentPlus (1 / 5) hbinary]
  simp only [dateData, controls]
  unfold ProposedStationaryBank.reserveDepositRatio
  ring

theorem reducedBankDeposits_eq
    {S : Type*} [Fintype S] (P : Primitives S)
    (paymentMinus paymentPlus : BankPayment)
    (hbinary : BinarySymmetricPaymentLaw P paymentMinus paymentPlus (1 / 5)) :
    localPrefixReducedBankDeposits P dateData = bankDeposits := by
  rcases ProposedStationaryBank.bank_margins_and_pricing with
    ⟨_hxi0, _hxiupper, hrlo, _hrhi, _hpricing, _hloanlo, _hloanhi⟩
  have hr : 0 < ProposedStationaryBank.reserveDepositRatio := by linarith
  unfold localPrefixReducedBankDeposits
  rw [reducedReserveDepositRatio_eq P paymentMinus paymentPlus hbinary]
  change reservesPre / ProposedStationaryBank.reserveDepositRatio = bankDeposits
  unfold reservesPre bankDeposits
  field_simp [ne_of_gt hr] <;> ring

theorem reducedBankEquity_eq :
    localPrefixReducedBankEquity dateData = bankEquity := by
  norm_num [localPrefixReducedBankEquity, dateData, controls]

/-- PROPUESTO, SIN COMPILAR. El credito real reconstruido coincide con el
agregado exacto, usando las masas de la fuente y las promesas nominales. -/
theorem reducedBankLoans_eq
    {S : Type*} [Fintype S] (P : Primitives S)
    (hmass : ∀ i, P.mass i = 1 / 2) :
    localPrefixReducedBankLoans P dateData = aggregateCredit := by
  unfold localPrefixReducedBankLoans
  rw [sum_firmType_eq_H_add_L]
  simp only [dateData, controls, hmass]
  unfold aggregateCredit average loan
  ring

/-- PROPUESTO, SIN COMPILAR. La fila de balance resulta de las cantidades
construidas; su anulacion no es una hipotesis. -/
theorem reduced_bank_balance_row
    {S : Type*} [Fintype S] (P : Primitives S)
    (paymentMinus paymentPlus : BankPayment)
    (hbinary : BinarySymmetricPaymentLaw P paymentMinus paymentPlus (1 / 5))
    (hmass : ∀ i, P.mass i = 1 / 2) :
    localReducedRemainingResidual P dateData 10 = 0 := by
  have hratio := reducedReserveDepositRatio_eq P paymentMinus paymentPlus hbinary
  have hdeposits := reducedBankDeposits_eq P paymentMinus paymentPlus hbinary
  have hquotient : reservesPre / ProposedStationaryBank.reserveDepositRatio =
      bankDeposits := by
    change reservesPre / localPrefixReserveDepositRatio P dateData = bankDeposits
      at hdeposits
    rw [hratio] at hdeposits
    exact hdeposits
  have hcapacity :
      (1 / ProposedStationaryBank.reserveDepositRatio - 1) * reservesPre =
        bankDeposits - reservesPre := by
    calc
      (1 / ProposedStationaryBank.reserveDepositRatio - 1) * reservesPre =
          reservesPre / ProposedStationaryBank.reserveDepositRatio - reservesPre := by
        ring
      _ = bankDeposits - reservesPre := by rw [hquotient]
  change localPrefixReducedBankLoans P dateData -
    (localPrefixReducedBankEquity dateData +
      (1 / localPrefixReserveDepositRatio P dateData - 1) * reservesPre) = 0
  rw [reducedBankLoans_eq P hmass, reducedBankEquity_eq, hratio, hcapacity]
  have hbalance := bank_balance
  linarith

/-- PROPUESTO, SIN COMPILAR. La cancelacion del punto construido ya no
recibe M>0 ni E>0 como hipotesis. Falta probar que una trayectoria dinamica
sea este punto o satisfaga sus propias cotas en cada fecha. -/
theorem stationary_expectedInterbank_eq_zero
    (P : Primitives LocalBridgePhase)
    (paymentMinus paymentPlus : BankPayment)
    (hbinary : BinarySymmetricPaymentLaw P paymentMinus paymentPlus (1 / 5))
    (t : ℕ) (h : History LocalBridgePhase t)
    (hrequirement : P.reserveRequirementPath t h = 1 / 10) :
    localSlackExpectedInterbank P (fun _ ↦ dateData) t h = 0 := by
  rcases ProposedStationaryBank.localPrefix_bank_domain
    P dateData paymentMinus paymentPlus hbinary rfl rfl rfl rfl with
    ⟨htau, hRR, hxi, hratio, _hratioUpper⟩
  refine proposed_localSlackExpectedInterbank_eq_zero_of_binarySymmetric
    P (fun _ ↦ dateData) paymentMinus paymentPlus (1 / 5) hbinary t h
    htau bank_scale_pos.2.2 ?_ hRR hxi hrequirement
  linarith

end ProposedStationaryRealScale
end Ventura26LiquidityAllocation
