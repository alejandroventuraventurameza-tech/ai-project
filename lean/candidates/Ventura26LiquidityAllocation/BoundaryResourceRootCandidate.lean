import Ventura26LiquidityAllocation.BoundaryFirmBridgeCandidate
import Ventura26LiquidityAllocation.PaperInterface
import Mathlib.Topology.Order.IntermediateValue

/-!
# Residual literal de recursos y raiz del enlace: PROPUESTA SIN COMPILAR

Proyecto: alejandroventuraventurameza-tech/ai-project.
Rama: work/chat-continuity.
Commit: 16e24fe828a5a0002ef13bb82bae9e295f190f86.
AppliedModelingLib: 194edcc95df74806a39b961d10dedddc6e730cce.
Mathlib: 5450b53e5ddc75d46418fabb605edbf36bd0beb6.
Lean previsto: leanprover/lean4:v4.30.0-rc2.

Dependencia propuesta BoundaryFirmBridgeCandidate.lean SHA256:
669a77eae0ebae4fb1ccfc16d30eb2a711b1ce47be9a6f4d83c107678affa44f.

Objetivo de este modulo:
1. Reemplazar el carrier Phi libre de boundaryEquilibriumSpec por el residual
   economico literal de recursos del enlace.
2. Separar la prueba analitica de unicidad de la evidencia computacional de
   signos en los extremos.
3. Exponer un contrato pequeno para internalizar posteriormente el certificado
   de aritmetica intervalar; este archivo NO convierte JSON en teorema Lean.

Fuentes numericas archivadas, no reejecutadas aqui:
code/v0m/cierre_interno_2026_10_17/finite_bridge.py
code/v0m/cierre_interno_2026_10_17/finite_bridge_certificate.json
code/v0m/verification_report.json

El certificado archivado usa Decimal con redondeo dirigido y registra:
Phi(1.025)<0, Phi(1.032)>0 y Phi'(R)>0 en todo el intervalo, ademas de una
caja estrecha para la raiz. Es evidencia intervalar reproducida historicamente,
NO una prueba del kernel de Lean.

La unicidad no necesita la cota intervalar de Phi'. Matematicamente puede
probarse por monotonia:
- la tasa de deposito de frontera crece con R;
- el consumo trabajador decrece;
- la escala de capital crece;
- ambos consumos empresariales decrecen;
- el costo de creacion de capital decrece;
- la produccion agregada crece por homogeneidad.
Luego Phi = Y-CW-sum_i v_i c_i-Gamma es estrictamente creciente.

Este modulo es un CANDIDATO SIN COMPILAR. No contiene sorry/admit/axiom.
-/

open scoped BigOperators
open Set

namespace Ventura26LiquidityAllocation
namespace ProposedBoundaryResourceRoot

open ProposedStationaryBank
open ProposedStationaryRealScale
open ProposedStationaryPrimitives
open ProposedBoundaryBridge

/-! ## Intervalo y formulas cerradas del enlace -/

noncomputable def boundaryLo : ℝ := 41 / 40

noncomputable def boundaryHi : ℝ := 129 / 125

def boundaryInterval : Set ℝ := Set.Icc boundaryLo boundaryHi

theorem boundaryLo_lt_boundaryHi : boundaryLo < boundaryHi := by
  norm_num [boundaryLo, boundaryHi]

noncomputable def boundaryReserveRate (R : ℝ) : ℝ :=
  R - meanSlope

/-- b = zeta * slopeGap / 2 = slopeGap / 10. -/
noncomputable def boundaryPaymentTerm : ℝ := slopeGap / 10

/-- Formula de precios de depositos de la frontera, con rho=1/10,
    zeta=1/5 y tightness=1/2. -/
noncomputable def boundaryDepositRate (R : ℝ) : ℝ :=
  let rr := boundaryReserveRate R
  (rr + (9 / 10) * meanSlope + (1 / 10) * boundaryPaymentTerm) /
    (1 + boundaryPaymentTerm / rr)

/-- Escala comun del capital corriente, con capital futuro estacionario. -/
noncomputable def boundaryCapitalScale (R : ℝ) : ℝ :=
  1 / ((39 / 40) + (boundaryCapitalPrice R - 1) / (1 / 2))

noncomputable def boundaryCapital (R : ℝ) (i : FirmType) : ℝ :=
  boundaryCapitalScale R * capital i

noncomputable def boundaryAggregateCapital (R : ℝ) : ℝ :=
  boundaryCapitalScale R * aggregateCapital

noncomputable def boundaryInvestment (R : ℝ) : ℝ :=
  aggregateCapital - (39 / 40) * boundaryAggregateCapital R

noncomputable def boundaryCapitalCost (R : ℝ) : ℝ :=
  boundaryInvestment R + (1 / 2) * boundaryInvestment R ^ 2 /
    (2 * boundaryAggregateCapital R)

noncomputable def boundaryWorkerConsumption (R : ℝ) : ℝ :=
  workerConsumption / ((99 / 100) * boundaryDepositRate R)

noncomputable def boundaryWage (R : ℝ) : ℝ :=
  wage *
    ((boundaryWorkerConsumption R / workerConsumption) *
      boundaryCapitalScale R ^ (4 / 5 : ℝ)) ^ (1 / 3 : ℝ)

noncomputable def boundaryLabor (R : ℝ) (i : FirmType) : ℝ :=
  ((1 / 2) * (5 / 6) * technology i *
      boundaryCapital R i ^ (2 / 5 : ℝ) / boundaryWage R) ^
    (1 / (1 - (1 / 2 : ℝ)) : ℝ)

noncomputable def boundaryOutput (R : ℝ) (i : FirmType) : ℝ :=
  operatingOutput (technology i) (boundaryCapital R i)
    (boundaryLabor R i) (2 / 5) (1 / 2)

noncomputable def boundaryAggregateOutput (R : ℝ) : ℝ :=
  average (boundaryOutput R)

/-- El residual del articulo, con signo output minus absorption. -/
noncomputable def boundaryResourceResidual (R : ℝ) : ℝ :=
  boundaryAggregateOutput R - boundaryWorkerConsumption R -
    average (boundaryConsumption R) - boundaryCapitalCost R

/-! ## Portador literal del modelo -/

noncomputable def boundaryControls (R : ℝ) : LocalPrefixControlsTen :=
  { ProposedStationaryRealScale.controls with
    consumptionH := boundaryConsumption R .H
    consumptionL := boundaryConsumption R .L
    workerConsumption := boundaryWorkerConsumption R
    wage := boundaryWage R
    inputPrice := 5 / 6
    inflation := 1
    capitalPrice := boundaryCapitalPrice R
    depositRate := boundaryDepositRate R
    loanRate := R
    tightness := 1 / 2 }

noncomputable def boundaryDateTemplate (R : ℝ) : LocalPrefixDateData :=
  { ProposedStationaryRealScale.dateData with
    currentCapital := boundaryCapital R
    controls := boundaryControls R
    nextCapital := capital
    nextFace := firmFace
    nextControls := ProposedStationaryRealScale.controls
    currentAggregateProductivity := 1
    nextAggregateProductivity := 1 }

/-- Se reutiliza el constructor del bloque empresarial para definir las
    promesas heredadas por el presupuesto, sin alterar los campos agregados. -/
noncomputable def boundaryDateData (G R : ℝ) : LocalPrefixDateData :=
  boundaryFirmDateData G R (boundaryDateTemplate R)

/-- El carrier economico literal: solo usa funciones del modelo conservado. -/
noncomputable def boundaryLiteralResourceResidual (G R : ℝ) : ℝ :=
  let d := boundaryDateData G R
  localPrefixAggregateOutput (primitives G) d -
    d.controls.workerConsumption -
    (∑ i, (primitives G).mass i * localPrefixFirmConsumption d.controls i) -
    localPrefixCapitalCost (primitives G) d

/-- PROPUESTO, SIN COMPILAR. Fija el signo entre la fila 2 del sistema reducido
    y el residual de recursos del articulo. Inflation=1 elimina Rotemberg. -/
theorem boundary_row_two_eq_neg_literal (G R : ℝ) :
    localReducedRemainingResidual (primitives G) (boundaryDateData G R) 2 =
      - boundaryLiteralResourceResidual G R := by
  unfold boundaryLiteralResourceResidual localReducedRemainingResidual
    localPrefixRotembergCost
  simp [boundaryDateData, boundaryDateTemplate, boundaryControls,
    boundaryFirmDateData, boundaryFirmDateSeed, boundaryFirmControls]
  ring

/-- PROPUESTO, SIN COMPILAR. Identifica el carrier literal con las formulas
    cerradas de la construccion escalar. Esta es la igualdad que elimina la
    funcion Phi libre del contrato del articulo. -/
theorem boundary_literal_eq_closed (G R : ℝ) :
    boundaryLiteralResourceResidual G R = boundaryResourceResidual R := by
  -- The source reduced system uses literal weighted sums.  The closed
  -- residual uses the same two-point mean, but its inputs have first
  -- been reconstructed from the reduced candidate.
  have hcapitalCurrent :
      localPrefixAggregateCapital (primitives G)
          (boundaryDateData G R).currentCapital =
        boundaryAggregateCapital R := by
    unfold localPrefixAggregateCapital
    rw [sum_firmType_eq_H_add_L]
    change (1 / 2 : ℝ) * boundaryCapital R .H +
      (1 / 2 : ℝ) * boundaryCapital R .L = boundaryAggregateCapital R
    unfold boundaryAggregateCapital boundaryCapital aggregateCapital average
    ring
  have hcapitalNext :
      localPrefixAggregateCapital (primitives G)
          (boundaryDateData G R).nextCapital = aggregateCapital := by
    unfold localPrefixAggregateCapital
    rw [sum_firmType_eq_H_add_L]
    change (1 / 2 : ℝ) * capital .H +
      (1 / 2 : ℝ) * capital .L = aggregateCapital
    unfold aggregateCapital average
    ring
  have hinvestment :
      localPrefixInvestment (primitives G) (boundaryDateData G R) =
        boundaryInvestment R := by
    unfold localPrefixInvestment
    rw [hcapitalNext, hcapitalCurrent]
    change aggregateCapital - (1 - (1 / 40 : ℝ)) *
      boundaryAggregateCapital R = boundaryInvestment R
    unfold boundaryInvestment
    ring
  have hcapitalCost :
      localPrefixCapitalCost (primitives G) (boundaryDateData G R) =
        boundaryCapitalCost R := by
    unfold localPrefixCapitalCost capitalCreationTechnology
    rw [hinvestment, hcapitalCurrent]
    change boundaryInvestment R +
      (1 / 2 : ℝ) * boundaryInvestment R ^ (2 : ℕ) /
        (2 * boundaryAggregateCapital R) = boundaryCapitalCost R
    rfl
  have hlabor (i : FirmType) :
      localPrefixLabor (primitives G) (boundaryDateData G R) i =
        boundaryLabor R i := by
    change
      ((1 / 2 : ℝ) * (5 / 6) * 1 * technology i *
        boundaryCapital R i ^ (2 / 5 : ℝ) / boundaryWage R) ^
        (1 / (1 - (1 / 2 : ℝ)) : ℝ) = boundaryLabor R i
    unfold boundaryLabor
    congr 1 <;> ring
  have houtput (i : FirmType) :
      localPrefixOutput (primitives G) (boundaryDateData G R) i =
        boundaryOutput R i := by
    unfold localPrefixOutput boundaryOutput
    rw [hlabor i]
    change operatingOutput (1 * technology i) (boundaryCapital R i)
        (boundaryLabor R i) (2 / 5) (1 / 2) =
      operatingOutput (technology i) (boundaryCapital R i)
        (boundaryLabor R i) (2 / 5) (1 / 2)
    simp only [one_mul]
  have haggregateOutput :
      localPrefixAggregateOutput (primitives G) (boundaryDateData G R) =
        boundaryAggregateOutput R := by
    unfold localPrefixAggregateOutput
    rw [sum_firmType_eq_H_add_L]
    change (1 / 2 : ℝ) *
        localPrefixOutput (primitives G) (boundaryDateData G R) .H +
      (1 / 2 : ℝ) *
        localPrefixOutput (primitives G) (boundaryDateData G R) .L =
      boundaryAggregateOutput R
    rw [houtput .H, houtput .L]
    unfold boundaryAggregateOutput average
    ring
  have hfirmAbsorption :
      (∑ i, (primitives G).mass i *
        localPrefixFirmConsumption (boundaryDateData G R).controls i) =
        average (boundaryConsumption R) := by
    rw [sum_firmType_eq_H_add_L]
    change (1 / 2 : ℝ) * boundaryConsumption R .H +
      (1 / 2 : ℝ) * boundaryConsumption R .L =
        average (boundaryConsumption R)
    unfold average
    ring
  change
    localPrefixAggregateOutput (primitives G) (boundaryDateData G R) -
      (boundaryDateData G R).controls.workerConsumption -
      (∑ i, (primitives G).mass i *
        localPrefixFirmConsumption (boundaryDateData G R).controls i) -
      localPrefixCapitalCost (primitives G) (boundaryDateData G R) =
      boundaryResourceResidual R
  rw [haggregateOutput, hfirmAbsorption, hcapitalCost]
  change boundaryAggregateOutput R - boundaryWorkerConsumption R -
      average (boundaryConsumption R) - boundaryCapitalCost R =
        boundaryResourceResidual R
  rfl

/-! ## Cotas de dominio y reescrituras monotonas -/

/-- Cota elemental que deja a V_L por encima de todo el intervalo de R.
    Usa solo Rbar>1 del padre y no la raiz de frontera. -/
theorem continuationReturn_L_gt_boundaryHi :
    boundaryHi < continuationReturn .L := by
  have hR := loanRate_gt_one
  have hR0 := loanRate_pos
  have hinv : 1 / ProposedStationaryBank.loanRate < 1 :=
    (div_lt_iff₀ hR0).2 (by simpa using hR)
  have hfrac :
      (2 / 5 : ℝ) * (39 / 40) / ProposedStationaryBank.loanRate < 39 / 100 := by
    have hpos : 0 < (2 / 5 : ℝ) * (39 / 40) := by norm_num
    calc
      (2 / 5 : ℝ) * (39 / 40) / ProposedStationaryBank.loanRate =
          ((2 / 5 : ℝ) * (39 / 40)) * (1 / ProposedStationaryBank.loanRate) := by ring
      _ < ((2 / 5 : ℝ) * (39 / 40)) * 1 :=
        mul_lt_mul_of_pos_left hinv hpos
      _ = 39 / 100 := by norm_num
  have hu : 3267 / 64000 < userCost .L := by
    unfold userCost pledgeability capitalPrice
    nlinarith
  unfold continuationReturn boundaryHi
  have hJ : liquidationValue = 3159 / 3200 := by
    norm_num [liquidationValue, capitalPrice]
  rw [hJ]
  nlinarith

/-- En el bracket, R y RR son estrictamente positivos. -/
theorem boundary_rate_domain {R : ℝ} (hR : R ∈ boundaryInterval) :
    0 < R ∧ 0 < boundaryReserveRate R := by
  have hRlo : boundaryLo ≤ R := hR.1
  have hm := slope_bounds.2.1
  constructor
  · have hlo : 0 < boundaryLo := by norm_num [boundaryLo]
    linarith
  · unfold boundaryReserveRate
    have hlo : (7 / 800 : ℝ) < boundaryLo := by norm_num [boundaryLo]
    linarith

/-- RD se reescribe como x + c*x/(x+b), siempre que x y x+b no sean cero.
    Esta segunda hipotesis es necesaria: fuera del dominio positivo del
    intervalo, el caso x=-b refuta la identidad debido a la division por cero
    totalizada en Lean. -/
theorem boundaryDepositRate_rewrite (R : ℝ)
    (hrr : boundaryReserveRate R ≠ 0)
    (hsum : boundaryReserveRate R + boundaryPaymentTerm ≠ 0) :
    boundaryDepositRate R = boundaryReserveRate R +
      ((9 / 10) * (meanSlope - boundaryPaymentTerm)) *
        boundaryReserveRate R /
          (boundaryReserveRate R + boundaryPaymentTerm) := by
  have hden : 1 + boundaryPaymentTerm / boundaryReserveRate R ≠ 0 := by
    intro hz
    have hm := congrArg (fun x : ℝ => x * boundaryReserveRate R) hz
    have hx : boundaryReserveRate R + boundaryPaymentTerm = 0 := by
      field_simp [hrr] at hm
      linarith
    exact hsum hx
  unfold boundaryDepositRate
  field_simp [hrr, hsum, hden]
  ring

/-- La escala puede escribirse como R/(2 V_L - 41 R/40). -/
theorem boundaryCapitalScale_rewrite (R : ℝ) (hR : R ≠ 0) :
    boundaryCapitalScale R =
      R / (2 * continuationReturn .L - (41 / 40) * R) := by
  unfold boundaryCapitalScale boundaryCapitalPrice
  field_simp [hR]
  ring

/-- En el bracket la escala es positiva y menor que 40/39; por tanto la
    inversion corriente es estrictamente positiva. -/
theorem boundary_scale_and_investment_domain {R : ℝ}
    (hR : R ∈ boundaryInterval) :
    0 < boundaryCapitalScale R ∧ boundaryCapitalScale R < 40 / 39 ∧
      0 < boundaryInvestment R := by
  rcases boundary_rate_domain hR with ⟨hR0, _hrr0⟩
  have hRhi : R ≤ boundaryHi := hR.2
  have hV : R < continuationReturn .L :=
    lt_of_le_of_lt hRhi continuationReturn_L_gt_boundaryHi
  have hq : 1 < boundaryCapitalPrice R := by
    unfold boundaryCapitalPrice
    exact (one_lt_div hR0).2 hV
  have hden : 0 < (39 / 40 : ℝ) +
      (boundaryCapitalPrice R - 1) / (1 / 2) := by
    have : 0 < boundaryCapitalPrice R - 1 := sub_pos.mpr hq
    positivity
  have hs0 : 0 < boundaryCapitalScale R := by
    unfold boundaryCapitalScale
    exact one_div_pos.mpr hden
  have hs1 : boundaryCapitalScale R < 40 / 39 := by
    unfold boundaryCapitalScale
    have hbase : (39 / 40 : ℝ) <
        (39 / 40) + (boundaryCapitalPrice R - 1) / (1 / 2) := by
      have : 0 < (boundaryCapitalPrice R - 1) / (1 / 2) := by positivity
      linarith
    calc
      1 / ((39 / 40 : ℝ) + (boundaryCapitalPrice R - 1) / (1 / 2)) <
          1 / (39 / 40 : ℝ) :=
        one_div_lt_one_div_of_lt (by norm_num) hbase
      _ = 40 / 39 := by norm_num
  have hK := aggregates_pos.1
  have hgap : 0 < 1 - (39 / 40 : ℝ) * boundaryCapitalScale R := by
    nlinarith
  refine ⟨hs0, hs1, ?_⟩
  unfold boundaryInvestment boundaryAggregateCapital
  nlinarith

/-- Forma algebraica del costo de capital en funcion de la escala s. -/
theorem boundaryCapitalCost_scale_formula {R : ℝ}
    (hs : 0 < boundaryCapitalScale R) :
    boundaryCapitalCost R = aggregateCapital *
      (41 / 80 + 1 / (4 * boundaryCapitalScale R) -
        (4719 / 6400) * boundaryCapitalScale R) := by
  have hK := aggregates_pos.1
  unfold boundaryCapitalCost boundaryInvestment boundaryAggregateCapital
  field_simp [ne_of_gt hK, ne_of_gt hs]
  ring

/-! ## Pegamento abstracto para la raiz exacta -/

/-- El certificado externo solo debe aportar estos dos signos cuando se
    internalice de forma verificable. -/
structure BoundaryEndpointSigns : Prop where
  lo_neg : boundaryResourceResidual boundaryLo < 0
  hi_pos : 0 < boundaryResourceResidual boundaryHi

/-- Paquete analitico independiente del certificado decimal. -/
structure BoundaryAnalyticPackage : Prop where
  continuousOn : ContinuousOn boundaryResourceResidual boundaryInterval
  strictMonoOn : StrictMonoOn boundaryResourceResidual boundaryInterval

/-- Lema generico: continuidad + signos opuestos + monotonia estricta producen
    la raiz unica requerida por PaperInterface.ExactRootOn. -/
theorem exactRootOn_of_continuous_strictMono
    {f : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b)
    (hcont : ContinuousOn f (Set.Icc a b))
    (hmono : StrictMonoOn f (Set.Icc a b))
    (ha : f a < 0) (hb : 0 < f b) :
    ExactRootOn f a b := by
  have hz : (0 : ℝ) ∈ Set.Icc (f a) (f b) := ⟨le_of_lt ha, le_of_lt hb⟩
  rcases intermediate_value_Icc hab hcont hz with ⟨x, hx, hfx⟩
  refine ⟨x, ⟨hx.1, hx.2, hfx⟩, ?_⟩
  intro y hy
  have hyI : y ∈ Set.Icc a b := ⟨hy.1, hy.2.1⟩
  by_contra hne
  rcases lt_or_gt_of_ne hne with hy_lt_x | hx_lt_y
  · have hlt := hmono hyI hx hy_lt_x
    rw [hfx, hy.2.2] at hlt
    exact (lt_irrefl (0 : ℝ)) hlt
  · have hlt := hmono hx hyI hx_lt_y
    rw [hfx, hy.2.2] at hlt
    exact (lt_irrefl (0 : ℝ)) hlt

/-- Especializacion al carrier economico literal. Las dos estructuras
    mantienen deliberadamente separadas la matematica analitica y la
    evidencia de signos de los extremos. -/
theorem boundary_exactRootOn
    (HA : BoundaryAnalyticPackage) (HS : BoundaryEndpointSigns) :
    ExactRootOn boundaryResourceResidual boundaryLo boundaryHi := by
  exact exactRootOn_of_continuous_strictMono
    (le_of_lt boundaryLo_lt_boundaryHi) HA.continuousOn HA.strictMonoOn
    HS.lo_neg HS.hi_pos

/-- Si las cinco piezas economicas tienen las monotonias indicadas, Phi es
    estrictamente creciente. Este lema evita diferenciar Phi. -/
theorem boundaryResourceResidual_strictMonoOn_of_components
    (hY : StrictMonoOn boundaryAggregateOutput boundaryInterval)
    (hCW : StrictAntiOn boundaryWorkerConsumption boundaryInterval)
    (hcH : StrictAntiOn (fun R ↦ boundaryConsumption R .H) boundaryInterval)
    (hcL : StrictAntiOn (fun R ↦ boundaryConsumption R .L) boundaryInterval)
    (hGamma : StrictAntiOn boundaryCapitalCost boundaryInterval) :
    StrictMonoOn boundaryResourceResidual boundaryInterval := by
  intro x hx y hy hxy
  have h1 := hY hx hy hxy
  have h2 := hCW hx hy hxy
  have h3 := hcH hx hy hxy
  have h4 := hcL hx hy hxy
  have h5 := hGamma hx hy hxy
  unfold boundaryResourceResidual average
  linarith

/-!
## Estado de la parte analitica aun por elaborar en Lean

Matematicamente, las hipotesis del lema anterior se descargan asi:

* RD es estrictamente creciente. Con x=R-meanSlope, b=slopeGap/10 y
  c=(9/10)(meanSlope-b)>0,
      RD = x + c*x/(x+b).
  Las cotas slope_bounds dan 0<b<meanSlope y boundary_rate_domain da x>0.

* CW = CWbar / ((99/100) RD) es estrictamente decreciente.

* Los dos consumos empresariales son constantes positivas por 1/R, luego
  son estrictamente decrecientes.

* s(R)=R/(2 V_L-(41/40)R) es estrictamente creciente y 0<s<40/39.
  Gamma(s)=Kbar*(41/80 + 1/(4s) - (4719/6400)s) es estrictamente
  decreciente.

* La identidad de homogeneidad de produccion es
      Y(R) = Ybar * s(R)^(8/15) * (CWbar/CW(R))^(1/3).
  Sus dos factores variables son positivos y estrictamente crecientes,
  por lo que Y es estrictamente creciente.

La traduccion de esta ultima identidad usa potencias reales racionales y es
la pieza mas sensible a elaboracion/tacticas. No se oculta detras de un sorry:
se deja como la siguiente obligacion de compilacion/refinamiento del modulo.

El certificado intervalar archivado aporta de manera separada los signos de
los extremos y, como comprobacion independiente, una cota positiva de Phi'
[34.7593..., 37.5087...] en el bracket. Ese certificado no se declara aqui
como teorema Lean.
-/

end ProposedBoundaryResourceRoot
end Ventura26LiquidityAllocation
