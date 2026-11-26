import Ventura26LiquidityAllocation.StationaryEquilibriumCandidate

/-!
# Bloque empresarial del enlace de frontera: PROPUESTA SIN COMPILAR

Proyecto: alejandroventuraventurameza-tech/ai-project.
Rama: work/chat-continuity.
Commit: 16e24fe828a5a0002ef13bb82bae9e295f190f86.
AppliedModelingLib: 194edcc95df74806a39b961d10dedddc6e730cce.
Mathlib: 5450b53e5ddc75d46418fabb605edbf36bd0beb6.
Lean previsto: leanprover/lean4:v4.30.0-rc2.

Fuente matematica: paper/paper.tex, 985--1068, enlace exacto de frontera.
Fuente de contratos: FinancialCore.lean, ActiveCollateralZeroDual y
ValuableCollateralLoan; EconomicModel.lean, LocalPrefixDateData y sus tres
residuales empresariales. No se modifica la fuente conservada.

Orden matematico previo al codigo:
1. V_i = u_i + J, pbar_i = qbar - theta_i*J/Rbar. La Euler estacionaria
   da pbar_i = (24/25)*(V_i-theta_i*J)>0.
2. V_H-V_L = (25/96)*J*mubar>0, donde mubar=1/Rbar-24/25.
3. Para cualquier R>0, q0=V_L/R y p_i=(V_L-theta_i*J)/R>0.
   Elegimos cL0=cbarL/((24/25)*R) y cH0=cbarH*p_H/pbar_H.
4. El SDF literal, con aversion uno, es (24/25)*c_i0/cbar_i.
   Por ello SDF_L=1/R, mu_L=0 y
   mu_H=(24/25)*(V_H-V_L)/(R*pbar_H)>0.
5. Las promesas originadas se mantienen theta_i*J*kbar_i>0, con cobertura
   en igualdad. L esta en ActiveCollateralZeroDual, no en la rama
   estrictamente holgada ni en ValuableCollateralLoan.
6. El portador de fecha conserva los campos no empresariales de una
   plantilla d. Sus consumos, precio de capital y tasa de prestamo se
   reemplazan por los anteriores; los campos empresariales siguientes
   son estacionarios. La promesa HEREDADA se define por el presupuesto
   exacto, no se supone su cumplimiento como premisa.
7. Se anulan las seis filas empresariales tanto de .binding como de
   .slack. Esta coincidencia de igualdades ocurre en la frontera;
   no prueba ninguna de las dos ramas estrictas perturbadas.

ALCANCE: este archivo no certifica signo ni cobertura de las promesas
heredadas construidas, factibilidad agregada, una raiz de Phi, continuidad
exacta en estados proximos, un Jacobiano invertible ni un nuevo equilibrio.
G permanece simbolico. La plantilla permite completar despues salarios,
capital heredado, recursos, bancos y politica sin reescribir este bloque.
Toda la cadena propuesta sigue SIN COMPILAR. No se ha ejecutado Lean.
-/

/-!
Destino propuesto: papers/Ventura26LiquidityAllocation/BoundaryFirmBridgeCandidate.lean.
Dependencia propuesta StationaryEquilibriumCandidate.lean SHA256:
c6b97bdfd9662db5c1c29ee4e1bf0d8a80a7cbd9a9b218f060f18cbc45418baf.
EconomicModel.lean SHA256:
d5e9bb95aad09ff515cc1418778c241d1b91ca3095c02b31eb369f496ea38d86.
FinancialCore.lean SHA256:
4130b338183b3e5e659df7a7f2f517fc356967404c2571a82cea0154f9fc58fa.
-/

namespace Ventura26LiquidityAllocation
namespace ProposedBoundaryBridge

open ProposedStationaryRealScale
open ProposedStationaryProductionBridge
open ProposedStationaryPrimitives

/-! ## Identidades del padre que fijan el enlace -/

noncomputable def continuationReturn (i : FirmType) : ℝ :=
  userCost i + liquidationValue

noncomputable def parentEffectivePrice (i : FirmType) : ℝ :=
  capitalPrice - pledgeability i * liquidationValue /
    ProposedStationaryBank.loanRate

theorem continuationReturn_pos (i : FirmType) : 0 < continuationReturn i :=
  add_pos (userCost_pos i) liquidationValue_pos

theorem parentEffectivePrice_eq_financingFraction (i : FirmType) :
    parentEffectivePrice i = capitalPrice * financingFraction i := by
  unfold parentEffectivePrice financingFraction liquidationValue
  ring

theorem parentEffectivePrice_pos (i : FirmType) :
    0 < parentEffectivePrice i := by
  rw [parentEffectivePrice_eq_financingFraction]
  exact mul_pos capitalPrice_pos (financing_and_expenditure_pos i).1

theorem parentEffectivePrice_identity (i : FirmType) :
    parentEffectivePrice i =
      (24 / 25) * (continuationReturn i - pledgeability i * liquidationValue) := by
  unfold parentEffectivePrice continuationReturn userCost liquidationValue
  field_simp [ne_of_gt loanRate_pos] <;> ring

theorem continuationReturn_H_sub_L :
    continuationReturn .H - continuationReturn .L =
      (25 / 96) * liquidationValue * collateralMultiplier := by
  unfold continuationReturn userCost pledgeability collateralMultiplier
    liquidationValue
  field_simp [ne_of_gt loanRate_pos] <;> ring

theorem continuationReturn_L_lt_H :
    continuationReturn .L < continuationReturn .H := by
  have hgap : 0 < continuationReturn .H - continuationReturn .L := by
    rw [continuationReturn_H_sub_L]
    exact mul_pos
      (mul_pos (by norm_num) liquidationValue_pos) collateralMultiplier_pos
  exact sub_pos.mp hgap

/-! ## Elecciones de impacto, todavia parametrizadas por R -/

noncomputable def boundaryCapitalPrice (R : ℝ) : ℝ :=
  continuationReturn .L / R

noncomputable def boundaryEffectivePrice (R : ℝ) (i : FirmType) : ℝ :=
  boundaryCapitalPrice R - pledgeability i * liquidationValue / R

noncomputable def boundaryConsumption (R : ℝ) : FirmType → ℝ
  | .H => firmConsumption .H * boundaryEffectivePrice R .H /
      parentEffectivePrice .H
  | .L => firmConsumption .L / ((24 / 25) * R)

noncomputable def boundarySDF (R : ℝ) (i : FirmType) : ℝ :=
  (24 / 25) * boundaryConsumption R i / firmConsumption i

noncomputable def boundaryDual (R : ℝ) (i : FirmType) : ℝ :=
  1 / R - boundarySDF R i

theorem boundaryCapitalPrice_pos (R : ℝ) (hR : 0 < R) :
    0 < boundaryCapitalPrice R :=
  div_pos (continuationReturn_pos .L) hR

theorem boundaryEffectivePrice_eq (R : ℝ) (i : FirmType) :
    boundaryEffectivePrice R i =
      (continuationReturn .L - pledgeability i * liquidationValue) / R := by
  unfold boundaryEffectivePrice boundaryCapitalPrice
  ring

theorem boundaryEffectivePrice_pos (R : ℝ) (hR : 0 < R) (i : FirmType) :
    0 < boundaryEffectivePrice R i := by
  rw [boundaryEffectivePrice_eq]
  have hremain : 0 < (1 - pledgeability i) * liquidationValue :=
    mul_pos (sub_pos.mpr (pledgeability_bounds i).2) liquidationValue_pos
  have hu := userCost_pos .L
  apply div_pos _ hR
  unfold continuationReturn
  nlinarith

theorem boundaryConsumption_pos (R : ℝ) (hR : 0 < R) (i : FirmType) :
    0 < boundaryConsumption R i := by
  cases i with
  | H =>
      exact div_pos
        (mul_pos (firmConsumption_pos .H) (boundaryEffectivePrice_pos R hR .H))
        (parentEffectivePrice_pos .H)
  | L =>
      exact div_pos (firmConsumption_pos .L) (mul_pos (by norm_num) hR)

theorem boundarySDF_pos (R : ℝ) (hR : 0 < R) (i : FirmType) :
    0 < boundarySDF R i :=
  div_pos (mul_pos (by norm_num) (boundaryConsumption_pos R hR i))
    (firmConsumption_pos i)

theorem boundarySDF_H (R : ℝ) :
    boundarySDF R .H =
      (24 / 25) * boundaryEffectivePrice R .H / parentEffectivePrice .H := by
  unfold boundarySDF boundaryConsumption
  field_simp [ne_of_gt (firmConsumption_pos .H),
    ne_of_gt (parentEffectivePrice_pos .H)] <;> ring

theorem boundarySDF_L (R : ℝ) (hR : 0 < R) :
    boundarySDF R .L = 1 / R := by
  unfold boundarySDF boundaryConsumption
  field_simp [ne_of_gt hR, ne_of_gt (firmConsumption_pos .L)] <;> ring

theorem boundaryDual_L (R : ℝ) (hR : 0 < R) :
    boundaryDual R .L = 0 := by
  unfold boundaryDual
  rw [boundarySDF_L R hR]
  ring

theorem boundaryDual_H_formula (R : ℝ) (hR : 0 < R) :
    boundaryDual R .H =
      (24 / 25) * (continuationReturn .H - continuationReturn .L) /
        (R * parentEffectivePrice .H) := by
  unfold boundaryDual
  rw [boundarySDF_H, boundaryEffectivePrice_eq]
  have hp := parentEffectivePrice_identity .H
  field_simp [ne_of_gt hR, ne_of_gt (parentEffectivePrice_pos .H)] <;>
    nlinarith [hp]

theorem boundaryDual_H_pos (R : ℝ) (hR : 0 < R) :
    0 < boundaryDual R .H := by
  rw [boundaryDual_H_formula R hR]
  exact div_pos
    (mul_pos (by norm_num) (sub_pos.mpr continuationReturn_L_lt_H))
    (mul_pos hR (parentEffectivePrice_pos .H))

theorem boundaryEffectiveEuler (R : ℝ) (hR : 0 < R) (i : FirmType) :
    boundaryEffectivePrice R i =
      boundarySDF R i * (continuationReturn i - pledgeability i * liquidationValue) := by
  cases i with
  | H =>
      rw [boundarySDF_H]
      calc
        boundaryEffectivePrice R .H =
            boundaryEffectivePrice R .H * parentEffectivePrice .H /
              parentEffectivePrice .H := by
          field_simp [ne_of_gt (parentEffectivePrice_pos .H)]
        _ = boundaryEffectivePrice R .H *
              ((24 / 25) *
                (continuationReturn .H - pledgeability .H * liquidationValue)) /
              parentEffectivePrice .H := by
          rw [parentEffectivePrice_identity .H]
        _ = (24 / 25) * boundaryEffectivePrice R .H / parentEffectivePrice .H *
              (continuationReturn .H - pledgeability .H * liquidationValue) := by
          ring
  | L =>
      rw [boundaryEffectivePrice_eq, boundarySDF_L R hR]
      ring

/-! ## Clasificacion financiera en los predicados conservados -/

theorem boundary_H_valuable (R : ℝ) (hR : 0 < R) :
    ValuableCollateralLoan R (pledgeability .H * liquidationValue) (capital .H)
      (boundarySDF R .H) (firmFace .H) (boundaryDual R .H) := by
  refine ⟨rfl, firmFace_pos .H, boundaryDual_H_pos R hR, ?_, rfl⟩
  have hmu := boundaryDual_H_pos R hR
  unfold boundaryDual at hmu
  linarith

theorem boundary_L_active_zero_dual (R : ℝ) (hR : 0 < R) :
    ActiveCollateralZeroDual R (pledgeability .L * liquidationValue) (capital .L)
      (boundarySDF R .L) (firmFace .L) (boundaryDual R .L) :=
  ⟨rfl, firmFace_pos .L, boundaryDual_L R hR, boundarySDF_L R hR⟩

theorem boundary_L_not_strictly_slack (R : ℝ) :
    ¬ SlackCollateralLoan R (pledgeability .L * liquidationValue) (capital .L)
      (boundarySDF R .L) (firmFace .L) (boundaryDual R .L) := by
  intro h
  have hstrict := h.2.1
  exact (lt_irrefl (firmFace .L)) (by simpa only [firmFace] using hstrict)

theorem boundary_L_not_valuable (R : ℝ) (hR : 0 < R) :
    ¬ ValuableCollateralLoan R (pledgeability .L * liquidationValue) (capital .L)
      (boundarySDF R .L) (firmFace .L) (boundaryDual R .L) := by
  intro h
  have hstrict := h.2.2.1
  rw [boundaryDual_L R hR] at hstrict
  exact (lt_irrefl (0 : ℝ)) hstrict

/-- Las KKT financieras se recuperan de la clasificacion probada de la
fuente. El dominio de tasas permanece una premisa visible y separada. -/
theorem boundary_signedFinancialKKT (R RD : ℝ)
    (hrates : PositiveRateDomain R RD) (i : FirmType) :
    SignedFinancialKKT R RD (pledgeability i * liquidationValue) (capital i)
      (boundarySDF R i) (firmFace i) (boundaryDual R i) := by
  have hR : 0 < R := hrates.1.trans hrates.2
  have hdomain : PositiveFinancialDomain R RD
      (pledgeability i * liquidationValue) (capital i) (boundarySDF R i) :=
    ⟨hrates, mul_pos (pledgeability_bounds i).1 liquidationValue_pos,
      capital_pos i, boundarySDF_pos R hR i⟩
  apply (signedFinancialKKT_iff_five_regimes hdomain).2
  cases i with
  | H => exact Or.inl (boundary_H_valuable R hR)
  | L => exact Or.inr (Or.inr (Or.inr (Or.inr (boundary_L_active_zero_dual R hR))))

/-! ## Portador de fecha y presupuesto heredado exacto -/

/-- Solo se fijan los controles requeridos por el bloque empresarial.
Salario, consumo trabajador, inputPrice, tasa de deposito y tightness
permanecen tomados de la plantilla y deben cerrarse por separado. -/
noncomputable def boundaryFirmControls (R : ℝ) (u : LocalPrefixControlsTen) :
    LocalPrefixControlsTen :=
  { u with
    consumptionH := boundaryConsumption R .H
    consumptionL := boundaryConsumption R .L
    capitalPrice := boundaryCapitalPrice R
    loanRate := R
    inflation := 1 }

theorem boundaryFirmConsumption_field (R : ℝ) (u : LocalPrefixControlsTen)
    (i : FirmType) :
    localPrefixFirmConsumption (boundaryFirmControls R u) i =
      boundaryConsumption R i := by
  cases i <;> rfl

noncomputable def boundaryFirmDateSeed (R : ℝ) (d : LocalPrefixDateData) :
    LocalPrefixDateData :=
  { d with
    controls := boundaryFirmControls R d.controls
    nextControls := controls
    nextCapital := capital
    nextFace := firmFace
    nextAggregateProductivity := 1 }

/-- Promesa heredada implicada por el presupuesto de fecha cero. Su signo
y su cobertura inicial NO estan incluidos en este resultado algebraico. -/
noncomputable def boundaryInheritedFace (G R : ℝ) (d : LocalPrefixDateData)
    (i : FirmType) : ℝ :=
  localPrefixOperatingProfit (primitives G) (boundaryFirmDateSeed R d) i +
    (1 - (1 / 40 : ℝ)) * boundaryCapitalPrice R * d.currentCapital i -
    boundaryConsumption R i - boundaryEffectivePrice R i * capital i

noncomputable def boundaryFirmDateData (G R : ℝ) (d : LocalPrefixDateData) :
    LocalPrefixDateData :=
  { boundaryFirmDateSeed R d with inheritedFace := boundaryInheritedFace G R d }

theorem boundary_source_entrepreneurSDF (G R : ℝ) (d : LocalPrefixDateData)
    (i : FirmType) :
    localPrefixEntrepreneurSDF (primitives G) (boundaryFirmDateData G R d) i =
      boundarySDF R i := by
  change (24 / 25 : ℝ) *
      crraMarginal 1 (localPrefixFirmConsumption controls i) /
      crraMarginal 1
        (localPrefixFirmConsumption (boundaryFirmControls R d.controls) i) = _
  rw [firmConsumption_field, boundaryFirmConsumption_field]
  simp only [crraMarginal, Real.rpow_neg_one, div_inv_eq_mul]
  unfold boundarySDF
  ring

theorem boundary_source_nextMarginalProduct (G R : ℝ) (d : LocalPrefixDateData)
    (i : FirmType) :
    localPrefixNextMarginalProduct (primitives G) (boundaryFirmDateData G R d) i =
      userCost i := by
  change localPrefixNextMarginalProduct (primitives G) dateData i = userCost i
  exact localPrefixNextMarginalProduct_eq (primitives G)
    (stationary_parameters G).toStationaryRealParameters i

theorem boundary_source_pledgeUnit (G R : ℝ) (d : LocalPrefixDateData)
    (i : FirmType) :
    localPrefixPledgeUnit (primitives G) (boundaryFirmDateData G R d) i =
      pledgeability i * liquidationValue := by
  change pledgeability i * (1 - (1 / 40 : ℝ)) * 1 * capitalPrice = _
  unfold liquidationValue
  ring

theorem boundary_source_firmWealth (G R : ℝ) (d : LocalPrefixDateData)
    (i : FirmType) :
    localPrefixFirmWealth (primitives G) (boundaryFirmDateData G R d) i =
      boundaryConsumption R i + boundaryEffectivePrice R i * capital i := by
  change localPrefixOperatingProfit (primitives G) (boundaryFirmDateSeed R d) i +
      (1 - (1 / 40 : ℝ)) * boundaryCapitalPrice R * d.currentCapital i -
      boundaryInheritedFace G R d i / 1 = _
  unfold boundaryInheritedFace
  ring

theorem boundary_source_firmBudget (G R : ℝ) (d : LocalPrefixDateData)
    (i : FirmType) :
    localReducedFirmBudgetResidual (primitives G) (boundaryFirmDateData G R d) i = 0 := by
  change localPrefixFirmConsumption (boundaryFirmControls R d.controls) i +
      boundaryCapitalPrice R * capital i - firmFace i / R -
      localPrefixFirmWealth (primitives G) (boundaryFirmDateData G R d) i = 0
  rw [boundaryFirmConsumption_field, boundary_source_firmWealth]
  unfold boundaryEffectivePrice firmFace
  ring

theorem boundary_source_bindingCapitalEuler (G R : ℝ) (hR : 0 < R)
    (d : LocalPrefixDateData) (i : FirmType) :
    localReducedFirmCapitalEulerResidual .binding (primitives G)
      (boundaryFirmDateData G R d) i = 0 := by
  have hscalar : boundaryCapitalPrice R -
      localPrefixPledgeUnit (primitives G) (boundaryFirmDateData G R d) i / R -
      localPrefixEntrepreneurSDF (primitives G) (boundaryFirmDateData G R d) i *
        (localPrefixNextMarginalProduct (primitives G) (boundaryFirmDateData G R d) i +
          (1 - (1 / 40 : ℝ)) * capitalPrice -
          localPrefixPledgeUnit (primitives G) (boundaryFirmDateData G R d) i / 1) = 0 := by
    rw [boundary_source_pledgeUnit, boundary_source_entrepreneurSDF,
      boundary_source_nextMarginalProduct]
    norm_num only [div_one, show (1 - (1 / 40 : ℝ)) = 39 / 40 by norm_num]
    change boundaryEffectivePrice R i -
      boundarySDF R i * (continuationReturn i - pledgeability i * liquidationValue) = 0
    rw [boundaryEffectiveEuler R hR i]
    ring
  cases i <;> exact hscalar

theorem boundary_source_bindingRegime (G R : ℝ) (d : LocalPrefixDateData)
    (i : FirmType) :
    localReducedFirmRegimeResidual .binding (primitives G)
      (boundaryFirmDateData G R d) i = 0 := by
  have hscalar : firmFace i -
      localPrefixPledgeUnit (primitives G) (boundaryFirmDateData G R d) i * capital i = 0 := by
    rw [boundary_source_pledgeUnit]
    unfold firmFace
    ring
  cases i <;> exact hscalar

theorem boundary_source_slackRegime_L (G R : ℝ) (hR : 0 < R)
    (d : LocalPrefixDateData) :
    localReducedFirmRegimeResidual .slack (primitives G)
      (boundaryFirmDateData G R d) .L = 0 := by
  change R * localPrefixEntrepreneurSDF (primitives G)
    (boundaryFirmDateData G R d) .L / 1 - 1 = 0
  rw [boundary_source_entrepreneurSDF, boundarySDF_L R hR]
  field_simp [ne_of_gt hR] <;> ring

theorem boundary_source_slackCapitalEuler_L (G R : ℝ) (hR : 0 < R)
    (d : LocalPrefixDateData) :
    localReducedFirmCapitalEulerResidual .slack (primitives G)
      (boundaryFirmDateData G R d) .L = 0 := by
  change boundaryCapitalPrice R -
      localPrefixEntrepreneurSDF (primitives G) (boundaryFirmDateData G R d) .L *
        (localPrefixNextMarginalProduct (primitives G) (boundaryFirmDateData G R d) .L +
          (1 - (1 / 40 : ℝ)) * capitalPrice) = 0
  rw [boundary_source_entrepreneurSDF, boundary_source_nextMarginalProduct,
    boundarySDF_L R hR]
  unfold boundaryCapitalPrice continuationReturn liquidationValue
  ring

/-- Las dos listas de igualdades empresariales coinciden en esta frontera.
Las desigualdades estrictas que distinguen S y B no se afirman aqui. -/
theorem boundary_source_firm_rows (G R : ℝ) (hR : 0 < R)
    (d : LocalPrefixDateData) (branch : LocalPrefixBranch) (i : FirmType) :
    localReducedFirmBudgetResidual (primitives G) (boundaryFirmDateData G R d) i = 0 ∧
    localReducedFirmCapitalEulerResidual branch (primitives G)
      (boundaryFirmDateData G R d) i = 0 ∧
    localReducedFirmRegimeResidual branch (primitives G)
      (boundaryFirmDateData G R d) i = 0 := by
  refine ⟨boundary_source_firmBudget G R d i, ?_, ?_⟩
  · cases branch with
    | binding => exact boundary_source_bindingCapitalEuler G R hR d i
    | slack =>
        cases i with
        | H => exact boundary_source_bindingCapitalEuler G R hR d .H
        | L => exact boundary_source_slackCapitalEuler_L G R hR d
  · cases branch with
    | binding => exact boundary_source_bindingRegime G R d i
    | slack =>
        cases i with
        | H => exact boundary_source_bindingRegime G R d .H
        | L => exact boundary_source_slackRegime_L G R hR d

end ProposedBoundaryBridge
end Ventura26LiquidityAllocation
