import Ventura26LiquidityAllocation.StationaryRealScaleCandidate

/-!
# Puente productivo del padre: PROPUESTA SIN COMPILAR

Proyecto: alejandroventuraventurameza-tech/ai-project.
Rama: work/chat-continuity.
Commit: 16e24fe828a5a0002ef13bb82bae9e295f190f86.
Base AppliedModelingLib: 194edcc95df74806a39b961d10dedddc6e730cce.
Lean previsto: leanprover/lean4:v4.30.0-rc2.
Mathlib fijado: 5450b53e5ddc75d46418fabb605edbf36bd0beb6.
Destino propuesto:
papers/Ventura26LiquidityAllocation/StationaryProductionBridgeCandidate.lean.

Depende de StationaryRealScaleCandidate y de InterbankCancellationCandidate.
Los tres son candidatos sin compilar. No se modifica el checkpoint, la rama
remota ni el import raiz. La revision estatica no sustituye elaboracion,
kernel, inspeccion de axiomas ni auditoria semantica del protocolo.
SHA256 de la version utilizada de StationaryRealScaleCandidate.lean:
cac64a87126ebda0a46d5a1ddaf64993252463a065e49950c6749248fca9e989

Las entradas de StationaryRealParameters son solo igualdades de primitivas.
No incluyen presupuesto, Euler, produccion, clearing ni equilibrio.

Argumento matematico:
  x_i=((4/5)*C_i/u_i)/w=(m*A_i)^2/(5*u_i*w)>0,
  k_i=x_i^5, k_i^(2/5)=x_i^2.
La base positiva de la demanda laboral es
  z_i=(m*A_i*k_i^(2/5))/(2*w).
Su cuadrado es (5/4)*u_i*k_i/w. Por z_i>0, la raiz de z_i^2
es z_i; la produccion Cobb-Douglas es 3*u_i*k_i y el beneficio
es (5/12)*Y_i. El producto marginal valorado al precio m es
  alpha*m*Y_i/k_i=u_i,
sin un factor adicional (1-beta).

Se enlazan las funciones reales del checkpoint, luego sus agregados,
las filas 1--5 y los residuales empresariales .binding. Tambien se
demuestran signos estrictos de los residuales .slack de L en este padre.

ALCANCE: son identidades en el dato estacionario construido. Todavia no
se construye un Primitives completo, un padre Allocation con todos sus
problemas de optimizacion, un estado heredado fiscal ni una continuacion.
En particular, localSlackPrivateBankCore fija el dual de L en cero en
t=0; no se utiliza para atribuirle el cierre empresarial .binding.
La cancelacion interbancaria previa mantiene su alcance bancario.
Las ramas S y B siguen separadas.
-/

namespace Ventura26LiquidityAllocation
namespace ProposedStationaryProductionBridge

open ProposedStationaryRealScale
open scoped BigOperators

variable {S : Type*} [Fintype S]

/-- Especificacion visible de primitivas del testigo. No presupone
ninguna ecuacion ni la existencia de una asignacion de equilibrio. -/
structure StationaryRealParameters (P : Primitives S) : Prop where
  alpha_eq : P.alpha = 2 / 5
  beta_eq : P.beta = 1 / 2
  productivity_eq : ∀ i, P.productivity i = technology i
  mass_eq : ∀ i, P.mass i = 1 / 2
  depreciation_eq : P.depreciation = 1 / 40
  pledgeability_eq : ∀ i, P.pledgeability i = pledgeability i
  entrepreneurDiscount_eq : P.entrepreneurDiscount = 24 / 25
  workerDiscount_eq : P.workerDiscount = 99 / 100
  laborScale_eq : P.laborScale = 1
  workerRiskAversion_eq : P.workerRiskAversion = 1
  laborCurvature_eq : P.laborCurvature = 1
  capitalAdjustmentCost_eq : P.capitalAdjustmentCost = 1 / 2
  priceElasticity_eq : P.priceElasticity = 6

noncomputable def capitalRoot (i : FirmType) : ℝ :=
  ((4 / 5) * profitCoefficient i / userCost i) / wage

theorem capitalRoot_pos (i : FirmType) : 0 < capitalRoot i := by
  have hC := profitCoefficient_pos i
  have hu := userCost_pos i
  have hw := wage_pos
  unfold capitalRoot
  positivity

theorem capital_eq_root_pow (i : FirmType) :
    capital i = capitalRoot i ^ (5 : ℕ) := by
  unfold capital capitalScale capitalRoot
  exact (div_pow _ _ 5).symm

theorem capitalRoot_identity (i : FirmType) :
    5 * userCost i * wage * capitalRoot i =
      ((5 / 6) * technology i) ^ (2 : ℕ) := by
  unfold capitalRoot profitCoefficient
  field_simp [ne_of_gt (userCost_pos i), ne_of_gt wage_pos] <;> ring

theorem capital_fifth_root (i : FirmType) :
    capital i ^ (1 / 5 : ℝ) = capitalRoot i := by
  rw [capital_eq_root_pow]
  simpa only [one_div] using
    (Real.pow_rpow_inv_natCast (x := capitalRoot i) (n := 5)
      (capitalRoot_pos i).le (by norm_num))

theorem capital_two_fifths (i : FirmType) :
    capital i ^ (2 / 5 : ℝ) = capitalRoot i ^ (2 : ℕ) := by
  rw [capital_eq_root_pow]
  have h := Real.rpow_mul (capitalRoot_pos i).le (5 : ℝ) (2 / 5 : ℝ)
  norm_num [Real.rpow_natCast] at h
  exact h.symm

/-- Base de la potencia laboral, distinta del consumo de la firma. -/
noncomputable def laborInput (i : FirmType) : ℝ :=
  (1 / 2) * (5 / 6) * technology i * capital i ^ (2 / 5 : ℝ) / wage

theorem laborInput_pos (i : FirmType) : 0 < laborInput i := by
  have hA := technology_pos i
  have hk := Real.rpow_pos_of_pos (capital_pos i) (2 / 5 : ℝ)
  have hw := wage_pos
  unfold laborInput
  positivity

theorem laborInput_sq_eq (i : FirmType) :
    laborInput i ^ (2 : ℕ) = labor i := by
  calc
    laborInput i ^ (2 : ℕ) =
        ((5 / 6) * technology i) ^ (2 : ℕ) *
          capitalRoot i ^ (4 : ℕ) / (4 * wage ^ (2 : ℕ)) := by
      unfold laborInput
      rw [capital_two_fifths]
      field_simp [ne_of_gt wage_pos] <;> ring
    _ = (5 * userCost i * wage * capitalRoot i) *
          capitalRoot i ^ (4 : ℕ) / (4 * wage ^ (2 : ℕ)) := by
      rw [← capitalRoot_identity i]
    _ = labor i := by
      unfold labor
      rw [capital_eq_root_pow]
      field_simp [ne_of_gt wage_pos] <;> ring

theorem labor_half_power (i : FirmType) :
    labor i ^ (1 / 2 : ℝ) = laborInput i := by
  rw [← laborInput_sq_eq i]
  simpa only [one_div] using
    (Real.pow_rpow_inv_natCast (x := laborInput i) (n := 2)
      (laborInput_pos i).le (by norm_num))

/-- PROPUESTO, SIN COMPILAR. Produccion Cobb-Douglas del punto exacto. -/
theorem production_identity (i : FirmType) :
    technology i * capital i ^ (2 / 5 : ℝ) * labor i ^ (1 / 2 : ℝ) =
      output i := by
  rw [labor_half_power, capital_two_fifths]
  calc
    technology i * capitalRoot i ^ (2 : ℕ) * laborInput i =
        ((5 / 6) * technology i) ^ (2 : ℕ) * capitalRoot i ^ (4 : ℕ) /
          ((5 / 3) * wage) := by
      unfold laborInput
      rw [capital_two_fifths]
      field_simp [ne_of_gt wage_pos] <;> ring
    _ = (5 * userCost i * wage * capitalRoot i) * capitalRoot i ^ (4 : ℕ) /
          ((5 / 3) * wage) := by
      rw [← capitalRoot_identity i]
    _ = output i := by
      unfold output
      rw [capital_eq_root_pow]
      field_simp [ne_of_gt wage_pos] <;> ring

theorem localPrefixLabor_eq
    (P : Primitives S) (H : StationaryRealParameters P) (i : FirmType) :
    localPrefixLabor P dateData i = labor i := by
  change (P.beta * (5 / 6) * 1 * P.productivity i *
    capital i ^ P.alpha / wage) ^ (1 / (1 - P.beta)) = labor i
  rw [H.beta_eq, H.alpha_eq, H.productivity_eq i]
  rw [show (1 / (1 - (1 / 2 : ℝ))) = (2 : ℝ) by norm_num, Real.rpow_two]
  simpa only [laborInput, mul_one] using laborInput_sq_eq i

theorem localPrefixOutput_eq
    (P : Primitives S) (H : StationaryRealParameters P) (i : FirmType) :
    localPrefixOutput P dateData i = output i := by
  change (1 * P.productivity i) * capital i ^ P.alpha *
    (localPrefixLabor P dateData i) ^ P.beta = output i
  rw [H.productivity_eq i, H.alpha_eq, H.beta_eq, localPrefixLabor_eq P H i]
  simpa only [one_mul] using production_identity i

theorem localPrefixOperatingProfit_eq
    (P : Primitives S) (H : StationaryRealParameters P) (i : FirmType) :
    localPrefixOperatingProfit P dateData i = profit i := by
  change (5 / 6) * localPrefixOutput P dateData i -
    wage * localPrefixLabor P dateData i = profit i
  rw [localPrefixOutput_eq P H i, localPrefixLabor_eq P H i]
  unfold profit output labor
  field_simp [ne_of_gt wage_pos] <;> ring

/-- PROPUESTO, SIN COMPILAR. El marginal valorado es alpha*m*Y/k;
no se agrega un segundo factor (1-beta). -/
theorem localPrefixNextMarginalProduct_eq
    (P : Primitives S) (H : StationaryRealParameters P) (i : FirmType) :
    localPrefixNextMarginalProduct P dateData i = userCost i := by
  change (5 / 6) * 1 * P.productivity i * P.alpha *
    capital i ^ (P.alpha - 1) * (localPrefixLabor P dateData i) ^ P.beta = userCost i
  rw [H.productivity_eq i, H.alpha_eq, H.beta_eq, localPrefixLabor_eq P H i,
    Real.rpow_sub_one (ne_of_gt (capital_pos i)) (2 / 5 : ℝ)]
  calc
    (5 / 6) * 1 * technology i * (2 / 5) *
        (capital i ^ (2 / 5 : ℝ) / capital i) * labor i ^ (1 / 2 : ℝ) =
        ((2 / 5) * (5 / 6)) *
          (technology i * capital i ^ (2 / 5 : ℝ) * labor i ^ (1 / 2 : ℝ)) /
          capital i := by ring
    _ = ((2 / 5) * (5 / 6)) * output i / capital i := by
      rw [production_identity]
    _ = userCost i := by
      unfold output
      field_simp [ne_of_gt (capital_pos i)] <;> ring

theorem localPrefixAggregateCapital_eq
    (P : Primitives S) (H : StationaryRealParameters P) :
    localPrefixAggregateCapital P capital = aggregateCapital := by
  unfold localPrefixAggregateCapital
  rw [sum_firmType_eq_H_add_L]
  simp only [H.mass_eq]
  unfold aggregateCapital average
  ring

theorem localPrefixAggregateOutput_eq
    (P : Primitives S) (H : StationaryRealParameters P) :
    localPrefixAggregateOutput P dateData = aggregateOutput := by
  unfold localPrefixAggregateOutput
  rw [sum_firmType_eq_H_add_L]
  simp only [H.mass_eq]
  rw [localPrefixOutput_eq P H .H, localPrefixOutput_eq P H .L]
  unfold aggregateOutput average
  ring

theorem localPrefixAggregateLabor_eq
    (P : Primitives S) (H : StationaryRealParameters P) :
    localPrefixAggregateLabor P dateData = aggregateLabor := by
  unfold localPrefixAggregateLabor
  rw [sum_firmType_eq_H_add_L]
  simp only [H.mass_eq]
  rw [localPrefixLabor_eq P H .H, localPrefixLabor_eq P H .L]
  unfold aggregateLabor average
  ring

theorem firmConsumption_field (i : FirmType) :
    localPrefixFirmConsumption controls i = firmConsumption i := by
  cases i <;> rfl

theorem aggregateFirmConsumption_eq
    (P : Primitives S) (H : StationaryRealParameters P) :
    (∑ i, P.mass i * localPrefixFirmConsumption controls i) =
      average firmConsumption := by
  rw [sum_firmType_eq_H_add_L]
  simp only [H.mass_eq]
  rw [firmConsumption_field .H, firmConsumption_field .L]
  unfold average
  ring

/-- Consumo constante y positivo: no requiere fijar aversion al riesgo. -/
theorem entrepreneurSDF_eq (P : Primitives S) (i : FirmType) :
    localPrefixEntrepreneurSDF P dateData i = P.entrepreneurDiscount := by
  change P.entrepreneurDiscount *
      crraMarginal P.entrepreneurRiskAversion (localPrefixFirmConsumption controls i) /
      crraMarginal P.entrepreneurRiskAversion (localPrefixFirmConsumption controls i) =
    P.entrepreneurDiscount
  rw [firmConsumption_field]
  have hpos : 0 < crraMarginal P.entrepreneurRiskAversion (firmConsumption i) :=
    Real.rpow_pos_of_pos (firmConsumption_pos i) (-P.entrepreneurRiskAversion)
  field_simp [ne_of_gt hpos] <;> ring

theorem householdSDF_eq (P : Primitives S) :
    P.workerDiscount * crraMarginal P.workerRiskAversion workerConsumption /
      crraMarginal P.workerRiskAversion workerConsumption = P.workerDiscount := by
  have hpos : 0 < crraMarginal P.workerRiskAversion workerConsumption :=
    Real.rpow_pos_of_pos workerConsumption_pos (-P.workerRiskAversion)
  field_simp [ne_of_gt hpos] <;> ring

theorem pledgeUnit_eq
    (P : Primitives S) (H : StationaryRealParameters P) (i : FirmType) :
    localPrefixPledgeUnit P dateData i = pledgeability i * liquidationValue := by
  change P.pledgeability i * (1 - P.depreciation) * 1 * capitalPrice =
    pledgeability i * liquidationValue
  rw [H.pledgeability_eq i, H.depreciation_eq]
  unfold liquidationValue
  ring

theorem firmWealth_eq
    (P : Primitives S) (H : StationaryRealParameters P) (i : FirmType) :
    localPrefixFirmWealth P dateData i =
      profit i + (39 / 40) * capitalPrice * capital i - firmFace i := by
  change localPrefixOperatingProfit P dateData i +
    (1 - P.depreciation) * capitalPrice * capital i - firmFace i / 1 = _
  rw [localPrefixOperatingProfit_eq P H i, H.depreciation_eq]
  ring

theorem firmBudget_eq_zero
    (P : Primitives S) (H : StationaryRealParameters P) (i : FirmType) :
    localReducedFirmBudgetResidual P dateData i = 0 := by
  change localPrefixFirmConsumption controls i + capitalPrice * capital i -
    firmFace i / ProposedStationaryBank.loanRate -
    localPrefixFirmWealth P dateData i = 0
  rw [firmConsumption_field, firmWealth_eq P H i]
  unfold firmConsumption loan
  field_simp [ne_of_gt loanRate_pos] <;> ring

theorem bindingCapitalEuler_eq_zero
    (P : Primitives S) (H : StationaryRealParameters P) (i : FirmType) :
    localReducedFirmCapitalEulerResidual .binding P dateData i = 0 := by
  have hscalar : capitalPrice - localPrefixPledgeUnit P dateData i /
      ProposedStationaryBank.loanRate - localPrefixEntrepreneurSDF P dateData i *
        (localPrefixNextMarginalProduct P dateData i +
          (1 - P.depreciation) * capitalPrice -
          localPrefixPledgeUnit P dateData i / 1) = 0 := by
    rw [pledgeUnit_eq P H i, entrepreneurSDF_eq, H.entrepreneurDiscount_eq,
      localPrefixNextMarginalProduct_eq P H i, H.depreciation_eq]
    unfold userCost liquidationValue
    field_simp [ne_of_gt loanRate_pos] <;> ring
  cases i <;> exact hscalar

theorem bindingRegime_eq_zero
    (P : Primitives S) (H : StationaryRealParameters P) (i : FirmType) :
    localReducedFirmRegimeResidual .binding P dateData i = 0 := by
  have hscalar : firmFace i - localPrefixPledgeUnit P dateData i * capital i = 0 := by
    rw [pledgeUnit_eq P H i]
    unfold firmFace
    ring
  cases i <;> exact hscalar

/-- Presupuesto, Euler y garantia: se derivan individualmente y se reunen
despues. El paquete no se usa como hipotesis de su propia demostracion. -/
theorem binding_firm_rows
    (P : Primitives S) (H : StationaryRealParameters P) :
    ∀ i, localReducedFirmBudgetResidual P dateData i = 0 ∧
      localReducedFirmCapitalEulerResidual .binding P dateData i = 0 ∧
      localReducedFirmRegimeResidual .binding P dateData i = 0 := by
  intro i
  exact ⟨firmBudget_eq_zero P H i, bindingCapitalEuler_eq_zero P H i,
    bindingRegime_eq_zero P H i⟩

theorem localPrefixInvestment_eq
    (P : Primitives S) (H : StationaryRealParameters P) :
    localPrefixInvestment P dateData = aggregateCapital / 40 := by
  change localPrefixAggregateCapital P capital -
    (1 - P.depreciation) * localPrefixAggregateCapital P capital = _
  rw [localPrefixAggregateCapital_eq P H, H.depreciation_eq]
  ring

theorem localPrefixCapitalCost_eq
    (P : Primitives S) (H : StationaryRealParameters P) :
    localPrefixCapitalCost P dateData = (161 / 6400) * aggregateCapital := by
  change localPrefixInvestment P dateData +
    P.capitalAdjustmentCost * localPrefixInvestment P dateData ^ (2 : ℕ) /
      (2 * localPrefixAggregateCapital P capital) = _
  rw [localPrefixInvestment_eq P H, H.capitalAdjustmentCost_eq,
    localPrefixAggregateCapital_eq P H]
  field_simp [ne_of_gt aggregates_pos.1] <;> ring

theorem localPrefixRotembergCost_eq_zero (P : Primitives S) :
    localPrefixRotembergCost P dateData = 0 := by
  simp [localPrefixRotembergCost, dateData, controls]

theorem capitalSupply_row_eq_zero
    (P : Primitives S) (H : StationaryRealParameters P) :
    localReducedRemainingResidual P dateData 1 = 0 := by
  change capitalPrice - 1 - P.capitalAdjustmentCost *
    localPrefixInvestment P dateData / localPrefixAggregateCapital P capital = 0
  rw [H.capitalAdjustmentCost_eq, localPrefixInvestment_eq P H,
    localPrefixAggregateCapital_eq P H]
  unfold capitalPrice
  field_simp [ne_of_gt aggregates_pos.1] <;> ring

theorem resource_row_eq_zero
    (P : Primitives S) (H : StationaryRealParameters P) :
    localReducedRemainingResidual P dateData 2 = 0 := by
  change workerConsumption +
    (∑ i, P.mass i * localPrefixFirmConsumption controls i) +
    localPrefixCapitalCost P dateData + localPrefixRotembergCost P dateData -
    localPrefixAggregateOutput P dateData = 0
  rw [aggregateFirmConsumption_eq P H, localPrefixCapitalCost_eq P H,
    localPrefixRotembergCost_eq_zero, localPrefixAggregateOutput_eq P H]
  unfold workerConsumption
  ring

theorem householdLabor_row_eq_zero
    (P : Primitives S) (H : StationaryRealParameters P) :
    localReducedRemainingResidual P dateData 3 = 0 := by
  change wage - P.laborScale * workerConsumption ^ P.workerRiskAversion *
    localPrefixAggregateLabor P dateData ^ P.laborCurvature = 0
  rw [H.laborScale_eq, H.workerRiskAversion_eq, H.laborCurvature_eq,
    localPrefixAggregateLabor_eq P H]
  simp only [Real.rpow_one, one_mul]
  exact sub_eq_zero.mpr worker_labor_equation

theorem householdDepositEuler_row_eq_zero
    (P : Primitives S) (H : StationaryRealParameters P) :
    localReducedRemainingResidual P dateData 4 = 0 := by
  change 1 -
    (P.workerDiscount * crraMarginal P.workerRiskAversion workerConsumption /
      crraMarginal P.workerRiskAversion workerConsumption) *
      ProposedStationaryBank.depositRate / 1 = 0
  rw [householdSDF_eq, H.workerDiscount_eq]
  norm_num [ProposedStationaryBank.depositRate]

theorem nkpc_row_eq_zero
    (P : Primitives S) (H : StationaryRealParameters P) :
    localReducedRemainingResidual P dateData 5 = 0 := by
  norm_num [localReducedRemainingResidual, dateData, controls, H.priceElasticity_eq]

/-- PROPUESTO, SIN COMPILAR. Se cierran exactamente las filas 1--5;
no se atribuye a este paquete el resto del sistema ni optimalidad. -/
theorem real_remaining_rows
    (P : Primitives S) (H : StationaryRealParameters P) :
    localReducedRemainingResidual P dateData 1 = 0 ∧
    localReducedRemainingResidual P dateData 2 = 0 ∧
    localReducedRemainingResidual P dateData 3 = 0 ∧
    localReducedRemainingResidual P dateData 4 = 0 ∧
    localReducedRemainingResidual P dateData 5 = 0 :=
  ⟨capitalSupply_row_eq_zero P H, resource_row_eq_zero P H,
    householdLabor_row_eq_zero P H, householdDepositEuler_row_eq_zero P H,
    nkpc_row_eq_zero P H⟩

noncomputable def collateralMultiplier : ℝ :=
  1 / ProposedStationaryBank.loanRate - 24 / 25

theorem collateralMultiplier_pos : 0 < collateralMultiplier := by
  rcases ProposedStationaryBank.bank_margins_and_pricing with
    ⟨_hxi0, _hxi1, _hr0, _hr1, _hpricing, _hloan0, hloan1⟩
  have hgap : (24 / 25 : ℝ) < 1 / ProposedStationaryBank.loanRate := by
    apply (lt_div_iff₀ loanRate_pos).2
    nlinarith
  exact sub_pos.mpr hgap

/-- PROPUESTO, SIN COMPILAR. El mismo padre no resuelve el regimen S de L. -/
theorem slack_L_regime_residual_neg
    (P : Primitives S) (H : StationaryRealParameters P) :
    localReducedFirmRegimeResidual .slack P dateData .L < 0 := by
  change ProposedStationaryBank.loanRate *
    localPrefixEntrepreneurSDF P dateData .L / 1 - 1 < 0
  rw [entrepreneurSDF_eq, H.entrepreneurDiscount_eq]
  rcases ProposedStationaryBank.bank_margins_and_pricing with
    ⟨_hxi0, _hxi1, _hr0, _hr1, _hpricing, _hloan0, hloan1⟩
  nlinarith

theorem slack_L_capitalEuler_residual_pos
    (P : Primitives S) (H : StationaryRealParameters P) :
    0 < localReducedFirmCapitalEulerResidual .slack P dateData .L := by
  change 0 < capitalPrice - localPrefixEntrepreneurSDF P dateData .L *
    (localPrefixNextMarginalProduct P dateData .L +
      (1 - P.depreciation) * capitalPrice)
  rw [entrepreneurSDF_eq, H.entrepreneurDiscount_eq,
    localPrefixNextMarginalProduct_eq P H .L, H.depreciation_eq]
  have hid : capitalPrice - (24 / 25) *
      (userCost .L + (1 - 1 / 40) * capitalPrice) =
      pledgeability .L * liquidationValue * collateralMultiplier := by
    unfold userCost liquidationValue collateralMultiplier
    field_simp [ne_of_gt loanRate_pos] <;> ring
  rw [hid]
  exact mul_pos
    (mul_pos (pledgeability_bounds .L).1 liquidationValue_pos)
    collateralMultiplier_pos

end ProposedStationaryProductionBridge
end Ventura26LiquidityAllocation
