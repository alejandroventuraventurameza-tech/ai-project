import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Ventura26LiquidityAllocation.BoundaryWorkerLaborCandidate

/-!
# Continuidad y monotonia del residual exacto de frontera

PROPUESTA LEAN NO COMPILADA.
Repo: alejandroventuraventurameza-tech/ai-project
Rama: work/chat-continuity
Commit: 16e24fe828a5a0002ef13bb82bae9e295f190f86
Mathlib: 5450b53e5ddc75d46418fabb605edbf36bd0beb6

No se introduce como hipotesis ninguna monotonia de las piezas ni la
continuidad del residual. Los signos de los extremos son otra obligacion,
BoundaryEndpointSigns, y NO se suponen certificados por este archivo.

Se importa la version corregida de BoundaryResourceRootCandidate: la
identidad para RD exige x != 0 y x+b != 0, no solo x != 0.
SHA256 del modulo inmediato BoundaryWorkerLaborCandidate:
2e7f8e5bd7f1adda6564189395054b0f110d1b5c5b02d13fba920265f5b0e772.

Toda esta cadena esta SIN COMPILAR. El trabajo matematico y la revision
estatica no equivalen a kernel, Lake ni auditoria transitiva de axiomas.
-/

open Set
open scoped BigOperators

namespace Ventura26LiquidityAllocation
namespace ProposedBoundaryAnalyticPackage

open ProposedStationaryBank
open ProposedStationaryRealScale
open ProposedStationaryProductionBridge
open ProposedBoundaryBridge
open ProposedBoundaryResourceRoot
open ProposedBoundaryWorkerLabor

private theorem paymentTerm_pos : 0 < boundaryPaymentTerm := by
  unfold boundaryPaymentTerm
  exact div_pos slope_bounds.2.2.1 (by norm_num)

private theorem depositExtra_pos :
    0 < (9 / 10 : ℝ) * (meanSlope - boundaryPaymentTerm) := by
  have h := slope_bounds.2.2.2.2
  unfold boundaryPaymentTerm at h
  exact mul_pos (by norm_num) h

private theorem reserveRate_mono :
    StrictMonoOn boundaryReserveRate boundaryInterval := by
  intro x hx y hy hxy
  unfold boundaryReserveRate
  linarith

/-- El orden de x/(x+b) se prueba por productos cruzados positivos. -/
private theorem reserveFraction_mono :
    StrictMonoOn
      (fun R => boundaryReserveRate R /
        (boundaryReserveRate R + boundaryPaymentTerm))
      boundaryInterval := by
  intro x hx y hy hxy
  have hxx := (boundary_rate_domain hx).2
  have hyy := (boundary_rate_domain hy).2
  have hxy' := reserveRate_mono hx hy hxy
  have hd1 := add_pos hxx paymentTerm_pos
  have hd2 := add_pos hyy paymentTerm_pos
  apply (div_lt_div_iff₀ hd1 hd2).2
  have hg := mul_pos (sub_pos.mpr hxy') paymentTerm_pos
  nlinarith

/-- La tasa de depositos aumenta estrictamente en el bracket. -/
theorem depositRate_strictMonoOn :
    StrictMonoOn boundaryDepositRate boundaryInterval := by
  intro x hx y hy hxy
  have hxx := (boundary_rate_domain hx).2
  have hyy := (boundary_rate_domain hy).2
  have hz1 := add_pos hxx paymentTerm_pos
  have hz2 := add_pos hyy paymentTerm_pos
  have hbase := reserveRate_mono hx hy hxy
  have hfrac := reserveFraction_mono hx hy hxy
  rw [boundaryDepositRate_rewrite x (ne_of_gt hxx) (ne_of_gt hz1),
    boundaryDepositRate_rewrite y (ne_of_gt hyy) (ne_of_gt hz2)]
  have hterm := mul_lt_mul_of_pos_left hfrac depositExtra_pos
  -- Explicit polynomial rearrangement of c*x/(x+b) = c*(x/(x+b)).
  convert add_lt_add hbase hterm using 1 <;> ring

/-- Los denominadores relevantes del consumo trabajador son positivos. -/
private theorem depositRate_pos {R : ℝ} (hR : R ∈ boundaryInterval) :
    0 < boundaryDepositRate R :=
  boundaryDepositRate_pos hR

theorem workerConsumption_strictAntiOn :
    StrictAntiOn boundaryWorkerConsumption boundaryInterval := by
  intro x hx y hy hxy
  have hrd := depositRate_strictMonoOn hx hy hxy
  have hdx := depositRate_pos hx
  have hdy := depositRate_pos hy
  have h1 : 0 < (99 / 100 : ℝ) * boundaryDepositRate x :=
    mul_pos (by norm_num) hdx
  have h2 : 0 < (99 / 100 : ℝ) * boundaryDepositRate y :=
    mul_pos (by norm_num) hdy
  have hden : (99 / 100 : ℝ) * boundaryDepositRate x <
      (99 / 100) * boundaryDepositRate y :=
    mul_lt_mul_of_pos_left hrd (by norm_num)
  unfold boundaryWorkerConsumption
  apply (div_lt_div_iff₀ h2 h1).2
  exact mul_lt_mul_of_pos_left hden workerConsumption_pos

/-! ## Dos consumos empresariales: constantes positivas sobre R -/

noncomputable def firmConsumptionNumerator : FirmType → ℝ
  | .H => firmConsumption .H *
      (continuationReturn .L - pledgeability .H * liquidationValue) /
        parentEffectivePrice .H
  | .L => firmConsumption .L / (24 / 25)

private theorem firmConsumptionNumerator_pos (i : FirmType) :
    0 < firmConsumptionNumerator i := by
  cases i with
  | H =>
      have hnet : 0 < continuationReturn .L -
          pledgeability .H * liquidationValue := by
        unfold continuationReturn
        have hp := (pledgeability_bounds .H).2
        have hu := userCost_pos .L
        have hj := liquidationValue_pos
        have hmargin : 0 < (1 - pledgeability .H) * liquidationValue :=
          mul_pos (sub_pos.mpr hp) hj
        nlinarith
      exact div_pos
        (mul_pos (firmConsumption_pos .H) hnet)
        (parentEffectivePrice_pos .H)
  | L =>
      exact div_pos (firmConsumption_pos .L) (by norm_num)

private theorem firmConsumption_eq_numerator_div {R : ℝ}
    (hR : 0 < R) (i : FirmType) :
    boundaryConsumption R i = firmConsumptionNumerator i / R := by
  cases i with
  | H =>
      unfold boundaryConsumption firmConsumptionNumerator
      rw [boundaryEffectivePrice_eq]
      field_simp [ne_of_gt hR, ne_of_gt (parentEffectivePrice_pos .H)] <;> ring
  | L =>
      unfold boundaryConsumption firmConsumptionNumerator
      field_simp [ne_of_gt hR] <;> ring

theorem firmConsumption_strictAntiOn (i : FirmType) :
    StrictAntiOn (fun R => boundaryConsumption R i) boundaryInterval := by
  intro x hx y hy hxy
  have hxpos := (boundary_rate_domain hx).1
  have hypos := (boundary_rate_domain hy).1
  change boundaryConsumption y i < boundaryConsumption x i
  rw [firmConsumption_eq_numerator_div hypos i,
    firmConsumption_eq_numerator_div hxpos i]
  apply (div_lt_div_iff₀ hypos hxpos).2
  exact mul_lt_mul_of_pos_left hxy (firmConsumptionNumerator_pos i)

/-! ## Escala y costo de capital -/

private theorem scaleDen_pos {R : ℝ} (hR : R ∈ boundaryInterval) :
    0 < 2 * continuationReturn .L - (41 / 40 : ℝ) * R := by
  have hV := continuationReturn_L_gt_boundaryHi
  have hr := hR.2
  have hvpos := continuationReturn_pos .L
  nlinarith

theorem capitalScale_strictMonoOn :
    StrictMonoOn boundaryCapitalScale boundaryInterval := by
  intro x hx y hy hxy
  have hxpos := (boundary_rate_domain hx).1
  have hypos := (boundary_rate_domain hy).1
  have hdx := scaleDen_pos hx
  have hdy := scaleDen_pos hy
  rw [boundaryCapitalScale_rewrite x (ne_of_gt hxpos),
    boundaryCapitalScale_rewrite y (ne_of_gt hypos)]
  apply (div_lt_div_iff₀ hdx hdy).2
  have hvpos := continuationReturn_pos .L
  nlinarith [mul_pos hvpos (sub_pos.mpr hxy)]

theorem capitalCost_strictAntiOn :
    StrictAntiOn boundaryCapitalCost boundaryInterval := by
  intro x hx y hy hxy
  have hsx := (boundary_scale_and_investment_domain hx).1
  have hsy := (boundary_scale_and_investment_domain hy).1
  have hsxy := capitalScale_strictMonoOn hx hy hxy
  have hdenx : 0 < (4 : ℝ) * boundaryCapitalScale x :=
    mul_pos (by norm_num) hsx
  have hdeny : 0 < (4 : ℝ) * boundaryCapitalScale y :=
    mul_pos (by norm_num) hsy
  have hdenxy : (4 : ℝ) * boundaryCapitalScale x <
      (4 : ℝ) * boundaryCapitalScale y :=
    mul_lt_mul_of_pos_left hsxy (by norm_num)
  have hinv : (1 : ℝ) / (4 * boundaryCapitalScale y) <
      1 / (4 * boundaryCapitalScale x) :=
    one_div_lt_one_div_of_lt hdenx hdenxy
  have hcostx := boundaryCapitalCost_scale_formula (R := x) hsx
  have hcosty := boundaryCapitalCost_scale_formula (R := y) hsy
  rw [hcostx, hcosty]
  have hK := aggregates_pos.1
  apply mul_lt_mul_of_pos_left _ hK
  linarith

/-! ## Producto agregado: una identidad de homogeneidad sin derivadas -/

private theorem laborFactor_pos {R : ℝ} (hR : R ∈ boundaryInterval) :
    0 < boundaryLaborFactor R := by
  have hs := (boundary_scale_and_investment_domain hR).1
  have hw := boundaryWage_pos hR
  unfold boundaryLaborFactor
  exact mul_pos (Real.rpow_pos_of_pos hs _)
    (pow_pos (div_pos wage_pos hw) _)

private theorem laborFactor_half_power {R : ℝ}
    (hR : R ∈ boundaryInterval) :
    boundaryLaborFactor R ^ (1 / 2 : ℝ) =
      boundaryCapitalScale R ^ (2 / 5 : ℝ) * (wage / boundaryWage R) := by
  have hs := (boundary_scale_and_investment_domain hR).1
  have hw := boundaryWage_pos hR
  have hz := Real.rpow_pos_of_pos hs (2 / 5 : ℝ)
  have ht := div_pos wage_pos hw
  have heq : boundaryLaborFactor R =
      (boundaryCapitalScale R ^ (2 / 5 : ℝ) *
        (wage / boundaryWage R)) ^ (2 : ℕ) := by
    unfold boundaryLaborFactor
    rw [← boundaryScale_two_fifths_sq hR]
    ring
  rw [heq]
  simpa only [one_div] using
    (Real.pow_rpow_inv_natCast
      (mul_nonneg hz.le ht.le) (n := 2) (by norm_num))

/-- Y_i de frontera es Y_i estacionario por s^(4/5)*(wbar/w0).
    Usa la demanda laboral literal y las identidades productivas ya demostradas.
-/
theorem output_scaling {R : ℝ} (hR : R ∈ boundaryInterval)
    (i : FirmType) :
    boundaryOutput R i =
      output i * boundaryCapitalScale R ^ (4 / 5 : ℝ) *
        (wage / boundaryWage R) := by
  have hs := (boundary_scale_and_investment_domain hR).1
  have hcf := boundaryCapital_two_fifths hR i
  have hlf := boundaryLabor_eq_parent_mul_factor hR i
  have hhalf := laborFactor_half_power hR
  have hpow :
      (labor i * boundaryLaborFactor R) ^ (1 / 2 : ℝ) =
        labor i ^ (1 / 2 : ℝ) * boundaryLaborFactor R ^ (1 / 2 : ℝ) :=
    Real.mul_rpow (labor_pos i).le (laborFactor_pos hR).le
  change technology i * boundaryCapital R i ^ (2 / 5 : ℝ) *
      boundaryLabor R i ^ (1 / 2 : ℝ) = _
  rw [hcf, hlf, hpow, hhalf]
  calc
    technology i *
        (boundaryCapitalScale R ^ (2 / 5 : ℝ) * capital i ^ (2 / 5 : ℝ)) *
        (labor i ^ (1 / 2 : ℝ) *
          (boundaryCapitalScale R ^ (2 / 5 : ℝ) * (wage / boundaryWage R))) =
        (technology i * capital i ^ (2 / 5 : ℝ) *
          labor i ^ (1 / 2 : ℝ)) *
          (boundaryCapitalScale R ^ (2 / 5 : ℝ)) ^ (2 : ℕ) *
          (wage / boundaryWage R) := by ring
    _ = _ := by
      rw [production_identity i, boundaryScale_two_fifths_sq hR]

theorem aggregateOutput_scaling {R : ℝ} (hR : R ∈ boundaryInterval) :
    boundaryAggregateOutput R =
      aggregateOutput * boundaryCapitalScale R ^ (4 / 5 : ℝ) *
        (wage / boundaryWage R) := by
  change (boundaryOutput R .H + boundaryOutput R .L) / 2 = _
  rw [output_scaling hR .H, output_scaling hR .L]
  unfold aggregateOutput average
  ring

noncomputable def scalePow (R : ℝ) : ℝ :=
  boundaryCapitalScale R ^ (4 / 5 : ℝ)

noncomputable def workerRatio (R : ℝ) : ℝ :=
  boundaryWorkerConsumption R / workerConsumption

noncomputable def wageRoot (R : ℝ) : ℝ :=
  (workerRatio R * scalePow R) ^ (1 / 3 : ℝ)

private theorem scalePow_pos {R : ℝ} (hR : R ∈ boundaryInterval) :
    0 < scalePow R :=
  Real.rpow_pos_of_pos (boundary_scale_and_investment_domain hR).1 _

private theorem workerRatio_pos {R : ℝ} (hR : R ∈ boundaryInterval) :
    0 < workerRatio R :=
  div_pos (boundaryWorkerConsumption_pos hR) workerConsumption_pos

private theorem wageRoot_pos {R : ℝ} (hR : R ∈ boundaryInterval) :
    0 < wageRoot R :=
  Real.rpow_pos_of_pos
    (mul_pos (workerRatio_pos hR) (scalePow_pos hR)) _

private theorem wageRoot_cube {R : ℝ} (hR : R ∈ boundaryInterval) :
    wageRoot R ^ (3 : ℕ) = workerRatio R * scalePow R := by
  unfold wageRoot
  simpa only [one_div] using
    (Real.rpow_inv_natCast_pow
      (mul_nonneg (workerRatio_pos hR).le (scalePow_pos hR).le)
      (n := 3) (by norm_num))

private theorem output_ratio_eq {R : ℝ} (hR : R ∈ boundaryInterval) :
    boundaryAggregateOutput R / aggregateOutput =
      scalePow R / wageRoot R := by
  have hY := aggregateOutput_scaling hR
  have hw : boundaryWage R = wage * wageRoot R := by rfl
  rw [hY, hw]
  unfold scalePow
  field_simp [ne_of_gt aggregates_pos.2.1, ne_of_gt wage_pos,
    ne_of_gt (wageRoot_pos hR)] <;> ring

/-- La identidad cubica evita manipular directamente una potencia 8/15. -/
private theorem output_ratio_cube {R : ℝ} (hR : R ∈ boundaryInterval) :
    (boundaryAggregateOutput R / aggregateOutput) ^ (3 : ℕ) =
      scalePow R ^ (2 : ℕ) / workerRatio R := by
  rw [output_ratio_eq hR]
  have hg := wageRoot_cube hR
  have hz := scalePow_pos hR
  have hu := workerRatio_pos hR
  calc
    (scalePow R / wageRoot R) ^ (3 : ℕ) =
        scalePow R ^ (3 : ℕ) / wageRoot R ^ (3 : ℕ) := by ring
    _ = scalePow R ^ (3 : ℕ) / (workerRatio R * scalePow R) := by rw [hg]
    _ = scalePow R ^ (2 : ℕ) / workerRatio R := by
      field_simp [ne_of_gt hu, ne_of_gt hz] <;> ring


/-- Exact source output power identity: normalized production is a
fifteenth root, not a decimal surrogate. The proof uses the literal
worker-consumption rule and the already established cubic aggregate-output
scaling. It leaves no endpoint sign or numerical box as an assumption. -/
theorem output_ratio_fifteenth_power {R : ℝ}
    (hR : R ∈ boundaryInterval) :
    (boundaryAggregateOutput R / aggregateOutput) ^ (15 : ℕ) =
      boundaryCapitalScale R ^ (8 : ℕ) *
        ((99 / 100 : ℝ) * boundaryDepositRate R) ^ (5 : ℕ) := by
  have hd : 0 < (99 / 100 : ℝ) * boundaryDepositRate R :=
    mul_pos (by norm_num) (boundaryDepositRate_pos hR)
  have hworker :
      workerRatio R =
        1 / ((99 / 100 : ℝ) * boundaryDepositRate R) := by
    unfold workerRatio boundaryWorkerConsumption
    field_simp [ne_of_gt workerConsumption_pos,
      ne_of_gt (boundaryDepositRate_pos hR)] <;> ring
  have hbase := output_ratio_cube hR
  rw [hworker] at hbase
  unfold scalePow at hbase
  have hcube :
      (boundaryAggregateOutput R / aggregateOutput) ^ (3 : ℕ) =
        (boundaryCapitalScale R ^ (4 / 5 : ℝ)) ^ (2 : ℕ) *
          ((99 / 100 : ℝ) * boundaryDepositRate R) := by
    calc
      _ = (boundaryCapitalScale R ^ (4 / 5 : ℝ)) ^ (2 : ℕ) /
            (1 / ((99 / 100 : ℝ) * boundaryDepositRate R)) := hbase
      _ = _ := by field_simp [ne_of_gt hd] <;> ring
  have hs8 :
      ((boundaryCapitalScale R ^ (4 / 5 : ℝ)) ^ (2 : ℕ)) ^ (5 : ℕ) =
        boundaryCapitalScale R ^ (8 : ℕ) := by
    calc
      _ = (boundaryCapitalScale R ^ (4 / 5 : ℝ)) ^ (10 : ℕ) := by ring
      _ = boundaryCapitalScale R ^ (8 : ℕ) := by
        have h := Real.rpow_mul
          (boundary_scale_and_investment_domain hR).1.le
          (4 / 5 : ℝ) (10 : ℝ)
        norm_num [Real.rpow_natCast] at h ⊢
        exact h.symm
  calc
    (boundaryAggregateOutput R / aggregateOutput) ^ (15 : ℕ) =
      ((boundaryAggregateOutput R / aggregateOutput) ^ (3 : ℕ)) ^ (5 : ℕ) := by ring
    _ = ((boundaryCapitalScale R ^ (4 / 5 : ℝ)) ^ (2 : ℕ) *
          ((99 / 100 : ℝ) * boundaryDepositRate R)) ^ (5 : ℕ) := by rw [hcube]
    _ = ((boundaryCapitalScale R ^ (4 / 5 : ℝ)) ^ (2 : ℕ)) ^ (5 : ℕ) *
          ((99 / 100 : ℝ) * boundaryDepositRate R) ^ (5 : ℕ) := by ring
    _ = _ := by rw [hs8]

private theorem scalePow_strictMonoOn :
    StrictMonoOn scalePow boundaryInterval := by
  intro x hx y hy hxy
  unfold scalePow
  exact Real.rpow_lt_rpow
    (boundary_scale_and_investment_domain hx).1.le
    (capitalScale_strictMonoOn hx hy hxy) (by norm_num)

private theorem workerRatio_strictAntiOn :
    StrictAntiOn workerRatio boundaryInterval := by
  intro x hx y hy hxy
  unfold workerRatio
  exact div_lt_div_of_pos_right
    (workerConsumption_strictAntiOn hx hy hxy) workerConsumption_pos

/-- Y0 aumenta: (Y0/Ybar)^3 = z^2/u,
    z=s^(4/5) aumenta y u=CW0/CWbar disminuye. -/
theorem aggregateOutput_strictMonoOn :
    StrictMonoOn boundaryAggregateOutput boundaryInterval := by
  intro x hx y hy hxy
  have hz0 := scalePow_pos hx
  have hz1 := scalePow_pos hy
  have hu0 := workerRatio_pos hx
  have hu1 := workerRatio_pos hy
  have hzp := scalePow_strictMonoOn hx hy hxy
  have hup := workerRatio_strictAntiOn hx hy hxy
  have hzsq : scalePow x ^ (2 : ℕ) < scalePow y ^ (2 : ℕ) := by
    have hprod := mul_pos (sub_pos.mpr hzp) (add_pos hz1 hz0)
    nlinarith
  have hcross : scalePow x ^ (2 : ℕ) * workerRatio y <
      scalePow y ^ (2 : ℕ) * workerRatio x := by
    calc
      _ < scalePow y ^ (2 : ℕ) * workerRatio y :=
        mul_lt_mul_of_pos_right hzsq hu1
      _ < scalePow y ^ (2 : ℕ) * workerRatio x :=
        mul_lt_mul_of_pos_left hup (sq_pos_of_pos hz1)
  have hratio : scalePow x ^ (2 : ℕ) / workerRatio x <
      scalePow y ^ (2 : ℕ) / workerRatio y :=
    (div_lt_div_iff₀ hu0 hu1).2 hcross
  have hcubex := output_ratio_cube hx
  have hcubey := output_ratio_cube hy
  have hcube : (boundaryAggregateOutput x / aggregateOutput) ^ (3 : ℕ) <
      (boundaryAggregateOutput y / aggregateOutput) ^ (3 : ℕ) := by
    rw [hcubex, hcubey]
    exact hratio
  have hratiolt : boundaryAggregateOutput x / aggregateOutput <
      boundaryAggregateOutput y / aggregateOutput := by
    have hratpos : 0 < boundaryAggregateOutput y / aggregateOutput := by
      rw [output_ratio_eq hy]
      exact div_pos hz1 (wageRoot_pos hy)
    by_contra hnot
    have hle : boundaryAggregateOutput y / aggregateOutput ≤
        boundaryAggregateOutput x / aggregateOutput := le_of_not_gt hnot
    have hp : (boundaryAggregateOutput y / aggregateOutput) ^ (3 : ℕ) ≤
        (boundaryAggregateOutput x / aggregateOutput) ^ (3 : ℕ) := by
      gcongr
    linarith
  have hmul := (div_lt_div_iff₀ aggregates_pos.2.1 aggregates_pos.2.1).1 hratiolt
  by_contra hnot
  have hge : boundaryAggregateOutput y ≤ boundaryAggregateOutput x := le_of_not_gt hnot
  have hmulOpp := mul_le_mul_of_nonneg_right hge aggregates_pos.2.1.le
  linarith

/-! ## Continuidad pieza por pieza -/

theorem depositRate_continuousOn :
    ContinuousOn boundaryDepositRate boundaryInterval := by
  have hrr : ContinuousOn boundaryReserveRate boundaryInterval := by
    unfold boundaryReserveRate
    exact continuousOn_id.sub continuousOn_const
  have hratio : ContinuousOn
      (fun R => boundaryPaymentTerm / boundaryReserveRate R) boundaryInterval := by
    exact continuousOn_const.div hrr (by
      intro R hR
      exact ne_of_gt (boundary_rate_domain hR).2)
  have hden : ContinuousOn
      (fun R => 1 + boundaryPaymentTerm / boundaryReserveRate R) boundaryInterval :=
    continuousOn_const.add hratio
  have hnum : ContinuousOn
      (fun R => boundaryReserveRate R + (9 / 10) * meanSlope +
        (1 / 10) * boundaryPaymentTerm) boundaryInterval := by
    exact (hrr.add continuousOn_const).add continuousOn_const
  unfold boundaryDepositRate
  exact hnum.div hden (by
    intro R hR
    have hpos := (boundary_rate_domain hR).2
    have hbpos := paymentTerm_pos
    have hq : 0 < 1 + boundaryPaymentTerm / boundaryReserveRate R := by
      have : 0 < boundaryPaymentTerm / boundaryReserveRate R :=
        div_pos hbpos hpos
      linarith
    exact ne_of_gt hq)

theorem capitalScale_continuousOn :
    ContinuousOn boundaryCapitalScale boundaryInterval := by
  have hR : ContinuousOn (fun R : ℝ => R) boundaryInterval := continuousOn_id
  have hq : ContinuousOn boundaryCapitalPrice boundaryInterval := by
    unfold boundaryCapitalPrice
    exact continuousOn_const.div hR (by
      intro R hmem
      exact ne_of_gt (boundary_rate_domain hmem).1)
  have hden : ContinuousOn
      (fun R => (39 / 40 : ℝ) + (boundaryCapitalPrice R - 1) / (1 / 2))
      boundaryInterval := by
    exact continuousOn_const.add
      ((hq.sub continuousOn_const).div continuousOn_const (by
        intro R hmem
        norm_num))
  unfold boundaryCapitalScale
  exact continuousOn_const.div hden (by
    intro R hR
    have hp : 1 < boundaryCapitalPrice R := by
      have hV := continuationReturn_L_gt_boundaryHi
      have hRp := (boundary_rate_domain hR).1
      have hRupper := hR.2
      unfold boundaryCapitalPrice
      exact (one_lt_div hRp).2 (lt_of_le_of_lt hRupper hV)
    have hd : 0 < (39 / 40 : ℝ) + (boundaryCapitalPrice R - 1) / (1 / 2) := by
      have : 0 < (boundaryCapitalPrice R - 1) / (1 / 2) :=
        div_pos (sub_pos.mpr hp) (by norm_num)
      linarith
    exact ne_of_gt hd)

theorem workerConsumption_continuousOn :
    ContinuousOn boundaryWorkerConsumption boundaryInterval := by
  unfold boundaryWorkerConsumption
  exact continuousOn_const.div
    (continuousOn_const.mul depositRate_continuousOn)
    (by intro R hR
        exact ne_of_gt (mul_pos (by norm_num) (depositRate_pos hR)))

theorem firmConsumption_continuousOn (i : FirmType) :
    ContinuousOn (fun R => boundaryConsumption R i) boundaryInterval := by
  have hq : ContinuousOn (fun R : ℝ => firmConsumptionNumerator i / R)
      boundaryInterval := by
    exact continuousOn_const.div continuousOn_id (by
      intro R hR
      exact ne_of_gt (boundary_rate_domain hR).1)
  exact hq.congr (by
    intro R hR
    exact firmConsumption_eq_numerator_div (boundary_rate_domain hR).1 i)

theorem capitalCost_continuousOn :
    ContinuousOn boundaryCapitalCost boundaryInterval := by
  have hs := capitalScale_continuousOn
  have hright : ContinuousOn
      (fun R => aggregateCapital * (41 / 80 + 1 / (4 * boundaryCapitalScale R) -
        (4719 / 6400) * boundaryCapitalScale R)) boundaryInterval := by
    have hrec : ContinuousOn (fun R => 1 / (4 * boundaryCapitalScale R))
        boundaryInterval :=
      continuousOn_const.div (continuousOn_const.mul hs) (by
        intro R hR
        exact ne_of_gt (mul_pos (by norm_num)
          (boundary_scale_and_investment_domain hR).1))
    have hlinear : ContinuousOn
        (fun R => 41 / 80 + 1 / (4 * boundaryCapitalScale R) -
          (4719 / 6400) * boundaryCapitalScale R) boundaryInterval :=
      (continuousOn_const.add hrec).sub (continuousOn_const.mul hs)
    exact continuousOn_const.mul hlinear
  exact hright.congr (by
    intro R hR
    exact boundaryCapitalCost_scale_formula
      (boundary_scale_and_investment_domain hR).1)

theorem aggregateOutput_continuousOn :
    ContinuousOn boundaryAggregateOutput boundaryInterval := by
  have hs := capitalScale_continuousOn
  have hc := workerConsumption_continuousOn
  have hpow : ContinuousOn (fun R => boundaryCapitalScale R ^ (4 / 5 : ℝ))
      boundaryInterval :=
    hs.rpow_const (by
      intro R hR
      exact Or.inr (by norm_num))
  have hinner : ContinuousOn
      (fun R => (boundaryWorkerConsumption R / workerConsumption) *
        boundaryCapitalScale R ^ (4 / 5 : ℝ)) boundaryInterval := by
    have hr : ContinuousOn
        (fun R => boundaryWorkerConsumption R / workerConsumption)
        boundaryInterval :=
      hc.div continuousOn_const (by
        intro R hmem
        exact ne_of_gt workerConsumption_pos)
    exact hr.mul hpow
  have hroot : ContinuousOn
      (fun R => ((boundaryWorkerConsumption R / workerConsumption) *
        boundaryCapitalScale R ^ (4 / 5 : ℝ)) ^ (1 / 3 : ℝ))
      boundaryInterval :=
    hinner.rpow_const (by
      intro R hR
      exact Or.inr (by norm_num))
  have hw : ContinuousOn boundaryWage boundaryInterval := by
    unfold boundaryWage
    exact continuousOn_const.mul hroot
  have hright : ContinuousOn
      (fun R => aggregateOutput * boundaryCapitalScale R ^ (4 / 5 : ℝ) *
        (wage / boundaryWage R)) boundaryInterval := by
    have hratio : ContinuousOn (fun R => wage / boundaryWage R)
        boundaryInterval := continuousOn_const.div hw (by
          intro R hR
          exact ne_of_gt (boundaryWage_pos hR))
    exact (continuousOn_const.mul hpow).mul hratio
  exact hright.congr (by
    intro R hR
    exact aggregateOutput_scaling hR)

theorem resourceResidual_continuousOn :
    ContinuousOn boundaryResourceResidual boundaryInterval := by
  have hH := firmConsumption_continuousOn .H
  have hL := firmConsumption_continuousOn .L
  have hAvg : ContinuousOn
      (fun R => average (boundaryConsumption R)) boundaryInterval := by
    change ContinuousOn
      (fun R => (boundaryConsumption R .H + boundaryConsumption R .L) / 2)
      boundaryInterval
    exact (hH.add hL).div continuousOn_const (by intro; norm_num)
  unfold boundaryResourceResidual
  exact ((aggregateOutput_continuousOn.sub workerConsumption_continuousOn).sub
    hAvg).sub capitalCost_continuousOn

/-- El paquete analitico se obtiene de lemas economicos internos, sin
    suponer continuidad/monotonia como campos. Los signos de los extremos
    siguen siendo una obligacion distinta. -/
theorem boundary_analyticPackage : BoundaryAnalyticPackage := by
  refine ⟨resourceResidual_continuousOn, ?_⟩
  exact boundaryResourceResidual_strictMonoOn_of_components
    aggregateOutput_strictMonoOn
    workerConsumption_strictAntiOn
    (firmConsumption_strictAntiOn .H)
    (firmConsumption_strictAntiOn .L)
    capitalCost_strictAntiOn

/-- Corolario aun condicional SOLO en los dos signos del bracket.
    No se reinterpreta el certificado JSON como una prueba Lean. -/
theorem boundary_uniqueRoot_of_signs (HS : BoundaryEndpointSigns) :
    ExactRootOn boundaryResourceResidual boundaryLo boundaryHi :=
  boundary_exactRootOn boundary_analyticPackage HS

end ProposedBoundaryAnalyticPackage
end Ventura26LiquidityAllocation
