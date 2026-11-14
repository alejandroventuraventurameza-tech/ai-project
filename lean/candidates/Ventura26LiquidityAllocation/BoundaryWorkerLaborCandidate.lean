import Ventura26LiquidityAllocation.BoundaryFullPrefixCandidate

/-!
# FOC laboral del nodo de frontera: PROPUESTA SIN COMPILAR

Este modulo descarga la unica interfaz real que quedo en
BoundaryFullPrefixCandidate. La prueba usa solo homogeneidad de la demanda
laboral, positividad de las bases y los lemas Real.mul_rpow / Real.rpow_mul del
Mathlib fijado. No introduce un residual como hipotesis.

Dependencia propuesta BoundaryFullPrefixCandidate.lean SHA256:
a6267df530c19760396c653e1703209fe0dcbc07194364a51427e97d1942451a.

Toda la cadena sigue SIN COMPILAR en esta conversacion.
-/

open scoped BigOperators
open Set

namespace Ventura26LiquidityAllocation
namespace ProposedBoundaryWorkerLabor

open ProposedStationaryBank
open ProposedStationaryRealScale
open ProposedStationaryProductionBridge
open ProposedBoundaryBridge
open ProposedBoundaryResourceRoot
open ProposedBoundaryFullPrefix

noncomputable def boundaryLaborFactor (R : ℝ) : ℝ :=
  boundaryCapitalScale R ^ (4 / 5 : ℝ) *
    (wage / boundaryWage R) ^ (2 : ℕ)

theorem boundaryDepositRate_pos {R : ℝ} (hR : R ∈ boundaryInterval) :
    0 < boundaryDepositRate R := by
  have hrr := (boundary_rate_domain hR).2
  rcases slope_bounds with ⟨_hm0, _hmhi, hg0, _hghi, hmgap⟩
  have hb0 : 0 < boundaryPaymentTerm := by
    unfold boundaryPaymentTerm
    positivity
  rw [boundaryDepositRate_rewrite R (ne_of_gt hrr) (ne_of_gt (add_pos hrr hb0))]
  have hterm : 0 <
      ((9 / 10 : ℝ) * (meanSlope - boundaryPaymentTerm)) *
        boundaryReserveRate R /
          (boundaryReserveRate R + boundaryPaymentTerm) := by
    unfold boundaryPaymentTerm
    positivity
  linarith

theorem boundaryWorkerConsumption_pos {R : ℝ} (hR : R ∈ boundaryInterval) :
    0 < boundaryWorkerConsumption R := by
  unfold boundaryWorkerConsumption
  exact div_pos workerConsumption_pos
    (mul_pos (by norm_num) (boundaryDepositRate_pos hR))

theorem boundaryWage_pos {R : ℝ} (hR : R ∈ boundaryInterval) :
    0 < boundaryWage R := by
  have hc := boundaryWorkerConsumption_pos hR
  have hs := (boundary_scale_and_investment_domain hR).1
  have hfactor : 0 <
      (boundaryWorkerConsumption R / workerConsumption) *
        boundaryCapitalScale R ^ (4 / 5 : ℝ) := by
    exact mul_pos (div_pos hc workerConsumption_pos)
      (Real.rpow_pos_of_pos hs (4 / 5 : ℝ))
  unfold boundaryWage
  exact mul_pos wage_pos (Real.rpow_pos_of_pos hfactor (1 / 3 : ℝ))

/-- La potencia 2/5 de cada capital escala multiplicativamente. -/
theorem boundaryCapital_two_fifths {R : ℝ} (hR : R ∈ boundaryInterval)
    (i : FirmType) :
    boundaryCapital R i ^ (2 / 5 : ℝ) =
      boundaryCapitalScale R ^ (2 / 5 : ℝ) * capital i ^ (2 / 5 : ℝ) := by
  unfold boundaryCapital
  exact Real.mul_rpow
    (boundary_scale_and_investment_domain hR).1.le (capital_pos i).le

/-- Elevar s^(2/5) al cuadrado produce s^(4/5). -/
theorem boundaryScale_two_fifths_sq {R : ℝ} (hR : R ∈ boundaryInterval) :
    (boundaryCapitalScale R ^ (2 / 5 : ℝ)) ^ (2 : ℕ) =
      boundaryCapitalScale R ^ (4 / 5 : ℝ) := by
  have h := Real.rpow_mul
    (boundary_scale_and_investment_domain hR).1.le (2 / 5 : ℝ) (2 : ℝ)
  norm_num [Real.rpow_natCast] at h ⊢
  exact h.symm

/-- Demanda de trabajo tipo por tipo bajo la escala comun. -/
theorem boundaryLabor_eq_parent_mul_factor {R : ℝ}
    (hR : R ∈ boundaryInterval) (i : FirmType) :
    boundaryLabor R i = labor i * boundaryLaborFactor R := by
  have hw0 := boundaryWage_pos hR
  have hw := wage_pos
  have hcap := boundaryCapital_two_fifths hR i
  have hsPow := boundaryScale_two_fifths_sq hR
  unfold boundaryLabor boundaryLaborFactor
  rw [show (1 / (1 - (1 / 2 : ℝ)) : ℝ) = 2 by norm_num,
    Real.rpow_two, hcap]
  have hparent := laborInput_sq_eq i
  unfold laborInput at hparent
  rw [← hparent]
  rw [← hsPow]
  field_simp [ne_of_gt hw0, ne_of_gt hw] <;> ring

noncomputable def boundaryAggregateLabor (R : ℝ) : ℝ :=
  average (boundaryLabor R)

theorem boundaryAggregateLabor_eq_parent_mul_factor {R : ℝ}
    (hR : R ∈ boundaryInterval) :
    boundaryAggregateLabor R = aggregateLabor * boundaryLaborFactor R := by
  rw [show boundaryAggregateLabor R =
      (boundaryLabor R .H + boundaryLabor R .L) / 2 by
        rfl,
    boundaryLabor_eq_parent_mul_factor hR .H,
    boundaryLabor_eq_parent_mul_factor hR .L]
  unfold aggregateLabor average
  ring

theorem boundary_localAggregateLabor_eq {G R : ℝ} :
    localPrefixAggregateLabor (boundaryPrimitives G R) (boundaryZeroData G R) =
      boundaryAggregateLabor R := by
  unfold localPrefixAggregateLabor boundaryAggregateLabor average
  rw [sum_firmType_eq_H_add_L]
  simp [boundaryPrimitives, ProposedStationaryPrimitives.primitives,
    boundaryZeroData, boundaryZeroSeed, boundaryFirmDateData,
    boundaryFirmDateSeed, boundaryFirmControls, boundaryControls,
    localPrefixLabor, boundaryLabor] <;> ring

/-- El factor cubico dentro del salario. -/
noncomputable def boundaryWageCubeFactor (R : ℝ) : ℝ :=
  (boundaryWorkerConsumption R / workerConsumption) *
    boundaryCapitalScale R ^ (4 / 5 : ℝ)

 theorem boundaryWageCubeFactor_pos {R : ℝ} (hR : R ∈ boundaryInterval) :
    0 < boundaryWageCubeFactor R := by
  unfold boundaryWageCubeFactor
  exact mul_pos
    (div_pos (boundaryWorkerConsumption_pos hR) workerConsumption_pos)
    (Real.rpow_pos_of_pos (boundary_scale_and_investment_domain hR).1 (4 / 5 : ℝ))

 theorem boundaryWageCube_root {R : ℝ} (hR : R ∈ boundaryInterval) :
    (boundaryWageCubeFactor R ^ (1 / 3 : ℝ)) ^ (3 : ℕ) =
      boundaryWageCubeFactor R := by
  have h := Real.rpow_inv_natCast_pow
    (boundaryWageCubeFactor_pos hR).le (n := 3) (by norm_num)
  simpa only [one_div] using h

 theorem boundaryWage_eq_parent_mul_cubeRoot (R : ℝ) :
    boundaryWage R = wage * boundaryWageCubeFactor R ^ (1 / 3 : ℝ) := by
  rfl

/-- Identidad salarial exacta de fecha cero. -/
theorem boundary_worker_labor_equation {R : ℝ}
    (hR : R ∈ boundaryInterval) :
    boundaryWage R = boundaryWorkerConsumption R * boundaryAggregateLabor R := by
  let g : ℝ := boundaryWageCubeFactor R ^ (1 / 3 : ℝ)
  have hg0 : 0 < g := Real.rpow_pos_of_pos (boundaryWageCubeFactor_pos hR) _
  have hg3 : g ^ (3 : ℕ) = boundaryWageCubeFactor R := by
    exact boundaryWageCube_root hR
  have hw0 : boundaryWage R = wage * g := by
    exact boundaryWage_eq_parent_mul_cubeRoot R
  have hfactor : boundaryLaborFactor R =
      boundaryCapitalScale R ^ (4 / 5 : ℝ) / g ^ (2 : ℕ) := by
    unfold boundaryLaborFactor
    rw [hw0]
    field_simp [ne_of_gt wage_pos, ne_of_gt hg0] <;> ring
  rw [boundaryAggregateLabor_eq_parent_mul_factor hR, hfactor, hw0,
    worker_labor_equation]
  unfold boundaryWageCubeFactor at hg3
  have hcubeScaled :
      workerConsumption * g ^ (3 : ℕ) =
        boundaryWorkerConsumption R * boundaryCapitalScale R ^ (4 / 5 : ℝ) := by
    rw [hg3]
    field_simp [ne_of_gt workerConsumption_pos] <;> ring
  have hscaled :
      workerConsumption * aggregateLabor * g ^ (3 : ℕ) =
        aggregateLabor * boundaryWorkerConsumption R *
          boundaryCapitalScale R ^ (4 / 5 : ℝ) := by
    calc
      _ = aggregateLabor * (workerConsumption * g ^ (3 : ℕ)) := by ring
      _ = aggregateLabor *
          (boundaryWorkerConsumption R * boundaryCapitalScale R ^ (4 / 5 : ℝ)) := by
            rw [hcubeScaled]
      _ = _ := by ring
  field_simp [ne_of_gt workerConsumption_pos, ne_of_gt hg0]
  nlinarith only [hscaled]

/-- Descarga la fila 3 literal del sistema reducido. -/
theorem boundary_workerLabor_row_zero (G : ℝ) {R : ℝ}
    (hR : R ∈ boundaryInterval) :
    localReducedRemainingResidual (boundaryPrimitives G R) (boundaryZeroData G R) 3 = 0 := by
  change boundaryWage R - 1 *
      boundaryWorkerConsumption R ^ (1 : ℝ) *
        localPrefixAggregateLabor (boundaryPrimitives G R) (boundaryZeroData G R) ^ (1 : ℝ) = 0
  simp only [Real.rpow_one, one_mul]
  rw [boundary_localAggregateLabor_eq, boundary_worker_labor_equation hR]
  ring

 theorem boundary_workerLabor_package (G : ℝ) {R : ℝ}
    (hR : R ∈ boundaryInterval) : BoundaryWorkerLaborPackage G R :=
  ⟨boundary_workerLabor_row_zero G hR⟩

/-- Con la FOC laboral descargada, el cierre de 33 filas ya solo recibe los
paquetes de existencia/unicidad de la raiz. -/
theorem boundary_full_prefix_equations_from_root
    (G : ℝ) (HA : BoundaryAnalyticPackage) (HS : BoundaryEndpointSigns)
    (branch : LocalPrefixBranch) :
    LocalReducedPrefixEquationsHold branch
      (boundaryPrimitives G (boundaryRoot HA HS))
      (boundaryInitialState G (boundaryRoot HA HS))
      (boundaryCoordinates (boundaryRoot HA HS)) .dateOne .recurrent boundaryTail := by
  have hspec := boundaryRoot_spec HA HS
  have hmem : boundaryRoot HA HS ∈ boundaryInterval := ⟨hspec.1, hspec.2.1⟩
  exact boundary_full_prefix_equations G HA HS
    (boundary_workerLabor_package G hmem) branch

end ProposedBoundaryWorkerLabor
end Ventura26LiquidityAllocation
