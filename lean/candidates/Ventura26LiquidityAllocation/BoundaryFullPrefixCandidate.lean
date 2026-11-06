import Ventura26LiquidityAllocation.BoundaryResourceRootCandidate

/-!
# Ensamblaje del prefijo completo de frontera: PROPUESTA SIN COMPILAR

Proyecto: alejandroventuraventurameza-tech/ai-project.
Rama: work/chat-continuity.
Commit: 16e24fe828a5a0002ef13bb82bae9e295f190f86.
AppliedModelingLib: 194edcc95df74806a39b961d10dedddc6e730cce.
Mathlib: 5450b53e5ddc75d46418fabb605edbf36bd0beb6.
Lean previsto: leanprover/lean4:v4.30.0-rc2.

Dependencia propuesta BoundaryResourceRootCandidate.lean SHA256:
98e0e4f27278eff5dc08b52c1c4d9107404ebd347a4228d135ad2616041e318b.

Objetivo:
* reconstruir el carrier literal 7+10+6+10=33 del prefijo usado por
  code/v0m/cierre_interno_2026_10_17/finite_bridge.py;
* introducir las innovaciones monetarias de fecha 0 y 1 que el certificado
  realmente usa, en lugar de reutilizar incorrectamente las innovaciones
  estacionarias nulas;
* cerrar algebraicamente las filas bancarias, monetarias y de renovacion;
* reducir las 33 igualdades a la raiz de recursos ya aislada y a una sola
  identidad real de oferta laboral que involucra potencias reales.

Este modulo no lee JSON ni convierte intervalos decimales en teoremas Lean.
La raiz entra mediante BoundaryAnalyticPackage + BoundaryEndpointSigns del
modulo anterior. La parte que todavia depende de algebra de potencias reales
se mantiene en una interfaz explicita y pequena; no se usa sorry/admit/axiom.

Toda la cadena sigue SIN COMPILAR en esta conversacion.
-/

open scoped BigOperators
open Set

namespace Ventura26LiquidityAllocation
namespace ProposedBoundaryFullPrefix

open ProposedStationaryBank
open ProposedStationaryRealScale
open ProposedStationaryProductionBridge
open ProposedStationaryReducedSystem
open ProposedStationaryPrimitives
open ProposedStationaryInheritedState
open ProposedBoundaryBridge
open ProposedBoundaryResourceRoot

/-! ## La raiz exacta, sin escoger un decimal -/

noncomputable def boundaryRoot
    (HA : BoundaryAnalyticPackage) (HS : BoundaryEndpointSigns) : ℝ :=
  Classical.choose (boundary_exactRootOn HA HS)

theorem boundaryRoot_spec
    (HA : BoundaryAnalyticPackage) (HS : BoundaryEndpointSigns) :
    boundaryLo ≤ boundaryRoot HA HS ∧
      boundaryRoot HA HS ≤ boundaryHi ∧
      boundaryResourceResidual (boundaryRoot HA HS) = 0 :=
  (Classical.choose_spec (boundary_exactRootOn HA HS)).1

/-! ## Cartera bancaria de fecha cero -/

noncomputable def boundaryReserveDepositRatio (R : ℝ) : ℝ :=
  1 / 10 + (boundaryDepositRate R / boundaryReserveRate R - 1 / 10) / 15

noncomputable def boundaryBankEquity (R : ℝ) : ℝ :=
  bankEquity * ProposedStationaryBank.loanRate / R

noncomputable def boundaryBankLoans (R : ℝ) : ℝ :=
  aggregateCredit * ProposedStationaryBank.loanRate / R

noncomputable def boundaryBankDeposits (R : ℝ) : ℝ :=
  (boundaryBankLoans R - boundaryBankEquity R) /
    (1 - boundaryReserveDepositRatio R)

noncomputable def boundaryReservesPre (R : ℝ) : ℝ :=
  boundaryReserveDepositRatio R * boundaryBankDeposits R

/-- En el bracket la razon de reservas queda estrictamente entre cero y uno.
La cota superior deliberadamente es gruesa; solo se necesita excluir el polo
1-h de la reconstruccion de depositos. -/
theorem boundaryReserveDepositRatio_bounds {R : ℝ}
    (hR : R ∈ boundaryInterval) :
    0 < boundaryReserveDepositRatio R ∧ boundaryReserveDepositRatio R < 1 := by
  rcases boundary_rate_domain hR with ⟨hR0, hrr0⟩
  rcases slope_bounds with ⟨hm0, hmhi, hg0, _hghi, hmgap⟩
  have hb0 : 0 < boundaryPaymentTerm := by
    unfold boundaryPaymentTerm
    positivity
  have hc0 : 0 < (9 / 10 : ℝ) * (meanSlope - boundaryPaymentTerm) := by
    have hcGap : 0 < meanSlope - boundaryPaymentTerm := by
      simpa only [boundaryPaymentTerm] using hmgap
    exact mul_pos (by norm_num) hcGap
  have hrd : boundaryReserveRate R < boundaryDepositRate R := by
    rw [boundaryDepositRate_rewrite R (ne_of_gt hrr0) (ne_of_gt (add_pos hrr0 hb0))]
    have hden : 0 < boundaryReserveRate R + boundaryPaymentTerm :=
      add_pos hrr0 hb0
    have hpos : 0 <
        ((9 / 10 : ℝ) * (meanSlope - boundaryPaymentTerm)) *
          boundaryReserveRate R /
            (boundaryReserveRate R + boundaryPaymentTerm) := by
      positivity
    linarith
  have hxi1 : 1 < boundaryDepositRate R / boundaryReserveRate R :=
    (one_lt_div hrr0).2 hrd
  have hrr1 : 1 < boundaryReserveRate R := by
    have hlo := hR.1
    have hloBound : (1 : ℝ) + 7 / 800 < boundaryLo := by
      norm_num [boundaryLo]
    unfold boundaryReserveRate
    linarith
  have hc_lt_rr :
      (9 / 10 : ℝ) * (meanSlope - boundaryPaymentTerm) <
        boundaryReserveRate R := by
    have hclt : (9 / 10 : ℝ) * (meanSlope - boundaryPaymentTerm) < 1 := by
      unfold boundaryPaymentTerm
      nlinarith
    linarith
  have hrd_lt_two_rr : boundaryDepositRate R < 2 * boundaryReserveRate R := by
    rw [boundaryDepositRate_rewrite R (ne_of_gt hrr0) (ne_of_gt (add_pos hrr0 hb0))]
    have hden : 0 < boundaryReserveRate R + boundaryPaymentTerm :=
      add_pos hrr0 hb0
    have hfrac_lt :
        boundaryReserveRate R /
            (boundaryReserveRate R + boundaryPaymentTerm) < 1 := by
      exact (div_lt_one hden).2 (by linarith)
    have hterm_lt :
        ((9 / 10 : ℝ) * (meanSlope - boundaryPaymentTerm)) *
            boundaryReserveRate R /
              (boundaryReserveRate R + boundaryPaymentTerm) <
          (9 / 10 : ℝ) * (meanSlope - boundaryPaymentTerm) := by
      calc
        _ = ((9 / 10 : ℝ) * (meanSlope - boundaryPaymentTerm)) *
              (boundaryReserveRate R /
                (boundaryReserveRate R + boundaryPaymentTerm)) := by ring
        _ < ((9 / 10 : ℝ) * (meanSlope - boundaryPaymentTerm)) * 1 :=
          mul_lt_mul_of_pos_left hfrac_lt hc0
        _ = _ := by ring
    linarith
  have hxi2 : boundaryDepositRate R / boundaryReserveRate R < 2 :=
    (div_lt_iff₀ hrr0).2 hrd_lt_two_rr
  unfold boundaryReserveDepositRatio
  constructor <;> nlinarith

 theorem boundaryBankLoans_gt_equity {R : ℝ}
    (hR : R ∈ boundaryInterval) : boundaryBankEquity R < boundaryBankLoans R := by
  rcases boundary_rate_domain hR with ⟨hR0, _⟩
  have hRbar := loanRate_pos
  have hratio := ProposedStationaryBank.bank_margins_and_pricing
  have hrhi : ProposedStationaryBank.reserveDepositRatio < 1 := by
    linarith [hratio.2.2.2.1]
  have hD := bank_scale_pos.2.1
  have hMltD : reservesPre < bankDeposits := by
    unfold reservesPre
    have : 2 * ProposedStationaryBank.reserveDepositRatio * bankEquity <
        2 * 1 * bankEquity := by
      have hE := bank_scale_pos.1
      nlinarith
    simpa [bankDeposits] using this
  have hBE : bankEquity < aggregateCredit := by
    have hbal := bank_balance
    linarith
  have hfactor : 0 < ProposedStationaryBank.loanRate / R :=
    div_pos hRbar hR0
  calc
    boundaryBankEquity R = bankEquity * (ProposedStationaryBank.loanRate / R) := by
      unfold boundaryBankEquity
      ring
    _ < aggregateCredit * (ProposedStationaryBank.loanRate / R) :=
      mul_lt_mul_of_pos_right hBE hfactor
    _ = boundaryBankLoans R := by
      unfold boundaryBankLoans
      ring

 theorem boundaryBankScale_pos {R : ℝ} (hR : R ∈ boundaryInterval) :
    0 < boundaryBankEquity R ∧ 0 < boundaryBankDeposits R ∧
      0 < boundaryReservesPre R := by
  rcases boundary_rate_domain hR with ⟨hR0, _⟩
  rcases boundaryReserveDepositRatio_bounds hR with ⟨hh0, hh1⟩
  have hE : 0 < boundaryBankEquity R := by
    unfold boundaryBankEquity
    exact div_pos (mul_pos bank_scale_pos.1 loanRate_pos) hR0
  have hgap : 0 < boundaryBankLoans R - boundaryBankEquity R :=
    sub_pos.mpr (boundaryBankLoans_gt_equity hR)
  have hD : 0 < boundaryBankDeposits R := by
    unfold boundaryBankDeposits
    exact div_pos hgap (sub_pos.mpr hh1)
  have hM : 0 < boundaryReservesPre R := by
    unfold boundaryReservesPre
    positivity
  exact ⟨hE, hD, hM⟩

/-! ## Innovaciones anunciadas: las mismas ecuaciones del certificado -/

noncomputable def boundaryReserveRateInnovationZero (R : ℝ) : ℝ :=
  Real.log (boundaryReserveRate R) -
    ((1 / 2) * Real.log ProposedStationaryBank.reserveRate +
      (1 / 2) *
        (Real.log ProposedStationaryBank.reserveRate +
          (1 / 8) * Real.log (boundaryAggregateOutput R / aggregateOutput)))

noncomputable def boundaryReserveQuantityInnovationZero (R : ℝ) : ℝ :=
  Real.log (boundaryReservesPre R) -
    ((1 / 2) * Real.log reservesPre + (1 / 2) * Real.log reservesPre)

noncomputable def boundaryReserveRateInnovationOne (R : ℝ) : ℝ :=
  Real.log ProposedStationaryBank.reserveRate -
    ((1 / 2) * Real.log (boundaryReserveRate R) +
      (1 / 2) * Real.log ProposedStationaryBank.reserveRate)

noncomputable def boundaryReserveQuantityInnovationOne (R : ℝ) : ℝ :=
  Real.log reservesPre -
    ((1 / 2) * Real.log (boundaryReservesPre R) +
      (1 / 2) * Real.log reservesPre)

noncomputable def boundaryPrimitives (G R : ℝ) : Primitives LocalBridgePhase :=
  { primitives G with
    reserveRateInnovation := fun phase ↦
      match phase with
      | .dateZero => boundaryReserveRateInnovationZero R
      | .dateOne => boundaryReserveRateInnovationOne R
      | .recurrent => 0
    reserveQuantityInnovation := fun phase ↦
      match phase with
      | .dateZero => boundaryReserveQuantityInnovationZero R
      | .dateOne => boundaryReserveQuantityInnovationOne R
      | .recurrent => 0 }

 theorem boundary_stationary_parameters (G R : ℝ) :
    StationaryParameters (boundaryPrimitives G R) := by
  exact
    { toStationaryRealParameters :=
        { alpha_eq := rfl
          beta_eq := rfl
          productivity_eq := fun _ ↦ rfl
          mass_eq := fun _ ↦ rfl
          depreciation_eq := rfl
          pledgeability_eq := fun _ ↦ rfl
          entrepreneurDiscount_eq := rfl
          workerDiscount_eq := rfl
          laborScale_eq := rfl
          workerRiskAversion_eq := rfl
          laborCurvature_eq := rfl
          capitalAdjustmentCost_eq := rfl
          priceElasticity_eq := rfl }
      bankExit_eq := rfl
      bankSeedShare_eq := rfl
      matchingIntensity_eq := rfl
      reserveRateSteady_eq := rfl
      reserveQuantitySteady_eq := rfl
      outputReference_eq := rfl }

 theorem boundary_binary_payment_law (G R : ℝ) :
    BinarySymmetricPaymentLaw (boundaryPrimitives G R) 0 1 (1 / 5) := by
  simpa [boundaryPrimitives] using binary_payment_law G

/-! ## Los 33 portadores del prefijo -/

noncomputable def boundaryZeroSeed (G R : ℝ) : LocalPrefixDateData where
  currentCapital := boundaryCapital R
  inheritedFace := firmFace
  currentBankFace := boundaryBankEquity R
  lagReserveRate := ProposedStationaryBank.reserveRate
  lagReservesPre := reservesPre
  controls := boundaryControls R
  nextCapital := capital
  nextFace := firmFace
  nextBankFace := bankEquity
  currentReserveRate := boundaryReserveRate R
  currentReservesPre := boundaryReservesPre R
  nextControls := controls
  currentAggregateProductivity := 1
  nextAggregateProductivity := 1
  reserveRateInnovation := boundaryReserveRateInnovationZero R
  reserveQuantityInnovation := boundaryReserveQuantityInnovationZero R
  reserveRequirement := 1 / 10
  corridorWidth := 1 / 50

noncomputable def boundaryZeroData (G R : ℝ) : LocalPrefixDateData :=
  boundaryFirmDateData G R (boundaryZeroSeed G R)

noncomputable def boundaryInitialState (G R : ℝ) : InheritedState :=
  { inheritedState G with
    capital := boundaryCapital R
    firmFace := boundaryInheritedFace G R (boundaryZeroSeed G R)
    bankFace := boundaryBankEquity R
    reserveRateLag := ProposedStationaryBank.reserveRate
    reservesPreLag := reservesPre }

noncomputable def boundaryStateOne (R : ℝ) : LocalPrefixStateSeven where
  capitalH := capital .H
  capitalL := capital .L
  firmFaceH := firmFace .H
  firmFaceL := firmFace .L
  bankFace := bankEquity
  reserveRateLag := boundaryReserveRate R
  reservesPreLag := boundaryReservesPre R

noncomputable def boundaryStateTwo : LocalPrefixStateSix := stateSix

noncomputable def boundaryCoordinates (R : ℝ) : LocalPrefixCoordinates where
  stateOne := boundaryStateOne R
  controlsZero := boundaryControls R
  stateTwo := boundaryStateTwo
  controlsOne := controls

noncomputable def boundaryTail : LocalPrefixContinuationRule := fun _ ↦ controls

 theorem boundary_dateZeroData_eq (G R : ℝ) :
    localPrefixDateZeroData (boundaryPrimitives G R) (boundaryInitialState G R)
      (boundaryCoordinates R) .dateOne = boundaryZeroData G R := by
  simp [localPrefixDateZeroData, boundaryPrimitives, boundaryInitialState,
    boundaryCoordinates, boundaryStateOne, boundaryZeroData, boundaryZeroSeed,
    boundaryFirmDateData, boundaryFirmDateSeed, boundaryFirmControls,
    boundaryControls, primitives, localPrefixStateSevenCapital,
    localPrefixStateSevenFace, localBridgeTree] <;>
    (repeat' constructor) <;>
    (first | rfl | (funext i; cases i <;> rfl))

noncomputable def boundaryOneData (G R : ℝ) : LocalPrefixDateData :=
  localPrefixDateOneData (boundaryPrimitives G R) (boundaryCoordinates R)
    .dateOne .recurrent boundaryTail

 theorem boundary_oneData_fields (G R : ℝ) :
    boundaryOneData G R =
      { dateData with
        lagReserveRate := boundaryReserveRate R
        lagReservesPre := boundaryReservesPre R
        reserveRateInnovation := boundaryReserveRateInnovationOne R
        reserveQuantityInnovation := boundaryReserveQuantityInnovationOne R } := by
  simp [boundaryOneData, localPrefixDateOneData, boundaryPrimitives,
    boundaryCoordinates, boundaryStateOne, boundaryStateTwo, boundaryTail,
    dateData, stateSix, controls, primitives, localPrefixStateSevenCapital,
    localPrefixStateSevenFace, localPrefixStateSixCapital,
    localPrefixStateSixFace] <;>
    (repeat' constructor) <;>
    (first | rfl | (funext i; cases i <;> rfl))

/-! ## Filas de fecha cero que no usan la raiz de recursos -/

 theorem boundary_zero_output_eq (G R : ℝ) :
    localPrefixAggregateOutput (boundaryPrimitives G R) (boundaryZeroData G R) =
      boundaryAggregateOutput R := by
  unfold boundaryAggregateOutput boundaryOutput boundaryLabor average
    localPrefixAggregateOutput localPrefixOutput localPrefixLabor
    boundaryZeroData boundaryZeroSeed boundaryFirmDateData boundaryFirmDateSeed
    boundaryFirmControls boundaryControls boundaryCapital boundaryWage
  simp [boundaryPrimitives, primitives, sum_firmType_eq_H_add_L] <;> ring

 theorem boundary_zero_bankRenewal (G R : ℝ) (hR : 0 < R) :
    localReducedRemainingResidual (boundaryPrimitives G R) (boundaryZeroData G R) 0 = 0 := by
  change bankEquity - bankRenewalFactor (boundaryPrimitives G R) * R *
      boundaryBankEquity R / 1 = 0
  rw [bankRenewalFactor_eq (boundaryPrimitives G R)
    (boundary_stationary_parameters G R)]
  unfold boundaryBankEquity
  field_simp [ne_of_gt hR, ne_of_gt loanRate_pos] <;> ring

 theorem boundary_zero_capitalSupply (G R : ℝ)
    (hR : R ∈ boundaryInterval) :
    localReducedRemainingResidual (boundaryPrimitives G R) (boundaryZeroData G R) 1 = 0 := by
  rcases boundary_scale_and_investment_domain hR with ⟨hs0, _hs1, _hI⟩
  have hK := aggregates_pos.1
  have hcapitalCurrent :
      localPrefixAggregateCapital (boundaryPrimitives G R)
          (boundaryZeroData G R).currentCapital =
        boundaryAggregateCapital R := by
    unfold localPrefixAggregateCapital
    rw [sum_firmType_eq_H_add_L]
    change (1 / 2 : ℝ) * boundaryCapital R .H +
      (1 / 2 : ℝ) * boundaryCapital R .L = boundaryAggregateCapital R
    unfold boundaryAggregateCapital boundaryCapital aggregateCapital average
    ring
  have hcapitalNext :
      localPrefixAggregateCapital (boundaryPrimitives G R)
          (boundaryZeroData G R).nextCapital = aggregateCapital := by
    unfold localPrefixAggregateCapital
    rw [sum_firmType_eq_H_add_L]
    change (1 / 2 : ℝ) * capital .H +
      (1 / 2 : ℝ) * capital .L = aggregateCapital
    unfold aggregateCapital average
    ring
  have hinvestment :
      localPrefixInvestment (boundaryPrimitives G R) (boundaryZeroData G R) =
        boundaryInvestment R := by
    unfold localPrefixInvestment
    rw [hcapitalNext, hcapitalCurrent]
    change aggregateCapital - (1 - (1 / 40 : ℝ)) *
      boundaryAggregateCapital R = boundaryInvestment R
    unfold boundaryInvestment
    ring
  change boundaryCapitalPrice R - 1 - (1 / 2 : ℝ) *
      localPrefixInvestment (boundaryPrimitives G R) (boundaryZeroData G R) /
      localPrefixAggregateCapital (boundaryPrimitives G R)
        (boundaryZeroData G R).currentCapital = 0
  rw [hinvestment, hcapitalCurrent]
  have hden :
      (39 / 40 : ℝ) +
          (boundaryCapitalPrice R - 1) / (1 / 2) ≠ 0 := by
    intro hz
    have hzero : boundaryCapitalScale R = 0 := by
      simp [boundaryCapitalScale, hz]
    exact (ne_of_gt hs0) hzero
  have hscale :
      boundaryCapitalScale R *
        ((39 / 40 : ℝ) + (boundaryCapitalPrice R - 1) / (1 / 2)) = 1 := by
    unfold boundaryCapitalScale
    field_simp [hden]
  have hscaleK :=
    congrArg (fun x : ℝ => x * aggregateCapital) hscale
  unfold boundaryInvestment boundaryAggregateCapital
  field_simp [ne_of_gt hK, ne_of_gt hs0]
  nlinarith only [hscaleK]

 theorem boundary_zero_householdEuler (G R : ℝ)
    (hR : R ∈ boundaryInterval) :
    localReducedRemainingResidual (boundaryPrimitives G R) (boundaryZeroData G R) 4 = 0 := by
  have hRD0 : 0 < boundaryDepositRate R := by
    have hrr := (boundary_rate_domain hR).2
    have hgt : boundaryReserveRate R < boundaryDepositRate R := by
      rcases boundaryReserveDepositRatio_bounds hR with ⟨_hh0, _hh1⟩
      rcases slope_bounds with ⟨_hm0, _hmhi, hg0, _hghi, hmgap⟩
      have hb0 : 0 < boundaryPaymentTerm := by unfold boundaryPaymentTerm; positivity
      rw [boundaryDepositRate_rewrite R (ne_of_gt hrr) (ne_of_gt (add_pos hrr hb0))]
      have hpos : 0 <
          ((9 / 10 : ℝ) * (meanSlope - boundaryPaymentTerm)) *
            boundaryReserveRate R /
              (boundaryReserveRate R + boundaryPaymentTerm) := by
        have hcGap : 0 < meanSlope - boundaryPaymentTerm := by
          simpa only [boundaryPaymentTerm] using hmgap
        exact div_pos
          (mul_pos (mul_pos (by norm_num) hcGap) hrr)
          (add_pos hrr hb0)
      linarith
    linarith
  have hCW := workerConsumption_pos
  change 1 - (99 / 100 : ℝ) *
      crraMarginal 1 workerConsumption /
        crraMarginal 1 (boundaryWorkerConsumption R) *
      boundaryDepositRate R / 1 = 0
  simp only [crraMarginal, Real.rpow_neg_one, div_inv_eq_mul]
  unfold boundaryWorkerConsumption
  field_simp [ne_of_gt hRD0, ne_of_gt hCW] <;> ring

 theorem boundary_zero_nkpc (G R : ℝ) :
    localReducedRemainingResidual (boundaryPrimitives G R) (boundaryZeroData G R) 5 = 0 := by
  change 1 - 6 + 6 * (5 / 6 : ℝ) - 150 * 1 * (1 - 1) +
      _ * 150 * _ / _ * 1 * (1 - 1) = 0
  ring

 theorem boundary_zero_reserveRateRule (G R : ℝ) :
    localReducedRemainingResidual (boundaryPrimitives G R) (boundaryZeroData G R) 6 = 0 := by
  simp only [localReducedRemainingResidual]
  rw [boundary_zero_output_eq G R]
  change Real.log (boundaryReserveRate R) -
    ((1 / 2) * Real.log ProposedStationaryBank.reserveRate +
      (1 - (1 / 2 : ℝ)) *
        (Real.log ProposedStationaryBank.reserveRate +
          (3 / 2) * Real.log 1 +
          (1 / 8) * Real.log (boundaryAggregateOutput R / aggregateOutput)) +
      boundaryReserveRateInnovationZero R) = 0
  simp only [Real.log_one, mul_zero, add_zero]
  unfold boundaryReserveRateInnovationZero
  ring

 theorem boundary_zero_reserveQuantityRule (G R : ℝ) :
    localReducedRemainingResidual (boundaryPrimitives G R) (boundaryZeroData G R) 7 = 0 := by
  change Real.log (boundaryReservesPre R) -
    ((1 / 2) * Real.log reservesPre +
      (1 - (1 / 2 : ℝ)) * Real.log reservesPre +
      boundaryReserveQuantityInnovationZero R) = 0
  unfold boundaryReserveQuantityInnovationZero
  ring

 theorem boundary_zero_pricing_rows (G R : ℝ)
    (hR : R ∈ boundaryInterval) :
    localReducedRemainingResidual (boundaryPrimitives G R) (boundaryZeroData G R) 8 = 0 ∧
      localReducedRemainingResidual (boundaryPrimitives G R) (boundaryZeroData G R) 9 = 0 := by
  have hrr0 := (boundary_rate_domain hR).2
  rcases matching_specialization (boundaryReserveRate R) with
    ⟨_hw, _hm, _hp, hdef, hsur⟩
  have hmean :
      (localPrefixBankDeficitSlope (boundaryPrimitives G R) (boundaryZeroData G R) +
        localPrefixBankSurplusSlope (boundaryPrimitives G R) (boundaryZeroData G R)) / 2 =
        meanSlope := by
    rw [show localPrefixBankDeficitSlope (boundaryPrimitives G R) (boundaryZeroData G R) =
          (1 + weight) / 100 by
          simpa [localPrefixBankDeficitSlope, boundaryZeroData, boundaryZeroSeed,
            boundaryFirmDateData, boundaryFirmDateSeed, boundaryFirmControls,
            boundaryPrimitives, boundaryControls] using hdef,
      show localPrefixBankSurplusSlope (boundaryPrimitives G R) (boundaryZeroData G R) =
          weight / 200 by
          simpa [localPrefixBankSurplusSlope, boundaryZeroData, boundaryZeroSeed,
            boundaryFirmDateData, boundaryFirmDateSeed, boundaryFirmControls,
            boundaryPrimitives, boundaryControls] using hsur]
    unfold meanSlope
    ring
  have hgap :
      localPrefixBankDeficitSlope (boundaryPrimitives G R) (boundaryZeroData G R) -
        localPrefixBankSurplusSlope (boundaryPrimitives G R) (boundaryZeroData G R) =
        slopeGap := by
    have hd : localPrefixBankDeficitSlope (boundaryPrimitives G R) (boundaryZeroData G R) =
          (1 + weight) / 100 := by
      simpa [localPrefixBankDeficitSlope, boundaryZeroData, boundaryZeroSeed,
        boundaryFirmDateData, boundaryFirmDateSeed, boundaryFirmControls,
        boundaryPrimitives, boundaryControls] using hdef
    have hs : localPrefixBankSurplusSlope (boundaryPrimitives G R) (boundaryZeroData G R) =
          weight / 200 := by
      simpa [localPrefixBankSurplusSlope, boundaryZeroData, boundaryZeroSeed,
        boundaryFirmDateData, boundaryFirmDateSeed, boundaryFirmControls,
        boundaryPrimitives, boundaryControls] using hsur
    rw [hd, hs]
    unfold slopeGap
    ring
  have hmoment := localPrefixMeanAbsolutePaymentShock_eq_of_binarySymmetric
    (boundaryPrimitives G R) 0 1 (1 / 5) (boundary_binary_payment_law G R)
  constructor
  · change R - boundaryReserveRate R -
      (localPrefixBankDeficitSlope (boundaryPrimitives G R) (boundaryZeroData G R) +
        localPrefixBankSurplusSlope (boundaryPrimitives G R) (boundaryZeroData G R)) / 2 = 0
    rw [hmean]
    unfold boundaryReserveRate
    ring
  · change boundaryReserveRate R + (1 - (1 / 10 : ℝ)) *
        ((localPrefixBankDeficitSlope (boundaryPrimitives G R) (boundaryZeroData G R) +
          localPrefixBankSurplusSlope (boundaryPrimitives G R) (boundaryZeroData G R)) / 2) -
      (boundaryDepositRate R / boundaryReserveRate R - (1 / 10 : ℝ)) *
        localPrefixMeanAbsolutePaymentShock (boundaryPrimitives G R) *
        (localPrefixBankDeficitSlope (boundaryPrimitives G R) (boundaryZeroData G R) -
          localPrefixBankSurplusSlope (boundaryPrimitives G R) (boundaryZeroData G R)) / 2 -
      boundaryDepositRate R = 0
    rw [hmean, hgap, hmoment]
    have hb0 : 0 < boundaryPaymentTerm := by
      unfold boundaryPaymentTerm
      exact div_pos slope_bounds.2.2.1 (by norm_num)
    have hsum0 : 0 < boundaryReserveRate R + boundaryPaymentTerm :=
      add_pos hrr0 hb0
    rw [boundaryDepositRate_rewrite R (ne_of_gt hrr0) (ne_of_gt hsum0)]
    field_simp [ne_of_gt hrr0, ne_of_gt hsum0]
    unfold boundaryPaymentTerm
    ring

 theorem boundary_zero_reserveDepositRatio (G R : ℝ) :
    localPrefixReserveDepositRatio (boundaryPrimitives G R) (boundaryZeroData G R) =
      boundaryReserveDepositRatio R := by
  rw [localPrefixReserveDepositRatio,
    localPrefixMeanAbsolutePaymentShock_eq_of_binarySymmetric
      (boundaryPrimitives G R) 0 1 (1 / 5) (boundary_binary_payment_law G R)]
  simp [boundaryZeroData, boundaryZeroSeed, boundaryFirmDateData,
    boundaryFirmDateSeed, boundaryFirmControls, boundaryControls,
    boundaryReserveDepositRatio]
  ring

 theorem boundary_zero_bankBalance (G R : ℝ)
    (hR : R ∈ boundaryInterval) :
    localReducedRemainingResidual (boundaryPrimitives G R) (boundaryZeroData G R) 10 = 0 := by
  rcases boundaryReserveDepositRatio_bounds hR with ⟨hh0, hh1⟩
  have hR0 := (boundary_rate_domain hR).1
  have hmass : ∀ i, (boundaryPrimitives G R).mass i = 1 / 2 := by
    intro i
    rfl
  have hfaces :
      (∑ i, (boundaryPrimitives G R).mass i * firmFace i) =
        ProposedStationaryBank.loanRate * aggregateCredit := by
    simpa [boundaryPrimitives] using aggregate_firmFace_eq G
  have hloans :
      localPrefixReducedBankLoans (boundaryPrimitives G R) (boundaryZeroData G R) =
        boundaryBankLoans R := by
    unfold localPrefixReducedBankLoans boundaryBankLoans
    change (∑ i, (boundaryPrimitives G R).mass i * firmFace i / R) =
      aggregateCredit * ProposedStationaryBank.loanRate / R
    rw [sum_firmType_eq_H_add_L] at hfaces ⊢
    rw [← add_div, hfaces]
    ring
  have hequity :
      localPrefixReducedBankEquity (boundaryZeroData G R) = boundaryBankEquity R := by
    simp [localPrefixReducedBankEquity, boundaryZeroData, boundaryZeroSeed,
      boundaryFirmDateData, boundaryFirmDateSeed, boundaryFirmControls,
      boundaryControls]
  have hratio := boundary_zero_reserveDepositRatio G R
  change localPrefixReducedBankLoans (boundaryPrimitives G R) (boundaryZeroData G R) -
    (localPrefixReducedBankEquity (boundaryZeroData G R) +
      (1 / localPrefixReserveDepositRatio (boundaryPrimitives G R) (boundaryZeroData G R) - 1) *
        boundaryReservesPre R) = 0
  rw [hloans, hequity, hratio]
  unfold boundaryReservesPre boundaryBankDeposits
  field_simp [ne_of_gt hh0, ne_of_gt (sub_pos.mpr hh1)]
  ring

/-! ## Fecha uno: el real bloque es estacionario; solo cambian los lags y shocks -/

 theorem boundary_one_policy_rows (G R : ℝ) :
    localReducedRemainingResidual (boundaryPrimitives G R) (boundaryOneData G R) 6 = 0 ∧
      localReducedRemainingResidual (boundaryPrimitives G R) (boundaryOneData G R) 7 = 0 := by
  have hY :
      localPrefixAggregateOutput (boundaryPrimitives G R)
        ({ dateData with
          lagReserveRate := boundaryReserveRate R
          lagReservesPre := boundaryReservesPre R
          reserveRateInnovation := boundaryReserveRateInnovationOne R
          reserveQuantityInnovation := boundaryReserveQuantityInnovationOne R } :
          LocalPrefixDateData) = aggregateOutput := by
    change localPrefixAggregateOutput (boundaryPrimitives G R) dateData =
      aggregateOutput
    exact localPrefixAggregateOutput_eq (boundaryPrimitives G R)
      (boundary_stationary_parameters G R).toStationaryRealParameters
  rw [boundary_oneData_fields]
  constructor
  · simp only [localReducedRemainingResidual]
    rw [hY]
    change Real.log ProposedStationaryBank.reserveRate -
      ((1 / 2) * Real.log (boundaryReserveRate R) +
        (1 - (1 / 2 : ℝ)) *
          (Real.log ProposedStationaryBank.reserveRate +
            (3 / 2) * Real.log 1 + (1 / 8) * Real.log (aggregateOutput / aggregateOutput)) +
        boundaryReserveRateInnovationOne R) = 0
    have hY := aggregates_pos.2.1
    simp only [div_self (ne_of_gt hY), Real.log_one, mul_zero, add_zero]
    unfold boundaryReserveRateInnovationOne
    ring
  · simp only [localReducedRemainingResidual]
    change Real.log reservesPre -
      ((1 / 2) * Real.log (boundaryReservesPre R) +
        (1 - (1 / 2 : ℝ)) * Real.log reservesPre +
        boundaryReserveQuantityInnovationOne R) = 0
    unfold boundaryReserveQuantityInnovationOne
    ring

/-- Las otras nueve filas comunes de fecha uno son literalmente las del padre:
los lags monetarios y las innovaciones no aparecen en ellas. -/
theorem boundary_one_nonpolicy_rows (G R : ℝ) :
    ∀ row : Fin 11, row ≠ 6 → row ≠ 7 →
      localReducedRemainingResidual (boundaryPrimitives G R) (boundaryOneData G R) row = 0 := by
  intro row h6 h7
  have hstationary :=
    (stationary_reduced_system (boundaryPrimitives G R)
      (boundary_stationary_parameters G R) 0 1
      (boundary_binary_payment_law G R)).1
  fin_cases row
  · simpa [boundary_oneData_fields] using hstationary (0 : Fin 11)
  · simpa [boundary_oneData_fields] using hstationary (1 : Fin 11)
  · simpa [boundary_oneData_fields] using hstationary (2 : Fin 11)
  · simpa [boundary_oneData_fields] using hstationary (3 : Fin 11)
  · simpa [boundary_oneData_fields] using hstationary (4 : Fin 11)
  · simpa [boundary_oneData_fields] using hstationary (5 : Fin 11)
  · exact (h6 rfl).elim
  · exact (h7 rfl).elim
  · simpa [boundary_oneData_fields] using hstationary (8 : Fin 11)
  · simpa [boundary_oneData_fields] using hstationary (9 : Fin 11)
  · simpa [boundary_oneData_fields] using hstationary (10 : Fin 11)

 theorem boundary_one_remaining_rows (G R : ℝ) :
    ∀ row : Fin 11,
      localReducedRemainingResidual (boundaryPrimitives G R) (boundaryOneData G R) row = 0 := by
  rcases boundary_one_policy_rows G R with ⟨h6, h7⟩
  intro row
  by_cases hr6 : row = 6
  · simpa [hr6] using h6
  by_cases hr7 : row = 7
  · simpa [hr7] using h7
  exact boundary_one_nonpolicy_rows G R row hr6 hr7

 theorem boundary_one_firm_rows (G R : ℝ) (i : FirmType) :
    localReducedFirmBudgetResidual (boundaryPrimitives G R) (boundaryOneData G R) i = 0 ∧
      localReducedFirmCapitalEulerResidual .binding (boundaryPrimitives G R)
        (boundaryOneData G R) i = 0 := by
  have h := (stationary_reduced_system (boundaryPrimitives G R)
    (boundary_stationary_parameters G R) 0 1
    (boundary_binary_payment_law G R)).2 i
  rw [boundary_oneData_fields]
  exact ⟨by simpa using h.1, by simpa using h.2.1⟩

 theorem boundary_commonPledge_one (G R : ℝ) :
    (boundaryCoordinates R).stateTwo.commonPledgeValue -
      (1 - (boundaryPrimitives G R).depreciation) *
        (boundaryTail (boundaryCoordinates R).stateTwo).inflation *
        (boundaryTail (boundaryCoordinates R).stateTwo).capitalPrice = 0 := by
  have h := commonPledge_stationary_identity (boundaryPrimitives G R)
    (boundary_stationary_parameters G R)
  simpa [boundaryCoordinates, boundaryStateTwo, boundaryTail] using sub_eq_zero.mpr h

/-! ## La unica pieza real de fecha cero que aun se aisla -/

/-- Esta identidad es la FOC laboral de fecha cero. Su demostracion matematica
usa la homogeneidad L0=Lbar*s^(4/5)*(wbar/w0)^2 junto con
wbar=CWbar*Lbar y la definicion cubica de boundaryWage. -/
structure BoundaryWorkerLaborPackage (G R : ℝ) : Prop where
  row_zero :
    localReducedRemainingResidual (boundaryPrimitives G R) (boundaryZeroData G R) 3 = 0

/-! ## Cierre de las 33 ecuaciones, condicionado solo a raiz + fila laboral -/

 theorem boundary_zero_resources_eq_neg (G R : ℝ) :
    localReducedRemainingResidual (boundaryPrimitives G R) (boundaryZeroData G R) 2 =
      - boundaryResourceResidual R := by
  have hrot :
      localPrefixRotembergCost (boundaryPrimitives G R) (boundaryZeroData G R) = 0 := by
    simp [localPrefixRotembergCost, boundaryZeroData, boundaryZeroSeed,
      boundaryFirmDateData, boundaryFirmDateSeed, boundaryFirmControls,
      boundaryControls]
  have hliteral :
      boundaryLiteralResourceResidual G R =
        localPrefixAggregateOutput (boundaryPrimitives G R) (boundaryZeroData G R) -
        (boundaryZeroData G R).controls.workerConsumption -
        (∑ i, (boundaryPrimitives G R).mass i *
          localPrefixFirmConsumption (boundaryZeroData G R).controls i) -
        localPrefixCapitalCost (boundaryPrimitives G R) (boundaryZeroData G R) := by
    rfl
  change
    (boundaryZeroData G R).controls.workerConsumption +
      (∑ i, (boundaryPrimitives G R).mass i *
        localPrefixFirmConsumption (boundaryZeroData G R).controls i) +
      localPrefixCapitalCost (boundaryPrimitives G R) (boundaryZeroData G R) +
      localPrefixRotembergCost (boundaryPrimitives G R) (boundaryZeroData G R) -
      localPrefixAggregateOutput (boundaryPrimitives G R) (boundaryZeroData G R) =
        - boundaryResourceResidual R
  rw [hrot, ← boundary_literal_eq_closed G R, hliteral]
  ring

 theorem boundary_zero_resources (G R : ℝ)
    (hroot : boundaryResourceResidual R = 0) :
    localReducedRemainingResidual (boundaryPrimitives G R) (boundaryZeroData G R) 2 = 0 := by
  rw [boundary_zero_resources_eq_neg G R, hroot]
  ring

 theorem boundary_zero_firm_rows (G R : ℝ) (hR : 0 < R)
    (branch : LocalPrefixBranch) (i : FirmType) :
    localReducedFirmBudgetResidual (boundaryPrimitives G R) (boundaryZeroData G R) i = 0 ∧
      localReducedFirmCapitalEulerResidual branch (boundaryPrimitives G R)
        (boundaryZeroData G R) i = 0 ∧
      localReducedFirmRegimeResidual branch (boundaryPrimitives G R)
        (boundaryZeroData G R) i = 0 := by
  have h := boundary_source_firm_rows G R hR (boundaryZeroSeed G R) branch i
  simpa [boundaryPrimitives, boundaryZeroData] using h

 theorem boundary_full_prefix_equations
    (G : ℝ) (HA : BoundaryAnalyticPackage) (HS : BoundaryEndpointSigns)
    (HL : BoundaryWorkerLaborPackage G (boundaryRoot HA HS))
    (branch : LocalPrefixBranch) :
    LocalReducedPrefixEquationsHold branch
      (boundaryPrimitives G (boundaryRoot HA HS))
      (boundaryInitialState G (boundaryRoot HA HS))
      (boundaryCoordinates (boundaryRoot HA HS)) .dateOne .recurrent boundaryTail := by
  let R := boundaryRoot HA HS
  have hspec := boundaryRoot_spec HA HS
  have hmem : R ∈ boundaryInterval := ⟨hspec.1, hspec.2.1⟩
  have hR0 := (boundary_rate_domain hmem).1
  have hroot : boundaryResourceResidual R = 0 := hspec.2.2
  intro equation
  change localReducedPrefixResidual branch (boundaryPrimitives G R)
    (boundaryInitialState G R) (boundaryCoordinates R) .dateOne .recurrent
      boundaryTail equation = 0
  simp only [localReducedPrefixResidual, boundary_dateZeroData_eq]
  change (match equation with
    | .firmBudgetZeroH => localReducedFirmBudgetResidual (boundaryPrimitives G R) (boundaryZeroData G R) .H
    | .firmBudgetZeroL => localReducedFirmBudgetResidual (boundaryPrimitives G R) (boundaryZeroData G R) .L
    | .firmCapitalEulerZeroH => localReducedFirmCapitalEulerResidual branch (boundaryPrimitives G R) (boundaryZeroData G R) .H
    | .firmCapitalEulerZeroL => localReducedFirmCapitalEulerResidual branch (boundaryPrimitives G R) (boundaryZeroData G R) .L
    | .firmRegimeZeroH => localReducedFirmRegimeResidual branch (boundaryPrimitives G R) (boundaryZeroData G R) .H
    | .firmRegimeZeroL => localReducedFirmRegimeResidual branch (boundaryPrimitives G R) (boundaryZeroData G R) .L
    | .bankEquityZero => localReducedRemainingResidual (boundaryPrimitives G R) (boundaryZeroData G R) 0
    | .capitalSupplyZero => localReducedRemainingResidual (boundaryPrimitives G R) (boundaryZeroData G R) 1
    | .resourcesZero => localReducedRemainingResidual (boundaryPrimitives G R) (boundaryZeroData G R) 2
    | .workerLaborZero => localReducedRemainingResidual (boundaryPrimitives G R) (boundaryZeroData G R) 3
    | .householdEulerZero => localReducedRemainingResidual (boundaryPrimitives G R) (boundaryZeroData G R) 4
    | .nkpcZero => localReducedRemainingResidual (boundaryPrimitives G R) (boundaryZeroData G R) 5
    | .reserveRateRuleZero => localReducedRemainingResidual (boundaryPrimitives G R) (boundaryZeroData G R) 6
    | .reserveQuantityRuleZero => localReducedRemainingResidual (boundaryPrimitives G R) (boundaryZeroData G R) 7
    | .loanPricingZero => localReducedRemainingResidual (boundaryPrimitives G R) (boundaryZeroData G R) 8
    | .depositPricingZero => localReducedRemainingResidual (boundaryPrimitives G R) (boundaryZeroData G R) 9
    | .bankBalanceZero => localReducedRemainingResidual (boundaryPrimitives G R) (boundaryZeroData G R) 10
    | .firmBudgetOneH => localReducedFirmBudgetResidual (boundaryPrimitives G R) (boundaryOneData G R) .H
    | .firmBudgetOneL => localReducedFirmBudgetResidual (boundaryPrimitives G R) (boundaryOneData G R) .L
    | .firmCapitalEulerOneH => localReducedFirmCapitalEulerResidual .binding (boundaryPrimitives G R) (boundaryOneData G R) .H
    | .firmCapitalEulerOneL => localReducedFirmCapitalEulerResidual .binding (boundaryPrimitives G R) (boundaryOneData G R) .L
    | .commonPledgeOne => (boundaryCoordinates R).stateTwo.commonPledgeValue -
        (1 - (boundaryPrimitives G R).depreciation) *
          (boundaryTail (boundaryCoordinates R).stateTwo).inflation *
          (boundaryTail (boundaryCoordinates R).stateTwo).capitalPrice
    | .bankEquityOne => localReducedRemainingResidual (boundaryPrimitives G R) (boundaryOneData G R) 0
    | .capitalSupplyOne => localReducedRemainingResidual (boundaryPrimitives G R) (boundaryOneData G R) 1
    | .resourcesOne => localReducedRemainingResidual (boundaryPrimitives G R) (boundaryOneData G R) 2
    | .workerLaborOne => localReducedRemainingResidual (boundaryPrimitives G R) (boundaryOneData G R) 3
    | .householdEulerOne => localReducedRemainingResidual (boundaryPrimitives G R) (boundaryOneData G R) 4
    | .nkpcOne => localReducedRemainingResidual (boundaryPrimitives G R) (boundaryOneData G R) 5
    | .reserveRateRuleOne => localReducedRemainingResidual (boundaryPrimitives G R) (boundaryOneData G R) 6
    | .reserveQuantityRuleOne => localReducedRemainingResidual (boundaryPrimitives G R) (boundaryOneData G R) 7
    | .loanPricingOne => localReducedRemainingResidual (boundaryPrimitives G R) (boundaryOneData G R) 8
    | .depositPricingOne => localReducedRemainingResidual (boundaryPrimitives G R) (boundaryOneData G R) 9
    | .bankBalanceOne => localReducedRemainingResidual (boundaryPrimitives G R) (boundaryOneData G R) 10) = 0
  cases equation with
  | firmBudgetZeroH => exact (boundary_zero_firm_rows G R hR0 branch .H).1
  | firmBudgetZeroL => exact (boundary_zero_firm_rows G R hR0 branch .L).1
  | firmCapitalEulerZeroH => exact (boundary_zero_firm_rows G R hR0 branch .H).2.1
  | firmCapitalEulerZeroL => exact (boundary_zero_firm_rows G R hR0 branch .L).2.1
  | firmRegimeZeroH => exact (boundary_zero_firm_rows G R hR0 branch .H).2.2
  | firmRegimeZeroL => exact (boundary_zero_firm_rows G R hR0 branch .L).2.2
  | bankEquityZero => exact boundary_zero_bankRenewal G R hR0
  | capitalSupplyZero => exact boundary_zero_capitalSupply G R hmem
  | resourcesZero => exact boundary_zero_resources G R hroot
  | workerLaborZero => exact HL.row_zero
  | householdEulerZero => exact boundary_zero_householdEuler G R hmem
  | nkpcZero => exact boundary_zero_nkpc G R
  | reserveRateRuleZero => exact boundary_zero_reserveRateRule G R
  | reserveQuantityRuleZero => exact boundary_zero_reserveQuantityRule G R
  | loanPricingZero => exact (boundary_zero_pricing_rows G R hmem).1
  | depositPricingZero => exact (boundary_zero_pricing_rows G R hmem).2
  | bankBalanceZero => exact boundary_zero_bankBalance G R hmem
  | firmBudgetOneH => exact (boundary_one_firm_rows G R .H).1
  | firmBudgetOneL => exact (boundary_one_firm_rows G R .L).1
  | firmCapitalEulerOneH => exact (boundary_one_firm_rows G R .H).2
  | firmCapitalEulerOneL => exact (boundary_one_firm_rows G R .L).2
  | commonPledgeOne => exact boundary_commonPledge_one G R
  | bankEquityOne => exact boundary_one_remaining_rows G R 0
  | capitalSupplyOne => exact boundary_one_remaining_rows G R 1
  | resourcesOne => exact boundary_one_remaining_rows G R 2
  | workerLaborOne => exact boundary_one_remaining_rows G R 3
  | householdEulerOne => exact boundary_one_remaining_rows G R 4
  | nkpcOne => exact boundary_one_remaining_rows G R 5
  | reserveRateRuleOne => exact boundary_one_remaining_rows G R 6
  | reserveQuantityRuleOne => exact boundary_one_remaining_rows G R 7
  | loanPricingOne => exact boundary_one_remaining_rows G R 8
  | depositPricingOne => exact boundary_one_remaining_rows G R 9
  | bankBalanceOne => exact boundary_one_remaining_rows G R 10

/-!
Estado matematico tras este modulo:

* La raiz R* no se aproxima por un decimal: se escoge del ExactRootOn.
* El estado heredado de fecha cero, el estado de fecha uno, el estado de fecha
  dos y los 20 controles son portadores concretos.
* Las innovaciones monetarias e0,e1 se reconstruyen como los residuos exactos
  de las reglas; son equivalentes a las formulas logaritmicas simplificadas de
  finite_bridge.py cuando las razones son positivas.
* Las filas 0,1,4,5,6,7,8,9,10 de fecha cero se descargan por algebra y dominio.
* La fila 2 es exactamente la ecuacion de raiz.
* Las seis filas empresariales de fecha cero se reutilizan del enlace KKT.
* Las 16 filas de fecha uno son el padre estacionario con lags/innovaciones
  corregidos.
* Solo queda aislada la FOC laboral de fecha cero, cuya prueba exige manipular
  la potencia real de la escala de capital. Esa es la siguiente meta Lean.

No se afirma todavia que este prefijo sea realizado por una Allocation, ni
factibilidad/optimalidad global, ni radio IFT, ni existencia de las ramas
estrictas S y B a ambos lados. Esas capas permanecen separadas.
-/

end ProposedBoundaryFullPrefix
end Ventura26LiquidityAllocation
