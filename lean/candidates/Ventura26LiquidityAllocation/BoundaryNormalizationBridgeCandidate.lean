import Ventura26LiquidityAllocation.BoundaryEndpointBoxesCandidate

/-!
# Source normalization, four elementary identities from existing parent data

UNCOMPILED candidate; pinned branch work/chat-continuity, commit
16e24fe828a5a0002ef13bb82bae9e295f190f86.

Mathematical conclusion: after multiplying all quantities by stationary
wage^5, no 12th root is needed. These four proofs use original parent
scaling lemmas and the previously established capital-cost identity.
The OUTPUT identity remains a distinct root-of-degree-15 obligation;
it is NOT assumed to hold as a theorem by this file.
-/

namespace Ventura26LiquidityAllocation
namespace ProposedBoundaryNormalizationBridge

open ProposedStationaryBank
open ProposedStationaryRealScale
open ProposedStationaryProductionBridge
open ProposedBoundaryBridge
open ProposedBoundaryResourceRoot
open ProposedBoundaryEndpointBoxes
open ProposedBoundaryWorkerLabor
open ProposedBoundaryAnalyticPackage
open ProposedBoundaryFullPrefix

/-- Express entrepreneur consumption in terms of unit-wage capital scale. -/
theorem firm_coefficient_scaled (i : FirmType) :
    wage ^ (5 : ℕ) * firmConsumption i = firmCoefficient i := by
  unfold firmCoefficient firmConsumption profit output loan firmFace capital
  field_simp [ne_of_gt wage_pos,
    ne_of_gt loanRate_pos] <;> ring

/-- Worker consumption: direct consequence of the stationary scale lemma. -/
theorem normalized_worker_eq (R : ℝ) :
    wage ^ (5 : ℕ) * boundaryWorkerConsumption R =
      normalizedWorkerConsumption R := by
  unfold boundaryWorkerConsumption normalizedWorkerConsumption
  rw [workerConsumption_scale]
  field_simp [ne_of_gt wage_pos, ne_of_gt (pow_pos wage_pos (5 : ℕ))] <;> ring

/-- The entrepreneur coefficients scale with wage^-5, while their
    initial-date consumption response is a rational function of R. -/
theorem normalized_firm_eq (R : ℝ) (hR : 0 < R) (i : FirmType) :
    wage ^ (5 : ℕ) * boundaryConsumption R i =
      normalizedFirmConsumption R i := by
  cases i with
  | H =>
      unfold normalizedFirmConsumption boundaryConsumption
      rw [boundaryEffectivePrice_eq]
      rw [← firm_coefficient_scaled .H]
      field_simp [ne_of_gt hR,
        ne_of_gt (parentEffectivePrice_pos .H)] <;> ring
  | L =>
      unfold normalizedFirmConsumption boundaryConsumption
      rw [← firm_coefficient_scaled .L]
      field_simp [ne_of_gt hR] <;> ring

/-- Investment adjustment costs are linear in aggregate capital, and the
    stationary aggregate capital equals the unit-wage coefficient / wage^5. -/
theorem normalized_capitalCost_eq (R : ℝ)
    (hscale : 0 < boundaryCapitalScale R) :
    wage ^ (5 : ℕ) * boundaryCapitalCost R =
      normalizedCapitalCost R := by
  rw [boundaryCapitalCost_scale_formula hscale, aggregateCapital_scale]
  unfold normalizedCapitalCost
  field_simp [ne_of_gt wage_pos, ne_of_gt (pow_pos wage_pos (5 : ℕ)),
    ne_of_gt hscale] <;> ring

/-- The original SOURCE production scaling proves the exact fifteenth
root expression, rather than postulating it at the two bracket endpoints.
This depends on output_ratio_fifteenth_power in the analytic module. -/
theorem normalized_output_eq_from_source (R : ℝ)
    (hR : R ∈ boundaryInterval) :
    wage ^ (5 : ℕ) * boundaryAggregateOutput R =
      normalizedOutput R := by
  have hY : 0 < boundaryAggregateOutput R := by
    rw [aggregateOutput_scaling hR]
    exact mul_pos
      (mul_pos aggregates_pos.2.1
        (Real.rpow_pos_of_pos
          (boundary_scale_and_investment_domain hR).1 _))
      (div_pos wage_pos (boundaryWage_pos hR))
  have hratio0 :
      0 ≤ boundaryAggregateOutput R / aggregateOutput :=
    (div_pos hY aggregates_pos.2.1).le
  have hpow := output_ratio_fifteenth_power hR
  have hroot :
      boundaryAggregateOutput R / aggregateOutput =
        (boundaryCapitalScale R ^ (8 : ℕ) *
          ((99 / 100 : ℝ) * boundaryDepositRate R) ^ (5 : ℕ)) ^
            (1 / 15 : ℝ) := by
    calc
      boundaryAggregateOutput R / aggregateOutput =
          ((boundaryAggregateOutput R / aggregateOutput) ^
              (15 : ℕ)) ^ (1 / 15 : ℝ) := by
            simpa only [one_div] using
              (Real.pow_rpow_inv_natCast hratio0
                (by norm_num : (15 : ℕ) ≠ 0)).symm
      _ = _ := by rw [hpow]
  have hscale :
      outputScale = wage ^ (5 : ℕ) * aggregateOutput := by
    rw [aggregateOutput_scale]
    field_simp [ne_of_gt wage_pos, ne_of_gt (pow_pos wage_pos (5 : ℕ))] <;> ring
  change wage ^ (5 : ℕ) * boundaryAggregateOutput R =
    outputScale * (boundaryCapitalScale R ^ (8 : ℕ) *
      ((99 / 100 : ℝ) * boundaryDepositRate R) ^ (5 : ℕ)) ^
        (1 / 15 : ℝ)
  rw [← hroot, hscale]
  field_simp [ne_of_gt aggregates_pos.2.1] <;> ring

/-- All five source-normalization fields follow once the one remaining
    output-root identity has been proved. The parent scales are NOT taken
    as hypotheses; the four non-output fields above construct their proofs. -/
theorem scaleIdentities_of_output_root (R : ℝ) (hR : R ∈ boundaryInterval)
    (houtput : wage ^ (5 : ℕ) * boundaryAggregateOutput R =
      normalizedOutput R) :
    BoundaryScaleIdentities R := by
  refine ⟨houtput, normalized_worker_eq R, ?_, ?_, ?_⟩
  · exact normalized_firm_eq R (boundary_rate_domain hR).1 .H
  · exact normalized_firm_eq R (boundary_rate_domain hR).1 .L
  · exact normalized_capitalCost_eq R
      (boundary_scale_and_investment_domain hR).1

/-- The remaining root identity is deliberately isolated in this predicate;
    its exact polynomial content is z^15=s^8*(betaW RD)^5 with z>0.
    A proof may use `Real.rpow_mul` or the root-uniqueness argument. -/
def OutputRootIdentityAt (R : ℝ) : Prop :=
  wage ^ (5 : ℕ) * boundaryAggregateOutput R = normalizedOutput R

/-- The final sign interface after eliminating four normalization obligations:
    only two output-root identities and ten rational boxes remain exposed. -/
theorem endpointSigns_of_boxes_and_output_roots
    (houtputLo : OutputRootIdentityAt boundaryLo)
    (houtputHi : OutputRootIdentityAt boundaryHi)
    (hboxes : BoundaryComponentBoxes) : BoundaryEndpointSigns := by
  apply endpointSigns_of_verified_components
    (scaleIdentities_of_output_root boundaryLo
      (by
        exact ⟨le_refl _, le_of_lt boundaryLo_lt_boundaryHi⟩) houtputLo)
    (scaleIdentities_of_output_root boundaryHi
      (by
        exact ⟨le_of_lt boundaryLo_lt_boundaryHi, le_refl _⟩) houtputHi)
    hboxes

/-- Both exact endpoint production roots are now consequences of
source production and positivity, not independent hypotheses. Ten
rational interval boxes remain an explicit proof obligation. -/
theorem endpointSigns_of_boxes
    (hboxes : BoundaryComponentBoxes) : BoundaryEndpointSigns := by
  exact endpointSigns_of_verified_components
    (scaleIdentities_of_output_root boundaryLo
      ⟨le_refl _, le_of_lt boundaryLo_lt_boundaryHi⟩
      (normalized_output_eq_from_source boundaryLo
        ⟨le_refl _, le_of_lt boundaryLo_lt_boundaryHi⟩))
    (scaleIdentities_of_output_root boundaryHi
      ⟨le_of_lt boundaryLo_lt_boundaryHi, le_refl _⟩
      (normalized_output_eq_from_source boundaryHi
        ⟨le_of_lt boundaryLo_lt_boundaryHi, le_refl _⟩))
    hboxes

/-- The boundary reduced prefix is closed conditionally on only the
ten endpoint boxes: neither the worker-labor FOC nor source monotonicity
nor the fifteenth output root is supplied as an extra assumption. The
full competitive equilibrium and terminal conditions remain separate. -/
theorem boundary_reduced_prefix_from_endpoint_boxes
    (G : ℝ) (hboxes : BoundaryComponentBoxes)
    (branch : LocalPrefixBranch) :
    LocalReducedPrefixEquationsHold branch
      (boundaryPrimitives G
        (boundaryRoot boundary_analyticPackage (endpointSigns_of_boxes hboxes)))
      (boundaryInitialState G
        (boundaryRoot boundary_analyticPackage (endpointSigns_of_boxes hboxes)))
      (boundaryCoordinates
        (boundaryRoot boundary_analyticPackage (endpointSigns_of_boxes hboxes)))
      .dateOne .recurrent boundaryTail := by
  exact boundary_full_prefix_equations_from_root G
    boundary_analyticPackage (endpointSigns_of_boxes hboxes) branch

/-- Conditional uniqueness for the SOURCE *scalar* frontier rate plus
the literal 33-row reduced prefix in every named reduced-system branch.
Uniqueness is of R on the resource bracket, not uniqueness of the
allocation or of an infinite-horizon competitive equilibrium.
The ten rational endpoint boxes are still explicit hypotheses. -/
theorem boundary_unique_reduced_prefix_rate_of_boxes
    (G : ℝ) (hboxes : BoundaryComponentBoxes) :
    ∃! R : ℝ,
      boundaryLo ≤ R ∧ R ≤ boundaryHi ∧
      boundaryResourceResidual R = 0 ∧
      ∀ branch : LocalPrefixBranch,
        LocalReducedPrefixEquationsHold branch
          (boundaryPrimitives G R)
          (boundaryInitialState G R)
          (boundaryCoordinates R) .dateOne .recurrent boundaryTail := by
  let R := boundaryRoot boundary_analyticPackage (endpointSigns_of_boxes hboxes)
  have hspec := boundaryRoot_spec
    boundary_analyticPackage (endpointSigns_of_boxes hboxes)
  have huniq :=
    (Classical.choose_spec
      (boundary_exactRootOn boundary_analyticPackage
        (endpointSigns_of_boxes hboxes))).2
  refine ⟨R, ⟨hspec.1, hspec.2.1, hspec.2.2, ?_⟩, ?_⟩
  · intro branch
    exact boundary_reduced_prefix_from_endpoint_boxes G hboxes branch
  · intro y hy
    exact huniq y ⟨hy.1, hy.2.1, hy.2.2.1⟩


/-- A tight, fully rational enclosure of the literal OTC matching weight.
Every inequality is reduced to exact rational square comparisons with
sqrt(3/2), never to a floating-point evaluation. -/
theorem boundary_weight_rational_micro_box :
    (44948974278 / 100000000000 : ℝ) <
      ProposedStationaryBank.weight ∧
    ProposedStationaryBank.weight <
      (44948974279 / 100000000000 : ℝ) := by
  have hs0 : 0 ≤ Real.sqrt (3 / 2 : ℝ) := Real.sqrt_nonneg _
  have hsq : Real.sqrt (3 / 2 : ℝ) ^ (2 : ℕ) = 3 / 2 :=
    Real.sq_sqrt (by norm_num)
  have hslo :
      (122474487139 / 100000000000 : ℝ) <
        Real.sqrt (3 / 2 : ℝ) := by
    have hsqlo :
        (122474487139 / 100000000000 : ℝ) ^ (2 : ℕ) <
          3 / 2 := by norm_num
    by_contra hn
    have hle :
        Real.sqrt (3 / 2 : ℝ) ≤
          (122474487139 / 100000000000 : ℝ) :=
      le_of_not_gt hn
    have hp : 0 ≤
        ((122474487139 / 100000000000 : ℝ) -
          Real.sqrt (3 / 2 : ℝ)) *
        ((122474487139 / 100000000000 : ℝ) +
          Real.sqrt (3 / 2 : ℝ)) :=
      mul_nonneg (sub_nonneg.mpr hle)
        (add_nonneg (by norm_num) hs0)
    nlinarith only [hsqlo, hsq, hp]
  have hshi :
      Real.sqrt (3 / 2 : ℝ) <
        (122474487140 / 100000000000 : ℝ) := by
    have hsqhi :
        (3 / 2 : ℝ) <
          (122474487140 / 100000000000 : ℝ) ^ (2 : ℕ) := by
      norm_num
    by_contra hn
    have hge :
        (122474487140 / 100000000000 : ℝ) ≤
          Real.sqrt (3 / 2 : ℝ) :=
      le_of_not_gt hn
    have hp : 0 ≤
        (Real.sqrt (3 / 2 : ℝ) -
          (122474487140 / 100000000000 : ℝ)) *
        (Real.sqrt (3 / 2 : ℝ) +
          (122474487140 / 100000000000 : ℝ)) :=
      mul_nonneg (sub_nonneg.mpr hge)
        (add_nonneg hs0 (by norm_num))
    nlinarith only [hsqhi, hsq, hp]
  have hd : 0 < 1 + Real.sqrt (3 / 2 : ℝ) := by linarith
  constructor
  · unfold ProposedStationaryBank.weight
    apply (lt_div_iff₀ hd).2
    nlinarith only [hshi]
  · unfold ProposedStationaryBank.weight
    apply (div_lt_iff₀ hd).2
    nlinarith only [hslo]

/-- The SOURCE OTC mean and differential slopes inherit rational
micro-intervals from the exact matching-weight enclosure. -/
theorem boundary_source_slope_rational_micro_boxes :
    ((8371173070 / 1000000000000 : ℝ) <
      ProposedStationaryBank.meanSlope ∧
      ProposedStationaryBank.meanSlope <
        (8371173072 / 1000000000000 : ℝ)) ∧
    ((12247448713 / 1000000000000 : ℝ) <
      ProposedStationaryBank.slopeGap ∧
      ProposedStationaryBank.slopeGap <
        (12247448715 / 1000000000000 : ℝ)) := by
  rcases boundary_weight_rational_micro_box with ⟨hlo, hhi⟩
  unfold ProposedStationaryBank.meanSlope ProposedStationaryBank.slopeGap
  constructor
  · constructor <;> linarith
  · constructor <;> linarith


/-- An enclosure of the stationary SOURCE reserve remuneration follows
from the exact bank quadratic, its strictly positive root, and previously
certified rational OTC slope boxes. No square root is approximated here. -/
theorem boundary_source_reserve_rate_micro_box :
    (100367704 / 100000000 : ℝ) <
      ProposedStationaryBank.reserveRate ∧
    ProposedStationaryBank.reserveRate <
      (100367709 / 100000000 : ℝ) := by
  rcases boundary_source_slope_rational_micro_boxes with
    ⟨⟨hmlo, hmhi⟩, ⟨hglo, hghi⟩⟩
  have hcoef :
      (100244447 / 100000000 : ℝ) <
        ProposedStationaryBank.rootCoefficient ∧
      ProposedStationaryBank.rootCoefficient <
        (100244449 / 100000000 : ℝ) := by
    unfold ProposedStationaryBank.rootCoefficient
      ProposedStationaryBank.depositRate
    constructor <;> linarith
  have hpoly := (ProposedStationaryBank.reserveRate_spec).2.2
  have hr1 : 1 < ProposedStationaryBank.reserveRate :=
    (ProposedStationaryBank.reserveRate_spec).1
  have hplo :
      (100367704 / 100000000 : ℝ) ^ (2 : ℕ) -
        ProposedStationaryBank.rootCoefficient *
          (100367704 / 100000000 : ℝ) -
        ProposedStationaryBank.depositRate *
          ProposedStationaryBank.slopeGap / 10 < 0 := by
    have hcert :
        (100367704 / 100000000 : ℝ) ^ (2 : ℕ) -
          (100244447 / 100000000 : ℝ) *
            (100367704 / 100000000 : ℝ) -
          (100 / 99 : ℝ) *
            (12247448713 / 1000000000000 : ℝ) / 10 < 0 := by
      norm_num
    unfold ProposedStationaryBank.depositRate
    nlinarith only [hcoef.1, hglo, hcert]
  have hphi :
      0 < (100367709 / 100000000 : ℝ) ^ (2 : ℕ) -
        ProposedStationaryBank.rootCoefficient *
          (100367709 / 100000000 : ℝ) -
        ProposedStationaryBank.depositRate *
          ProposedStationaryBank.slopeGap / 10 := by
    have hcert :
        0 < (100367709 / 100000000 : ℝ) ^ (2 : ℕ) -
          (100244449 / 100000000 : ℝ) *
            (100367709 / 100000000 : ℝ) -
          (100 / 99 : ℝ) *
            (12247448715 / 1000000000000 : ℝ) / 10 := by
      norm_num
    unfold ProposedStationaryBank.depositRate
    nlinarith only [hcoef.2, hghi, hcert]
  constructor
  · by_contra hn
    have hle :
        ProposedStationaryBank.reserveRate ≤
          (100367704 / 100000000 : ℝ) := le_of_not_gt hn
    have hfac : 0 ≤
        ((100367704 / 100000000 : ℝ) -
          ProposedStationaryBank.reserveRate) *
        ((100367704 / 100000000 : ℝ) +
          ProposedStationaryBank.reserveRate -
          ProposedStationaryBank.rootCoefficient) :=
      mul_nonneg (sub_nonneg.mpr hle)
        (by linarith [hcoef.2, hr1])
    nlinarith only [hfac, hplo, hpoly]
  · by_contra hn
    have hle :
        (100367709 / 100000000 : ℝ) ≤
          ProposedStationaryBank.reserveRate := le_of_not_gt hn
    have hfac : 0 ≤
        (ProposedStationaryBank.reserveRate -
          (100367709 / 100000000 : ℝ)) *
        (ProposedStationaryBank.reserveRate +
          (100367709 / 100000000 : ℝ) -
          ProposedStationaryBank.rootCoefficient) :=
      mul_nonneg (sub_nonneg.mpr hle)
        (by linarith [hcoef.2, hr1])
    nlinarith only [hfac, hphi, hpoly]

/-- The loan gross rate equals reserve remuneration plus the exact
mean OTC slope; hence both levels admit a rational source certificate. -/
theorem boundary_source_loan_rate_micro_box :
    (101204821 / 100000000 : ℝ) <
      ProposedStationaryBank.loanRate ∧
    ProposedStationaryBank.loanRate <
      (101204827 / 100000000 : ℝ) := by
  rcases boundary_source_reserve_rate_micro_box with ⟨hrlo, hrhi⟩
  rcases boundary_source_slope_rational_micro_boxes with
    ⟨⟨hmlo, hmhi⟩, _⟩
  unfold ProposedStationaryBank.loanRate
  constructor <;> linarith



/-- A two-billionth-width interval for the literal stationary reserve
remuneration follows from the SOURCE quadratic and the rational OTC
slope bounds. This sharpens, rather than assumes, the original root
certificate; no floating-point approximations enter the theorem. -/
theorem boundary_source_reserve_rate_sharp_box :
    (1003677063 / 1000000000 : ℝ) <
      ProposedStationaryBank.reserveRate ∧
    ProposedStationaryBank.reserveRate <
      (1003677065 / 1000000000 : ℝ) := by
  rcases boundary_source_slope_rational_micro_boxes with
    ⟨⟨hmlo, hmhi⟩, ⟨hglo, hghi⟩⟩
  have hcoef :
      (1002444479849 / 1000000000000 : ℝ) <
        ProposedStationaryBank.rootCoefficient ∧
      ProposedStationaryBank.rootCoefficient <
        (1002444479851 / 1000000000000 : ℝ) := by
    unfold ProposedStationaryBank.rootCoefficient
      ProposedStationaryBank.depositRate
    constructor <;> linarith
  have hpoly := (ProposedStationaryBank.reserveRate_spec).2.2
  have hr1 : 1 < ProposedStationaryBank.reserveRate :=
    (ProposedStationaryBank.reserveRate_spec).1
  have hplo :
      (1003677063 / 1000000000 : ℝ) ^ (2 : ℕ) -
        ProposedStationaryBank.rootCoefficient *
          (1003677063 / 1000000000 : ℝ) -
        ProposedStationaryBank.depositRate *
          ProposedStationaryBank.slopeGap / 10 < 0 := by
    have hcert :
        (1003677063 / 1000000000 : ℝ) ^ (2 : ℕ) -
          (1002444479849 / 1000000000000 : ℝ) *
            (1003677063 / 1000000000 : ℝ) -
          (100 / 99 : ℝ) *
            (12247448713 / 1000000000000 : ℝ) / 10 < 0 := by
      norm_num
    unfold ProposedStationaryBank.depositRate
    nlinarith only [hcoef.1, hglo, hcert]
  have hphi :
      0 < (1003677065 / 1000000000 : ℝ) ^ (2 : ℕ) -
        ProposedStationaryBank.rootCoefficient *
          (1003677065 / 1000000000 : ℝ) -
        ProposedStationaryBank.depositRate *
          ProposedStationaryBank.slopeGap / 10 := by
    have hcert :
        0 < (1003677065 / 1000000000 : ℝ) ^ (2 : ℕ) -
          (1002444479851 / 1000000000000 : ℝ) *
            (1003677065 / 1000000000 : ℝ) -
          (100 / 99 : ℝ) *
            (12247448715 / 1000000000000 : ℝ) / 10 := by
      norm_num
    unfold ProposedStationaryBank.depositRate
    nlinarith only [hcoef.2, hghi, hcert]
  constructor
  · by_contra hn
    have hle :
        ProposedStationaryBank.reserveRate ≤
          (1003677063 / 1000000000 : ℝ) := le_of_not_gt hn
    have hfac : 0 ≤
        ((1003677063 / 1000000000 : ℝ) -
          ProposedStationaryBank.reserveRate) *
        ((1003677063 / 1000000000 : ℝ) +
          ProposedStationaryBank.reserveRate -
          ProposedStationaryBank.rootCoefficient) :=
      mul_nonneg (sub_nonneg.mpr hle)
        (by linarith [hcoef.2, hr1])
    nlinarith only [hfac, hplo, hpoly]
  · by_contra hn
    have hle :
        (1003677065 / 1000000000 : ℝ) ≤
          ProposedStationaryBank.reserveRate := le_of_not_gt hn
    have hfac : 0 ≤
        (ProposedStationaryBank.reserveRate -
          (1003677065 / 1000000000 : ℝ)) *
        (ProposedStationaryBank.reserveRate +
          (1003677065 / 1000000000 : ℝ) -
          ProposedStationaryBank.rootCoefficient) :=
      mul_nonneg (sub_nonneg.mpr hle)
        (by linarith [hcoef.2, hr1])
    nlinarith only [hfac, hphi, hpoly]

/-- SOURCE loan gross rate: the reserve rate plus the exact OTC mean
slope. The bounds are derived, not substituted for the bank solution. -/
theorem boundary_source_loan_rate_sharp_box :
    (101204823607 / 100000000000 : ℝ) <
      ProposedStationaryBank.loanRate ∧
    ProposedStationaryBank.loanRate <
      (101204823808 / 100000000000 : ℝ) := by
  rcases boundary_source_reserve_rate_sharp_box with ⟨hrlo, hrhi⟩
  rcases boundary_source_slope_rational_micro_boxes with
    ⟨⟨hmlo, hmhi⟩, _⟩
  unfold ProposedStationaryBank.loanRate
  constructor <;> linarith


#print axioms boundary_source_reserve_rate_sharp_box
#print axioms boundary_source_loan_rate_sharp_box

/-- The two SOURCE firm user costs inherit strict rational envelopes from
the proved positive loan-rate box. This is a statement about stationary
primitive parameters and a candidate bank pricing solution; it does not
by itself certify a full competitive equilibrium. -/
theorem boundary_source_user_cost_micro_boxes :
    ((6316636 / 100000000 : ℝ) <
        ProposedStationaryRealScale.userCost .H ∧
      ProposedStationaryRealScale.userCost .H <
        (6316638 / 100000000 : ℝ)) ∧
    ((5594364 / 100000000 : ℝ) <
        ProposedStationaryRealScale.userCost .L ∧
      ProposedStationaryRealScale.userCost .L <
        (5594368 / 100000000 : ℝ)) := by
  rcases boundary_source_loan_rate_micro_box with ⟨hrlo, hrhi⟩
  have hpos : 0 < ProposedStationaryBank.loanRate :=
    ProposedStationaryRealScale.loanRate_pos
  have hscaledH :
      ProposedStationaryRealScale.userCost .H *
        ProposedStationaryBank.loanRate =
      (81 / 80 : ℝ) * ((511 / 2400 : ℝ) *
        ProposedStationaryBank.loanRate - 39 / 256) := by
    unfold ProposedStationaryRealScale.userCost
      ProposedStationaryRealScale.capitalPrice
      ProposedStationaryRealScale.pledgeability
    field_simp [ne_of_gt hpos] <;> ring
  have hscaledL :
      ProposedStationaryRealScale.userCost .L *
        ProposedStationaryBank.loanRate =
      (81 / 80 : ℝ) * ((137 / 300 : ℝ) *
        ProposedStationaryBank.loanRate - 13 / 32) := by
    unfold ProposedStationaryRealScale.userCost
      ProposedStationaryRealScale.capitalPrice
      ProposedStationaryRealScale.pledgeability
    field_simp [ne_of_gt hpos] <;> ring
  constructor
  · constructor
    · by_contra hn
      have hle :
          ProposedStationaryRealScale.userCost .H ≤
            (6316636 / 100000000 : ℝ) := le_of_not_gt hn
      have hmul := mul_le_mul_of_nonneg_right hle hpos.le
      rw [hscaledH] at hmul
      linarith only [hmul, hrlo]
    · by_contra hn
      have hge :
          (6316638 / 100000000 : ℝ) ≤
            ProposedStationaryRealScale.userCost .H := le_of_not_gt hn
      have hmul := mul_le_mul_of_nonneg_right hge hpos.le
      rw [hscaledH] at hmul
      linarith only [hmul, hrhi]
  · constructor
    · by_contra hn
      have hle :
          ProposedStationaryRealScale.userCost .L ≤
            (5594364 / 100000000 : ℝ) := le_of_not_gt hn
      have hmul := mul_le_mul_of_nonneg_right hle hpos.le
      rw [hscaledL] at hmul
      linarith only [hmul, hrlo]
    · by_contra hn
      have hge :
          (5594368 / 100000000 : ℝ) ≤
            ProposedStationaryRealScale.userCost .L := le_of_not_gt hn
      have hmul := mul_le_mul_of_nonneg_right hge hpos.le
      rw [hscaledL] at hmul
      linarith only [hmul, hrhi]

/-- Structural SOURCE collateral wedge: the stationary bank pricing
condition RL < 25/24 alone implies the lower-pledgeability high-productivity
firm has a strictly higher capital user cost. No micro-interval bounds or
root approximation enter this proof. This is not a GE welfare result. -/
theorem boundary_source_user_cost_wedge_of_bank_pricing :
    ProposedStationaryRealScale.userCost .L <
      ProposedStationaryRealScale.userCost .H := by
  rcases ProposedStationaryBank.bank_margins_and_pricing with
    ⟨_, _, _, _, _, _, hloanUpper⟩
  have hloan : 0 < ProposedStationaryBank.loanRate :=
    ProposedStationaryRealScale.loanRate_pos
  have hdifference :
      (ProposedStationaryRealScale.userCost .H -
        ProposedStationaryRealScale.userCost .L) *
        ProposedStationaryBank.loanRate =
      (81 / 320 : ℝ) *
        ((65 / 64 : ℝ) -
          (39 / 40 : ℝ) * ProposedStationaryBank.loanRate) := by
    unfold ProposedStationaryRealScale.userCost
      ProposedStationaryRealScale.capitalPrice
      ProposedStationaryRealScale.pledgeability
    field_simp [ne_of_gt hloan] <;> ring
  have hbracket :
      0 < (65 / 64 : ℝ) -
        (39 / 40 : ℝ) * ProposedStationaryBank.loanRate := by
    linarith only [hloanUpper]
  have hright : 0 <
      (81 / 320 : ℝ) *
        ((65 / 64 : ℝ) -
          (39 / 40 : ℝ) * ProposedStationaryBank.loanRate) :=
    mul_pos (by norm_num) hbracket
  by_contra hn
  have hle :
      ProposedStationaryRealScale.userCost .H ≤
        ProposedStationaryRealScale.userCost .L :=
    le_of_not_gt hn
  have hprod :
      (ProposedStationaryRealScale.userCost .H -
        ProposedStationaryRealScale.userCost .L) *
          ProposedStationaryBank.loanRate ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hle) hloan.le
  linarith only [hdifference, hright, hprod]

#print axioms boundary_source_user_cost_wedge_of_bank_pricing

/-- A strictly higher-technology firm has lower pledgeability and a
larger stationary user cost under the SOURCE illustrative parameters.
This is a wedge ranking, not a general-equilibrium welfare result. -/
theorem boundary_source_productivity_collateral_cost_wedge :
    ProposedStationaryRealScale.technology .L <
      ProposedStationaryRealScale.technology .H ∧
    ProposedStationaryRealScale.pledgeability .H <
      ProposedStationaryRealScale.pledgeability .L ∧
    ProposedStationaryRealScale.userCost .L <
      ProposedStationaryRealScale.userCost .H := by
  refine ⟨?_, ?_, boundary_source_user_cost_wedge_of_bank_pricing⟩
  · norm_num [ProposedStationaryRealScale.technology]
  · norm_num [ProposedStationaryRealScale.pledgeability]


/-- Structural capital misallocation ranking in the literal SOURCE
stationary construction. The high-technology H firm has a lower
stationary capital scale than L, because the collateral/user-cost wedge
dominates its 1% technology advantage. Unlike numerical certificates,
this uses only the original broad bank bounds and source identities.
It does not assert a complete GE allocation or a growth effect. -/
theorem boundary_source_stationary_capital_scale_order :
    ProposedStationaryRealScale.capitalScale .H <
      ProposedStationaryRealScale.capitalScale .L := by
  have hrpos : 0 < ProposedStationaryBank.loanRate :=
    ProposedStationaryRealScale.loanRate_pos
  have hrUpper := (ProposedStationaryBank.reserveRate_spec).2.1
  have hmUpper := (ProposedStationaryBank.slope_bounds).2.1
  have hrBound :
      ProposedStationaryBank.loanRate < (103 / 100 : ℝ) := by
    change ProposedStationaryBank.reserveRate +
      ProposedStationaryBank.meanSlope < (103 / 100 : ℝ)
    norm_num [ProposedStationaryBank.depositRate] at hrUpper
    linarith only [hrUpper, hmUpper]
  let alpha : ℝ := 10201 / 10000
  have hprofitRatio :
      ProposedStationaryRealScale.profitCoefficient .H =
        alpha * ProposedStationaryRealScale.profitCoefficient .L := by
    dsimp [alpha]
    norm_num [ProposedStationaryRealScale.profitCoefficient,
      ProposedStationaryRealScale.technology]
  have hscaled :
      (ProposedStationaryRealScale.userCost .H -
        alpha * ProposedStationaryRealScale.userCost .L) *
        ProposedStationaryBank.loanRate =
      (81 / 80 : ℝ) *
        (((511 / 2400 : ℝ) - alpha * (137 / 300 : ℝ)) *
            ProposedStationaryBank.loanRate +
          alpha * (13 / 32 : ℝ) - 39 / 256) := by
    dsimp [alpha]
    unfold ProposedStationaryRealScale.userCost
      ProposedStationaryRealScale.pledgeability
      ProposedStationaryRealScale.capitalPrice
    field_simp [ne_of_gt hrpos] <;> ring
  have hmargin :
      0 < (((511 / 2400 : ℝ) - alpha * (137 / 300 : ℝ)) *
            ProposedStationaryBank.loanRate +
          alpha * (13 / 32 : ℝ) - 39 / 256) := by
    dsimp [alpha]
    linarith only [hrBound]
  have hscaledPos :
      0 < (ProposedStationaryRealScale.userCost .H -
        alpha * ProposedStationaryRealScale.userCost .L) *
        ProposedStationaryBank.loanRate := by
    rw [hscaled]
    exact mul_pos (by norm_num) hmargin
  have hcost :
      alpha * ProposedStationaryRealScale.userCost .L <
        ProposedStationaryRealScale.userCost .H := by
    by_contra hn
    have hle : ProposedStationaryRealScale.userCost .H -
        alpha * ProposedStationaryRealScale.userCost .L ≤ 0 := by
      linarith only [le_of_not_gt hn]
    have hprod := mul_nonpos_of_nonpos_of_nonneg hle hrpos.le
    linarith only [hprod, hscaledPos]
  have hprofitL :
      0 < ProposedStationaryRealScale.profitCoefficient .L :=
    ProposedStationaryRealScale.profitCoefficient_pos .L
  have hcostH :
      0 < ProposedStationaryRealScale.userCost .H :=
    ProposedStationaryRealScale.userCost_pos .H
  have hcostL :
      0 < ProposedStationaryRealScale.userCost .L :=
    ProposedStationaryRealScale.userCost_pos .L
  have hprodIneq :
      ProposedStationaryRealScale.profitCoefficient .H *
          ProposedStationaryRealScale.userCost .L <
        ProposedStationaryRealScale.profitCoefficient .L *
          ProposedStationaryRealScale.userCost .H := by
    rw [hprofitRatio]
    have h := mul_lt_mul_of_pos_right hcost hprofitL
    nlinarith only [h]
  have hbase :
      (4 / 5 : ℝ) * ProposedStationaryRealScale.profitCoefficient .H /
          ProposedStationaryRealScale.userCost .H <
        (4 / 5 : ℝ) * ProposedStationaryRealScale.profitCoefficient .L /
          ProposedStationaryRealScale.userCost .L := by
    apply (div_lt_div_iff₀ hcostH hcostL).2
    have h := mul_lt_mul_of_pos_left hprodIneq
      (by norm_num : (0 : ℝ) < 4 / 5)
    nlinarith only [h]
  have hbase0 :
      0 ≤ (4 / 5 : ℝ) * ProposedStationaryRealScale.profitCoefficient .H /
          ProposedStationaryRealScale.userCost .H :=
    (div_pos
      (mul_pos (by norm_num)
        (ProposedStationaryRealScale.profitCoefficient_pos .H))
      hcostH).le
  unfold ProposedStationaryRealScale.capitalScale
  gcongr


/-- Exact-rational stationary capital-scale enclosure for the lower-
productivity firm L. Both inequalities are consequences of the SOURCE
cost box; the fifth powers and divisions are controlled over positive
domains. This is a prerequisite for the endpoint cash-flow boxes. -/
theorem boundary_source_capital_scale_L_rational_box :
    (943153 / 10000 : ℝ) <
      ProposedStationaryRealScale.capitalScale .L ∧
    ProposedStationaryRealScale.capitalScale .L <
      (943158 / 10000 : ℝ) := by
  rcases (boundary_source_user_cost_micro_boxes).2 with ⟨hcostlo, hcosthi⟩
  have hcostpos :
      0 < ProposedStationaryRealScale.userCost .L :=
    ProposedStationaryRealScale.userCost_pos .L
  have hbaseLo :
      (24826555 / 10000000 : ℝ) <
        (5 / 36 : ℝ) / ProposedStationaryRealScale.userCost .L := by
    apply (lt_div_iff₀ hcostpos).2
    linarith only [hcosthi]
  have hbaseHi :
      (5 / 36 : ℝ) / ProposedStationaryRealScale.userCost .L <
        (24826574 / 10000000 : ℝ) := by
    apply (div_lt_iff₀ hcostpos).2
    linarith only [hcostlo]
  have hpowLo :
      (24826555 / 10000000 : ℝ) ^ (5 : ℕ) <
        ((5 / 36 : ℝ) /
          ProposedStationaryRealScale.userCost .L) ^ (5 : ℕ) := by
    gcongr
  have hpowHi :
      ((5 / 36 : ℝ) /
        ProposedStationaryRealScale.userCost .L) ^ (5 : ℕ) <
        (24826574 / 10000000 : ℝ) ^ (5 : ℕ) := by
    gcongr
  have hcapital :
      ProposedStationaryRealScale.capitalScale .L =
        ((5 / 36 : ℝ) /
          ProposedStationaryRealScale.userCost .L) ^ (5 : ℕ) := by
    unfold ProposedStationaryRealScale.capitalScale
    norm_num [ProposedStationaryRealScale.profitCoefficient,
      ProposedStationaryRealScale.technology]
  rw [hcapital]
  constructor
  · exact lt_trans (by norm_num) hpowLo
  · exact lt_trans hpowHi (by norm_num)

/-- The two L-consumption endpoint boxes have a common SOURCE
numerator. An exact rational enclosure of firmCoefficient L,
rather than two unrelated endpoint assumptions, suffices for both.
The numerator bounds remain obligations to be derived from the bank
and firm primitives; this lemma does not assert those bounds. -/
theorem boundary_firm_L_endpoint_boxes_of_coefficient_box
    (hlo : (376471 / 100000 : ℝ) <
      firmCoefficient .L)
    (hhi : firmCoefficient .L <
      (376473 / 100000 : ℝ)) :
    (382592 / 100000 : ℝ) <
      normalizedFirmConsumption boundaryLo .L ∧
    normalizedFirmConsumption boundaryHi .L <
      (380000 / 100000 : ℝ) := by
  have hdenLo : 0 < (24 / 25 : ℝ) * boundaryLo := by
    norm_num [boundaryLo]
  have hdenHi : 0 < (24 / 25 : ℝ) * boundaryHi := by
    norm_num [boundaryHi]
  constructor
  · change (382592 / 100000 : ℝ) <
      firmCoefficient .L / ((24 / 25 : ℝ) * boundaryLo)
    apply (lt_div_iff₀ hdenLo).2
    exact lt_trans (by norm_num [boundaryLo]) hlo
  · change firmCoefficient .L / ((24 / 25 : ℝ) * boundaryHi) <
      (380000 / 100000 : ℝ)
    apply (div_lt_iff₀ hdenHi).2
    exact lt_trans hhi (by norm_num [boundaryHi])


/-- A sharper rational lower enclosure follows from the same *SOURCE*
cost box as the earlier coarse capital enclosure. No decimal constant is
introduced as an axiom. -/
theorem boundary_source_capital_scale_L_sharp_lower :
    (9431533 / 100000 : ℝ) <
      ProposedStationaryRealScale.capitalScale .L := by
  rcases (boundary_source_user_cost_micro_boxes).2 with ⟨_, hcosthi⟩
  have hcostpos :
      0 < ProposedStationaryRealScale.userCost .L :=
    ProposedStationaryRealScale.userCost_pos .L
  have hbaseLo :
      (24826555 / 10000000 : ℝ) <
        (5 / 36 : ℝ) / ProposedStationaryRealScale.userCost .L := by
    apply (lt_div_iff₀ hcostpos).2
    linarith only [hcosthi]
  have hpowLo :
      (24826555 / 10000000 : ℝ) ^ (5 : ℕ) <
        ((5 / 36 : ℝ) /
          ProposedStationaryRealScale.userCost .L) ^ (5 : ℕ) := by
    gcongr
  have hcapital :
      ProposedStationaryRealScale.capitalScale .L =
        ((5 / 36 : ℝ) /
          ProposedStationaryRealScale.userCost .L) ^ (5 : ℕ) := by
    unfold ProposedStationaryRealScale.capitalScale
    norm_num [ProposedStationaryRealScale.profitCoefficient,
      ProposedStationaryRealScale.technology]
  rw [hcapital]
  exact lt_trans (by norm_num) hpowLo

/-- The stationary L firm's numerator is algebraically determined by its
capital and the SOURCE bank loan rate. The correlation between capital
and loan rate is not discarded by this identity. -/
private theorem boundary_source_firm_L_coefficient_formula :
    firmCoefficient .L =
      ProposedStationaryRealScale.capitalScale .L *
        ((81 / 80 : ℝ) * ((187 / 1200 : ℝ) -
          (377 / 3200 : ℝ) / ProposedStationaryBank.loanRate)) := by
  have hrpos : 0 < ProposedStationaryBank.loanRate :=
    ProposedStationaryRealScale.loanRate_pos
  dsimp [firmCoefficient, ProposedStationaryRealScale.userCost,
    ProposedStationaryRealScale.pledgeability,
    ProposedStationaryRealScale.capitalPrice,
    ProposedStationaryRealScale.liquidationValue]
  field_simp [ne_of_gt hrpos] <;> ring

/-- Two of the original ten endpoint component inequalities are derived
from SOURCE bank pricing and firm primitives: no coefficient-box premise.
The other eight component inequalities remain independent obligations. -/
theorem boundary_firm_L_endpoint_boxes_from_source :
    (382592 / 100000 : ℝ) <
      normalizedFirmConsumption boundaryLo .L ∧
    normalizedFirmConsumption boundaryHi .L <
      (380000 / 100000 : ℝ) := by
  let f : ℝ := (81 / 80 : ℝ) *
    ((187 / 1200 : ℝ) -
      (377 / 3200 : ℝ) / ProposedStationaryBank.loanRate)
  have hrpos : 0 < ProposedStationaryBank.loanRate :=
    ProposedStationaryRealScale.loanRate_pos
  rcases boundary_source_loan_rate_micro_box with ⟨hrlo, hrhi⟩
  have hfm :
      f * ProposedStationaryBank.loanRate =
        (81 / 80 : ℝ) *
          ((187 / 1200 : ℝ) * ProposedStationaryBank.loanRate -
            (377 / 3200 : ℝ)) := by
    dsimp [f]
    field_simp [ne_of_gt hrpos] <;> ring
  have hflo : (39916157 / 1000000000 : ℝ) < f := by
    by_contra hn
    have hle : f ≤ (39916157 / 1000000000 : ℝ) :=
      le_of_not_gt hn
    have hm := mul_le_mul_of_nonneg_right hle hrpos.le
    rw [hfm] at hm
    linarith only [hm, hrlo]
  have hfhi : f < (39916165 / 1000000000 : ℝ) := by
    by_contra hn
    have hge : (39916165 / 1000000000 : ℝ) ≤ f :=
      le_of_not_gt hn
    have hm := mul_le_mul_of_nonneg_right hge hrpos.le
    rw [hfm] at hm
    linarith only [hm, hrhi]
  have hfpos : 0 < f :=
    lt_trans (by norm_num : (0 : ℝ) <
      (39916157 / 1000000000 : ℝ)) hflo
  have hklo := boundary_source_capital_scale_L_sharp_lower
  have hkhi := (boundary_source_capital_scale_L_rational_box).2
  have hcoefflo :
      (1470588 / 390625 : ℝ) < firmCoefficient .L := by
    rw [boundary_source_firm_L_coefficient_formula]
    change (1470588 / 390625 : ℝ) <
      ProposedStationaryRealScale.capitalScale .L * f
    calc
      (1470588 / 390625 : ℝ) <
          (9431533 / 100000 : ℝ) *
            (39916157 / 1000000000 : ℝ) := by norm_num
      _ < (9431533 / 100000 : ℝ) * f :=
        mul_lt_mul_of_pos_left hflo (by norm_num)
      _ < ProposedStationaryRealScale.capitalScale .L * f :=
        mul_lt_mul_of_pos_right hklo hfpos
  have hcoeffhi :
      firmCoefficient .L < (58824 / 15625 : ℝ) := by
    rw [boundary_source_firm_L_coefficient_formula]
    change ProposedStationaryRealScale.capitalScale .L * f <
      (58824 / 15625 : ℝ)
    calc
      ProposedStationaryRealScale.capitalScale .L * f <
          (943158 / 10000 : ℝ) * f :=
        mul_lt_mul_of_pos_right hkhi hfpos
      _ < (943158 / 10000 : ℝ) *
          (39916165 / 1000000000 : ℝ) :=
        mul_lt_mul_of_pos_left hfhi (by norm_num)
      _ < (58824 / 15625 : ℝ) := by norm_num
  have hdenLo : 0 < (24 / 25 : ℝ) * boundaryLo := by
    norm_num [boundaryLo]
  have hdenHi : 0 < (24 / 25 : ℝ) * boundaryHi := by
    norm_num [boundaryHi]
  constructor
  · change (382592 / 100000 : ℝ) <
      firmCoefficient .L / ((24 / 25 : ℝ) * boundaryLo)
    apply (lt_div_iff₀ hdenLo).2
    exact lt_of_le_of_lt (by norm_num [boundaryLo]) hcoefflo
  · change firmCoefficient .L / ((24 / 25 : ℝ) * boundaryHi) <
      (380000 / 100000 : ℝ)
    apply (div_lt_iff₀ hdenHi).2
    exact lt_of_lt_of_le hcoeffhi (by norm_num [boundaryHi])

/-- The independent sign certificate now has eight, not ten, open
rational inequalities; both L-consumption boxes follow from the
source-equation chain above. -/
structure BoundaryRemainingEightBoxes : Prop where
  Ylo_upper : normalizedOutput boundaryLo < 1327678 / 100000
  CWlo_lower : 793630 / 100000 < normalizedWorkerConsumption boundaryLo
  CHlo_lower : 296932 / 100000 < normalizedFirmConsumption boundaryLo .H
  GammaLo_lower : 266849 / 100000 < normalizedCapitalCost boundaryLo
  Yhi_lower : 1340498 / 100000 < normalizedOutput boundaryHi
  CWhi_upper : normalizedWorkerConsumption boundaryHi < 788240 / 100000
  CHhi_upper : normalizedFirmConsumption boundaryHi .H < 294921 / 100000
  GammaHi_upper : normalizedCapitalCost boundaryHi < 164406 / 100000

theorem boundary_component_boxes_from_eight
    (h : BoundaryRemainingEightBoxes) : BoundaryComponentBoxes := by
  rcases boundary_firm_L_endpoint_boxes_from_source with ⟨hclo, hchi⟩
  exact ⟨h.Ylo_upper, h.CWlo_lower, h.CHlo_lower, hclo,
    h.GammaLo_lower, h.Yhi_lower, h.CWhi_upper,
    h.CHhi_upper, hchi, h.GammaHi_upper⟩

/-- Certified uniqueness of the exact SOURCE scalar root on the bracket,
conditional only on the eight remaining component inequalities.
This is a 33-row reduced prefix, NOT a complete infinite-horizon
competitive equilibrium or branch-selection theorem. -/
theorem boundary_unique_reduced_prefix_rate_of_eight
    (G : ℝ) (h : BoundaryRemainingEightBoxes) :
    ∃! R : ℝ,
      boundaryLo ≤ R ∧ R ≤ boundaryHi ∧
      boundaryResourceResidual R = 0 ∧
      ∀ branch : LocalPrefixBranch,
        LocalReducedPrefixEquationsHold branch
          (boundaryPrimitives G R)
          (boundaryInitialState G R)
          (boundaryCoordinates R) .dateOne .recurrent boundaryTail := by
  exact boundary_unique_reduced_prefix_rate_of_boxes G
    (boundary_component_boxes_from_eight h)


/-- Exact-rational enclosure of the high-productivity firm's stationary
capital scale from its SOURCE user cost. This is not a GE existence claim. -/
theorem boundary_source_capital_scale_H_rational_box :
    (567703 / 10000 : ℝ) <
      ProposedStationaryRealScale.capitalScale .H ∧
    ProposedStationaryRealScale.capitalScale .H <
      (567705 / 10000 : ℝ) := by
  rcases (boundary_source_user_cost_micro_boxes).1 with ⟨hulo, huhi⟩
  have hu : 0 < ProposedStationaryRealScale.userCost .H :=
    ProposedStationaryRealScale.userCost_pos .H
  have hbaseLo :
      (22429741 / 10000000 : ℝ) <
        (10201 / 72000 : ℝ) / ProposedStationaryRealScale.userCost .H := by
    apply (lt_div_iff₀ hu).2
    linarith only [huhi]
  have hbaseHi :
      (10201 / 72000 : ℝ) / ProposedStationaryRealScale.userCost .H <
        (22429749 / 10000000 : ℝ) := by
    apply (div_lt_iff₀ hu).2
    linarith only [hulo]
  have hpowLo :
      (22429741 / 10000000 : ℝ) ^ (5 : ℕ) <
        ((10201 / 72000 : ℝ) /
          ProposedStationaryRealScale.userCost .H) ^ (5 : ℕ) := by
    gcongr
  have hpowHi :
      ((10201 / 72000 : ℝ) /
        ProposedStationaryRealScale.userCost .H) ^ (5 : ℕ) <
        (22429749 / 10000000 : ℝ) ^ (5 : ℕ) := by
    gcongr
  have hcapital :
      ProposedStationaryRealScale.capitalScale .H =
        ((10201 / 72000 : ℝ) /
          ProposedStationaryRealScale.userCost .H) ^ (5 : ℕ) := by
    unfold ProposedStationaryRealScale.capitalScale
    norm_num [ProposedStationaryRealScale.profitCoefficient,
      ProposedStationaryRealScale.technology]
  rw [hcapital]
  constructor
  · exact lt_trans (by norm_num) hpowLo
  · exact lt_trans hpowHi (by norm_num)

/-- Original SOURCE bank pricing converts the firm's non-normalized
consumption coefficient into a rational loan-rate factor times capital. -/
private theorem boundary_source_firm_H_coefficient_formula :
    firmCoefficient .H =
      ProposedStationaryRealScale.capitalScale .H *
        ((81 / 80 : ℝ) * ((911 / 9600 : ℝ) -
          (1131 / 25600 : ℝ) / ProposedStationaryBank.loanRate)) := by
  have hr : 0 < ProposedStationaryBank.loanRate :=
    ProposedStationaryRealScale.loanRate_pos
  dsimp [firmCoefficient, ProposedStationaryRealScale.userCost,
    ProposedStationaryRealScale.pledgeability,
    ProposedStationaryRealScale.capitalPrice,
    ProposedStationaryRealScale.liquidationValue]
  field_simp [ne_of_gt hr] <;> ring

/-- The H firm's SOURCE numerator falls within a strict rational box
sufficiently sharp for both original endpoint consumption inequalities. -/
theorem boundary_source_firm_H_coefficient_rational_box :
    (294539 / 100000 : ℝ) < firmCoefficient .H ∧
    firmCoefficient .H < (294541 / 100000 : ℝ) := by
  let f : ℝ := (81 / 80 : ℝ) *
    ((911 / 9600 : ℝ) -
      (1131 / 25600 : ℝ) / ProposedStationaryBank.loanRate)
  have hr : 0 < ProposedStationaryBank.loanRate :=
    ProposedStationaryRealScale.loanRate_pos
  rcases boundary_source_loan_rate_micro_box with ⟨hrlo, hrhi⟩
  have hfm :
      f * ProposedStationaryBank.loanRate =
        (81 / 80 : ℝ) *
          ((911 / 9600 : ℝ) * ProposedStationaryBank.loanRate -
            (1131 / 25600 : ℝ)) := by
    dsimp [f]
    field_simp [ne_of_gt hr] <;> ring
  have hflo : (518826 / 10000000 : ℝ) < f := by
    by_contra hn
    have hle : f ≤ (518826 / 10000000 : ℝ) := le_of_not_gt hn
    have hm := mul_le_mul_of_nonneg_right hle hr.le
    rw [hfm] at hm
    linarith only [hm, hrlo]
  have hfhi : f < (518827 / 10000000 : ℝ) := by
    by_contra hn
    have hge : (518827 / 10000000 : ℝ) ≤ f := le_of_not_gt hn
    have hm := mul_le_mul_of_nonneg_right hge hr.le
    rw [hfm] at hm
    linarith only [hm, hrhi]
  have hfpos : 0 < f :=
    lt_trans (by norm_num : (0 : ℝ) < 518826 / 10000000) hflo
  rcases boundary_source_capital_scale_H_rational_box with ⟨hklo, hkhi⟩
  rw [boundary_source_firm_H_coefficient_formula]
  change (294539 / 100000 : ℝ) <
    ProposedStationaryRealScale.capitalScale .H * f ∧
    ProposedStationaryRealScale.capitalScale .H * f <
      (294541 / 100000 : ℝ)
  constructor
  · calc
      (294539 / 100000 : ℝ) <
          (567703 / 10000 : ℝ) * (518826 / 10000000 : ℝ) := by norm_num
      _ < (567703 / 10000 : ℝ) * f :=
        mul_lt_mul_of_pos_left hflo (by norm_num)
      _ < ProposedStationaryRealScale.capitalScale .H * f :=
        mul_lt_mul_of_pos_right hklo hfpos
  · calc
      ProposedStationaryRealScale.capitalScale .H * f <
          (567705 / 10000 : ℝ) * f :=
        mul_lt_mul_of_pos_right hkhi hfpos
      _ < (567705 / 10000 : ℝ) * (518827 / 10000000 : ℝ) :=
        mul_lt_mul_of_pos_left hfhi (by norm_num)
      _ < (294541 / 100000 : ℝ) := by norm_num


/-- Both high-productivity H consumption endpoint enclosures are consequences
of the original firm coefficient, source user-cost bounds, and the exact
financial price-identity. The strict margins are proved by rational arithmetic,
not by importing interval output as axioms. -/
theorem boundary_firm_H_endpoint_boxes_from_source :
    (296932 / 100000 : ℝ) <
      normalizedFirmConsumption boundaryLo .H ∧
    normalizedFirmConsumption boundaryHi .H <
      (294921 / 100000 : ℝ) := by
  rcases boundary_source_firm_H_coefficient_rational_box with
    ⟨hcLo, hcHi⟩
  rcases (boundary_source_user_cost_micro_boxes).1 with
    ⟨huHlo, huHhi⟩
  rcases (boundary_source_user_cost_micro_boxes).2 with
    ⟨huLlo, huLhi⟩
  have hprice :
      parentEffectivePrice .H =
        (24 / 25 : ℝ) *
          (ProposedStationaryRealScale.userCost .H +
            (17 / 20 : ℝ) *
              ProposedStationaryRealScale.liquidationValue) := by
    rw [parentEffectivePrice_identity .H]
    dsimp [continuationReturn, ProposedStationaryRealScale.pledgeability]
    ring
  have hpriceLo :
      (8661847 / 10000000 : ℝ) < parentEffectivePrice .H := by
    rw [hprice]
    dsimp [ProposedStationaryRealScale.liquidationValue,
      ProposedStationaryRealScale.capitalPrice]
    linarith only [huHlo]
  have hpriceHi :
      parentEffectivePrice .H < (8661848 / 10000000 : ℝ) := by
    rw [hprice]
    dsimp [ProposedStationaryRealScale.liquidationValue,
      ProposedStationaryRealScale.capitalPrice]
    linarith only [huHhi]
  have hnLo :
      (895053 / 1000000 : ℝ) <
        continuationReturn .L -
          ProposedStationaryRealScale.pledgeability .H *
            ProposedStationaryRealScale.liquidationValue := by
    dsimp [continuationReturn, ProposedStationaryRealScale.pledgeability,
      ProposedStationaryRealScale.liquidationValue,
      ProposedStationaryRealScale.capitalPrice]
    linarith only [huLlo]
  have hnHi :
      continuationReturn .L -
        ProposedStationaryRealScale.pledgeability .H *
          ProposedStationaryRealScale.liquidationValue <
        (8950531 / 10000000 : ℝ) := by
    dsimp [continuationReturn, ProposedStationaryRealScale.pledgeability,
      ProposedStationaryRealScale.liquidationValue,
      ProposedStationaryRealScale.capitalPrice]
    linarith only [huLhi]
  have hnpos :
      0 < continuationReturn .L -
        ProposedStationaryRealScale.pledgeability .H *
          ProposedStationaryRealScale.liquidationValue :=
    lt_trans (by norm_num : (0 : ℝ) < 895053 / 1000000) hnLo
  have hprodLo :
      (294539 / 100000 : ℝ) * (895053 / 1000000 : ℝ) <
        firmCoefficient .H *
          (continuationReturn .L -
            ProposedStationaryRealScale.pledgeability .H *
              ProposedStationaryRealScale.liquidationValue) := by
    calc
      _ < (294539 / 100000 : ℝ) *
            (continuationReturn .L -
              ProposedStationaryRealScale.pledgeability .H *
                ProposedStationaryRealScale.liquidationValue) :=
        mul_lt_mul_of_pos_left hnLo (by norm_num)
      _ < _ := mul_lt_mul_of_pos_right hcLo hnpos
  have hprodHi :
      firmCoefficient .H *
        (continuationReturn .L -
          ProposedStationaryRealScale.pledgeability .H *
            ProposedStationaryRealScale.liquidationValue) <
      (294541 / 100000 : ℝ) * (8950531 / 10000000 : ℝ) := by
    calc
      _ < (294541 / 100000 : ℝ) *
            (continuationReturn .L -
              ProposedStationaryRealScale.pledgeability .H *
                ProposedStationaryRealScale.liquidationValue) :=
        mul_lt_mul_of_pos_right hcHi hnpos
      _ < _ := mul_lt_mul_of_pos_left hnHi (by norm_num)
  have hRlo : 0 < boundaryLo := by norm_num [boundaryLo]
  have hRhi : 0 < boundaryHi := by norm_num [boundaryHi]
  have hpricepos : 0 < parentEffectivePrice .H :=
    parentEffectivePrice_pos .H
  have hdenLo : 0 < boundaryLo * parentEffectivePrice .H :=
    mul_pos hRlo hpricepos
  have hdenHi : 0 < boundaryHi * parentEffectivePrice .H :=
    mul_pos hRhi hpricepos
  constructor
  · change (296932 / 100000 : ℝ) <
      firmCoefficient .H *
        (continuationReturn .L -
          ProposedStationaryRealScale.pledgeability .H *
            ProposedStationaryRealScale.liquidationValue) /
          (boundaryLo * parentEffectivePrice .H)
    apply (lt_div_iff₀ hdenLo).2
    have hdenlt :
        boundaryLo * parentEffectivePrice .H <
          boundaryLo * (8661848 / 10000000 : ℝ) :=
      mul_lt_mul_of_pos_left hpriceHi hRlo
    calc
      (296932 / 100000 : ℝ) *
          (boundaryLo * parentEffectivePrice .H) <
        (296932 / 100000 : ℝ) *
          (boundaryLo * (8661848 / 10000000 : ℝ)) :=
        mul_lt_mul_of_pos_left hdenlt (by norm_num)
      _ < (294539 / 100000 : ℝ) * (895053 / 1000000 : ℝ) := by
        norm_num [boundaryLo]
      _ < _ := hprodLo
  · change firmCoefficient .H *
        (continuationReturn .L -
          ProposedStationaryRealScale.pledgeability .H *
            ProposedStationaryRealScale.liquidationValue) /
          (boundaryHi * parentEffectivePrice .H) <
        (294921 / 100000 : ℝ)
    apply (div_lt_iff₀ hdenHi).2
    have hdenlt :
        boundaryHi * (8661847 / 10000000 : ℝ) <
          boundaryHi * parentEffectivePrice .H :=
      mul_lt_mul_of_pos_left hpriceLo hRhi
    calc
      firmCoefficient .H *
        (continuationReturn .L -
          ProposedStationaryRealScale.pledgeability .H *
            ProposedStationaryRealScale.liquidationValue) <
        (294541 / 100000 : ℝ) * (8950531 / 10000000 : ℝ) :=
        hprodHi
      _ < (294921 / 100000 : ℝ) *
          (boundaryHi * (8661847 / 10000000 : ℝ)) := by
        norm_num [boundaryHi]
      _ < (294921 / 100000 : ℝ) *
          (boundaryHi * parentEffectivePrice .H) :=
        mul_lt_mul_of_pos_left hdenlt (by norm_num)

/-- The only remaining endpoint-sign premises concern aggregate output,
worker consumption and capital-installation costs at both endpoints. -/
structure BoundaryRemainingSixBoxes : Prop where
  Ylo_upper : normalizedOutput boundaryLo < 1327678 / 100000
  CWlo_lower : 793630 / 100000 < normalizedWorkerConsumption boundaryLo
  GammaLo_lower : 266849 / 100000 < normalizedCapitalCost boundaryLo
  Yhi_lower : 1340498 / 100000 < normalizedOutput boundaryHi
  CWhi_upper : normalizedWorkerConsumption boundaryHi < 788240 / 100000
  GammaHi_upper : normalizedCapitalCost boundaryHi < 164406 / 100000

theorem boundary_eight_boxes_from_six
    (h : BoundaryRemainingSixBoxes) : BoundaryRemainingEightBoxes := by
  rcases boundary_firm_H_endpoint_boxes_from_source with ⟨hlo, hhi⟩
  exact ⟨h.Ylo_upper, h.CWlo_lower, hlo, h.GammaLo_lower,
    h.Yhi_lower, h.CWhi_upper, hhi, h.GammaHi_upper⟩

/-- Uniqueness is only for the SOURCE scalar rate plus the 33-row reduced
prefix. No full competitive equilibrium or infinite continuation is proved. -/
theorem boundary_unique_reduced_prefix_rate_of_six
    (G : ℝ) (h : BoundaryRemainingSixBoxes) :
    ∃! R : ℝ,
      boundaryLo ≤ R ∧ R ≤ boundaryHi ∧
      boundaryResourceResidual R = 0 ∧
      ∀ branch : LocalPrefixBranch,
        LocalReducedPrefixEquationsHold branch
          (boundaryPrimitives G R)
          (boundaryInitialState G R)
          (boundaryCoordinates R) .dateOne .recurrent boundaryTail := by
  exact boundary_unique_reduced_prefix_rate_of_eight G
    (boundary_eight_boxes_from_six h)


/-- The upper endpoint's *original* stationary capital-installation
cost has a certified strict rational upper bound. This is obtained by
enclosing K_H, K_L and the date-zero capital scaling from SOURCE
costs and prices. It does not assume an endpoint sign. -/
theorem boundary_capital_cost_hi_box_from_source :
    normalizedCapitalCost boundaryHi < (164406 / 100000 : ℝ) := by
  rcases (boundary_source_user_cost_micro_boxes).2 with ⟨hulo, huhi⟩
  have hden :
      0 < 2 * continuationReturn .L -
        (41 / 40 : ℝ) * boundaryHi := by
    dsimp [continuationReturn, ProposedStationaryRealScale.liquidationValue,
      ProposedStationaryRealScale.capitalPrice, boundaryHi]
    linarith only [hulo]
  have hsLo :
      (10034396 / 10000000 : ℝ) <
        boundaryCapitalScale boundaryHi := by
    rw [boundaryCapitalScale_rewrite boundaryHi
      (by norm_num [boundaryHi])]
    apply (lt_div_iff₀ hden).2
    dsimp [continuationReturn, ProposedStationaryRealScale.liquidationValue,
      ProposedStationaryRealScale.capitalPrice, boundaryHi]
    linarith only [huhi]
  have hfour :
      4 * (10034396 / 10000000 : ℝ) <
        4 * boundaryCapitalScale boundaryHi := by
    nlinarith only [hsLo]
  have hinv :
      (1 : ℝ) / (4 * boundaryCapitalScale boundaryHi) <
        1 / (4 * (10034396 / 10000000 : ℝ)) :=
    one_div_lt_one_div_of_lt (by norm_num) hfour
  have hfactor :
      (41 / 80 : ℝ) +
          1 / (4 * boundaryCapitalScale boundaryHi) -
          (4719 / 6400 : ℝ) * boundaryCapitalScale boundaryHi <
        (2176319 / 100000000 : ℝ) := by
    have hrat :
        (41 / 80 : ℝ) +
            1 / (4 * (10034396 / 10000000 : ℝ)) -
            (4719 / 6400 : ℝ) * (10034396 / 10000000 : ℝ) <
          (2176319 / 100000000 : ℝ) := by norm_num
    linarith only [hinv, hsLo, hrat]
  have hKpos : 0 < ProposedStationaryRealScale.average
      ProposedStationaryRealScale.capitalScale :=
    ProposedStationaryRealScale.aggregate_scales_pos.1
  have hKbound :
      ProposedStationaryRealScale.average
          ProposedStationaryRealScale.capitalScale <
        (7554315 / 100000 : ℝ) := by
    rcases boundary_source_capital_scale_H_rational_box with ⟨_, hH⟩
    rcases boundary_source_capital_scale_L_rational_box with ⟨_, hL⟩
    unfold ProposedStationaryRealScale.average
    linarith only [hH, hL]
  have hproduct :
      normalizedCapitalCost boundaryHi <
        (7554315 / 100000 : ℝ) *
          (2176319 / 100000000 : ℝ) := by
    unfold normalizedCapitalCost
    calc
      _ < ProposedStationaryRealScale.average
          ProposedStationaryRealScale.capitalScale *
            (2176319 / 100000000 : ℝ) :=
          mul_lt_mul_of_pos_left hfactor hKpos
      _ < (7554315 / 100000 : ℝ) *
            (2176319 / 100000000 : ℝ) :=
          mul_lt_mul_of_pos_right hKbound (by norm_num)
  exact lt_trans hproduct (by norm_num)

/-- Five explicit endpoint inequalities remain independent: output
and worker consumption at both ends, plus installation cost at the
lower end. The upper installation-cost box follows from SOURCE. -/
structure BoundaryRemainingFiveBoxes : Prop where
  Ylo_upper : normalizedOutput boundaryLo < 1327678 / 100000
  CWlo_lower : 793630 / 100000 < normalizedWorkerConsumption boundaryLo
  GammaLo_lower : 266849 / 100000 < normalizedCapitalCost boundaryLo
  Yhi_lower : 1340498 / 100000 < normalizedOutput boundaryHi
  CWhi_upper : normalizedWorkerConsumption boundaryHi < 788240 / 100000

theorem boundary_six_boxes_from_five
    (h : BoundaryRemainingFiveBoxes) : BoundaryRemainingSixBoxes := by
  exact ⟨h.Ylo_upper, h.CWlo_lower, h.GammaLo_lower,
    h.Yhi_lower, h.CWhi_upper, boundary_capital_cost_hi_box_from_source⟩

/-- Strictly conditional scalar uniqueness and the 33-row prefix. The
five remaining boxes are not yet Lean-proved from SOURCE primitives. -/
theorem boundary_unique_reduced_prefix_rate_of_five
    (G : ℝ) (h : BoundaryRemainingFiveBoxes) :
    ∃! R : ℝ,
      boundaryLo ≤ R ∧ R ≤ boundaryHi ∧
      boundaryResourceResidual R = 0 ∧
      ∀ branch : LocalPrefixBranch,
        LocalReducedPrefixEquationsHold branch
          (boundaryPrimitives G R)
          (boundaryInitialState G R)
          (boundaryCoordinates R) .dateOne .recurrent boundaryTail := by
  exact boundary_unique_reduced_prefix_rate_of_six G
    (boundary_six_boxes_from_five h)


/-- Independent, rational SOURCE bound for stationary worker consumption
in the initial normalization. The bound uses the *same* bank loan
rate, firm user costs, aggregate capital and lending as the parent
construction; no external midpoint or rounded root is assumed. -/
theorem boundary_worker_consumption_scale_upper :
    ProposedStationaryRealScale.workerConsumptionScale <
      (8038094 / 1000000 : ℝ) := by
  rcases boundary_source_loan_rate_micro_box with ⟨hrlo, hrhi⟩
  rcases boundary_source_user_cost_micro_boxes with
    ⟨⟨_, huHhi⟩, ⟨_, huLhi⟩⟩
  rcases boundary_source_capital_scale_H_rational_box with ⟨_, hkHhi⟩
  rcases boundary_source_capital_scale_L_rational_box with ⟨_, hkLhi⟩
  have hkHpos := ProposedStationaryRealScale.capitalScale_pos .H
  have hkLpos := ProposedStationaryRealScale.capitalScale_pos .L
  have hprodH :
      ProposedStationaryRealScale.userCost .H *
          ProposedStationaryRealScale.capitalScale .H <
        (6316638 / 100000000 : ℝ) * (567705 / 10000 : ℝ) := by
    calc
      _ < (6316638 / 100000000 : ℝ) *
            ProposedStationaryRealScale.capitalScale .H :=
        mul_lt_mul_of_pos_right huHhi hkHpos
      _ < _ := mul_lt_mul_of_pos_left hkHhi (by norm_num)
  have hprodL :
      ProposedStationaryRealScale.userCost .L *
          ProposedStationaryRealScale.capitalScale .L <
        (5594368 / 100000000 : ℝ) * (943158 / 10000 : ℝ) := by
    calc
      _ < (5594368 / 100000000 : ℝ) *
            ProposedStationaryRealScale.capitalScale .L :=
        mul_lt_mul_of_pos_right huLhi hkLpos
      _ < _ := mul_lt_mul_of_pos_left hkLhi (by norm_num)
  have hYexpr :
      ProposedStationaryRealScale.outputScale =
        (3 / 2 : ℝ) *
          (ProposedStationaryRealScale.userCost .H *
              ProposedStationaryRealScale.capitalScale .H +
            ProposedStationaryRealScale.userCost .L *
              ProposedStationaryRealScale.capitalScale .L) := by
    unfold ProposedStationaryRealScale.outputScale
      ProposedStationaryRealScale.average
    ring
  have hYhi :
      ProposedStationaryRealScale.outputScale <
        (1329354 / 100000 : ℝ) := by
    rw [hYexpr]
    have hsum := add_lt_add hprodH hprodL
    linarith only [hsum]
  have hKhi :
      ProposedStationaryRealScale.average
          ProposedStationaryRealScale.capitalScale <
        (7554315 / 100000 : ℝ) := by
    unfold ProposedStationaryRealScale.average
    linarith only [hkHhi, hkLhi]
  have hrpos : 0 < ProposedStationaryBank.loanRate :=
    ProposedStationaryRealScale.loanRate_pos
  have hcreditScaled :
      ProposedStationaryRealScale.creditScale *
          ProposedStationaryBank.loanRate =
        ((3 / 20 : ℝ) * (3159 / 3200 : ℝ) *
            ProposedStationaryRealScale.capitalScale .H +
          (2 / 5 : ℝ) * (3159 / 3200 : ℝ) *
            ProposedStationaryRealScale.capitalScale .L) / 2 := by
    unfold ProposedStationaryRealScale.creditScale
      ProposedStationaryRealScale.average
      ProposedStationaryRealScale.pledgeability
      ProposedStationaryRealScale.liquidationValue
      ProposedStationaryRealScale.capitalPrice
    field_simp [ne_of_gt hrpos] <;> ring
  have hcreditScaledUpper :
      ((3 / 20 : ℝ) * (3159 / 3200 : ℝ) *
          ProposedStationaryRealScale.capitalScale .H +
        (2 / 5 : ℝ) * (3159 / 3200 : ℝ) *
          ProposedStationaryRealScale.capitalScale .L) / 2 <
        (22553 / 1000 : ℝ) * (101204821 / 100000000 : ℝ) := by
    linarith only [hkHhi, hkLhi]
  have hcreditUpper :
      ProposedStationaryRealScale.creditScale <
        (22553 / 1000 : ℝ) := by
    by_contra hn
    have hge : (22553 / 1000 : ℝ) ≤
        ProposedStationaryRealScale.creditScale := le_of_not_gt hn
    have hm := mul_le_mul_of_nonneg_right hge hrpos.le
    rw [hcreditScaled] at hm
    linarith only [hcreditScaledUpper, hm, hrlo]
  have hdiff : 0 < ProposedStationaryBank.loanRate - 1 :=
    sub_pos.mpr ProposedStationaryRealScale.loanRate_gt_one
  have hcreditPayoff :
      (ProposedStationaryBank.loanRate - 1) *
          ProposedStationaryRealScale.creditScale <
        ((101204827 / 100000000 : ℝ) - 1) *
          (22553 / 1000 : ℝ) := by
    calc
      _ < (ProposedStationaryBank.loanRate - 1) *
            (22553 / 1000 : ℝ) :=
        mul_lt_mul_of_pos_left hcreditUpper hdiff
      _ < _ :=
        mul_lt_mul_of_pos_right (by linarith only [hrhi]) (by norm_num)
  have hrat :
      (7 / 12 : ℝ) * (1329354 / 100000 : ℝ) +
        (7554315 / 100000 : ℝ) / 6400 +
        ((101204827 / 100000000 : ℝ) - 1) *
          (22553 / 1000 : ℝ) <
        (8038094 / 1000000 : ℝ) := by norm_num
  unfold ProposedStationaryRealScale.workerConsumptionScale
  linarith only [hYhi, hKhi, hcreditPayoff, hrat]

/-- Source OTC slope boxes imply a strict, rational lower enclosure of
the *boundary date-zero* deposit rate at R=129/125. Markov and policy
prices remain the original ones; no midpoint of the stationary root is
substituted. -/
theorem boundary_deposit_rate_hi_source_lower :
    (10300529 / 10000000 : ℝ) <
      boundaryDepositRate boundaryHi := by
  rcases boundary_source_slope_rational_micro_boxes with
    ⟨⟨_, hmhi⟩, ⟨hglo, hghi⟩⟩
  have hRmem : boundaryHi ∈ boundaryInterval :=
    ⟨le_of_lt boundaryLo_lt_boundaryHi, le_refl _⟩
  have hrrpos : 0 < boundaryReserveRate boundaryHi :=
    (boundary_rate_domain hRmem).2
  have hpaymentpos : 0 < boundaryPaymentTerm := by
    unfold boundaryPaymentTerm
    linarith only [hglo]
  have hnum :
      (1031285357 / 1000000000 : ℝ) <
        boundaryReserveRate boundaryHi +
          (9 / 10 : ℝ) * ProposedStationaryBank.meanSlope +
          (1 / 10 : ℝ) * boundaryPaymentTerm := by
    unfold boundaryReserveRate boundaryPaymentTerm boundaryHi
    linarith only [hmhi, hglo]
  have hfrac :
      boundaryPaymentTerm / boundaryReserveRate boundaryHi <
        (1196474 / 1000000000 : ℝ) := by
    apply (div_lt_iff₀ hrrpos).2
    unfold boundaryPaymentTerm boundaryReserveRate boundaryHi
    linarith only [hmhi, hghi]
  have hdenpos :
      0 < 1 + boundaryPaymentTerm / boundaryReserveRate boundaryHi := by
    have hd := div_pos hpaymentpos hrrpos
    linarith only [hd]
  have hdenUpper :
      1 + boundaryPaymentTerm / boundaryReserveRate boundaryHi <
        (1001196474 / 1000000000 : ℝ) := by
    linarith only [hfrac]
  change (10300529 / 10000000 : ℝ) <
    (boundaryReserveRate boundaryHi +
      (9 / 10 : ℝ) * ProposedStationaryBank.meanSlope +
      (1 / 10 : ℝ) * boundaryPaymentTerm) /
    (1 + boundaryPaymentTerm / boundaryReserveRate boundaryHi)
  apply (lt_div_iff₀ hdenpos).2
  calc
    (10300529 / 10000000 : ℝ) *
        (1 + boundaryPaymentTerm / boundaryReserveRate boundaryHi) <
      (10300529 / 10000000 : ℝ) *
        (1001196474 / 1000000000 : ℝ) :=
      mul_lt_mul_of_pos_left hdenUpper (by norm_num)
    _ < (1031285357 / 1000000000 : ℝ) := by norm_num
    _ < _ := hnum

/-- The upper-end worker-consumption box has been discharged from
SOURCE bank prices, firm capital, costs and credit, with exact strict
margins. This is independent of the unproved output-root endpoint
certificate. -/
theorem boundary_worker_hi_box_from_source :
    normalizedWorkerConsumption boundaryHi <
      (788240 / 100000 : ℝ) := by
  have hw := boundary_worker_consumption_scale_upper
  have hrd := boundary_deposit_rate_hi_source_lower
  have hden : 0 < (99 / 100 : ℝ) * boundaryDepositRate boundaryHi := by
    exact mul_pos (by norm_num)
      (lt_trans (by norm_num : (0 : ℝ) < 10300529 / 10000000) hrd)
  unfold normalizedWorkerConsumption
  apply (div_lt_iff₀ hden).2
  have hrat :
      (8038094 / 1000000 : ℝ) <
        (788240 / 100000 : ℝ) *
          ((99 / 100 : ℝ) * (10300529 / 10000000 : ℝ)) := by
    norm_num
  have hrate :
      (788240 / 100000 : ℝ) *
          ((99 / 100 : ℝ) * (10300529 / 10000000 : ℝ)) <
        (788240 / 100000 : ℝ) *
          ((99 / 100 : ℝ) * boundaryDepositRate boundaryHi) := by
    have hmult := mul_lt_mul_of_pos_left hrd
      (by norm_num : (0 : ℝ) < 99 / 100)
    exact mul_lt_mul_of_pos_left hmult (by norm_num)
  exact lt_trans hw (lt_trans hrat hrate)

/-- After proving the SOURCE upper-end worker and installation cost,
only four endpoint boxes survive, two of them containing the real
fifteenth root of normalized output. -/
structure BoundaryRemainingFourBoxes : Prop where
  Ylo_upper : normalizedOutput boundaryLo < 1327678 / 100000
  CWlo_lower : 793630 / 100000 < normalizedWorkerConsumption boundaryLo
  GammaLo_lower : 266849 / 100000 < normalizedCapitalCost boundaryLo
  Yhi_lower : 1340498 / 100000 < normalizedOutput boundaryHi

theorem boundary_five_boxes_from_four
    (h : BoundaryRemainingFourBoxes) : BoundaryRemainingFiveBoxes := by
  exact ⟨h.Ylo_upper, h.CWlo_lower, h.GammaLo_lower,
    h.Yhi_lower, boundary_worker_hi_box_from_source⟩

theorem boundary_unique_reduced_prefix_rate_of_four
    (G : ℝ) (h : BoundaryRemainingFourBoxes) :
    ∃! R : ℝ,
      boundaryLo ≤ R ∧ R ≤ boundaryHi ∧
      boundaryResourceResidual R = 0 ∧
      ∀ branch : LocalPrefixBranch,
        LocalReducedPrefixEquationsHold branch
          (boundaryPrimitives G R)
          (boundaryInitialState G R)
          (boundaryCoordinates R) .dateOne .recurrent boundaryTail := by
  exact boundary_unique_reduced_prefix_rate_of_five G
    (boundary_five_boxes_from_four h)

/-- A finer SOURCE user-cost box from the quadratic bank solution:
the lower R_L bound and the upper R_L bound are kernel-proved rather
than rounded decimal estimates. -/
theorem boundary_source_user_cost_sharp_boxes :
    ((63166370 / 1000000000 : ℝ) <
        ProposedStationaryRealScale.userCost .H ∧
      ProposedStationaryRealScale.userCost .H <
        (63166372 / 1000000000 : ℝ)) ∧
    ((55943655 / 1000000000 : ℝ) <
        ProposedStationaryRealScale.userCost .L ∧
      ProposedStationaryRealScale.userCost .L <
        (55943657 / 1000000000 : ℝ)) := by
  rcases boundary_source_loan_rate_sharp_box with ⟨hrlo, hrhi⟩
  have hrpos : 0 < ProposedStationaryBank.loanRate :=
    ProposedStationaryRealScale.loanRate_pos
  have hscaledH :
      ProposedStationaryRealScale.userCost .H *
        ProposedStationaryBank.loanRate =
      (81 / 80 : ℝ) *
        ((511 / 2400 : ℝ) * ProposedStationaryBank.loanRate -
          39 / 256) := by
    unfold ProposedStationaryRealScale.userCost
      ProposedStationaryRealScale.capitalPrice
      ProposedStationaryRealScale.pledgeability
    field_simp [ne_of_gt hrpos] <;> ring
  have hscaledL :
      ProposedStationaryRealScale.userCost .L *
        ProposedStationaryBank.loanRate =
      (81 / 80 : ℝ) *
        ((137 / 300 : ℝ) * ProposedStationaryBank.loanRate -
          13 / 32) := by
    unfold ProposedStationaryRealScale.userCost
      ProposedStationaryRealScale.capitalPrice
      ProposedStationaryRealScale.pledgeability
    field_simp [ne_of_gt hrpos] <;> ring
  constructor
  · constructor
    · by_contra hn
      have hle :
          ProposedStationaryRealScale.userCost .H ≤
            (63166370 / 1000000000 : ℝ) := le_of_not_gt hn
      have hm := mul_le_mul_of_nonneg_right hle hrpos.le
      rw [hscaledH] at hm
      linarith only [hm, hrlo]
    · by_contra hn
      have hge :
          (63166372 / 1000000000 : ℝ) ≤
            ProposedStationaryRealScale.userCost .H := le_of_not_gt hn
      have hm := mul_le_mul_of_nonneg_right hge hrpos.le
      rw [hscaledH] at hm
      linarith only [hm, hrhi]
  · constructor
    · by_contra hn
      have hle :
          ProposedStationaryRealScale.userCost .L ≤
            (55943655 / 1000000000 : ℝ) := le_of_not_gt hn
      have hm := mul_le_mul_of_nonneg_right hle hrpos.le
      rw [hscaledL] at hm
      linarith only [hm, hrlo]
    · by_contra hn
      have hge :
          (55943657 / 1000000000 : ℝ) ≤
            ProposedStationaryRealScale.userCost .L := le_of_not_gt hn
      have hm := mul_le_mul_of_nonneg_right hge hrpos.le
      rw [hscaledL] at hm
      linarith only [hm, hrhi]

/-- Sharper capital-scale enclosures for *both* heterogeneous firms,
from source user costs and fifth powers. No GE capital allocation is
asserted; these values describe the stationary SOURCE candidate. -/
theorem boundary_source_capital_scales_sharp_boxes :
    ((5677035 / 100000 : ℝ) <
        ProposedStationaryRealScale.capitalScale .H ∧
      ProposedStationaryRealScale.capitalScale .H <
        (5677037 / 100000 : ℝ)) ∧
    ((9431553 / 100000 : ℝ) <
        ProposedStationaryRealScale.capitalScale .L ∧
      ProposedStationaryRealScale.capitalScale .L <
        (9431556 / 100000 : ℝ)) := by
  rcases boundary_source_user_cost_sharp_boxes with
    ⟨⟨huHlo, huHhi⟩, ⟨huLlo, huLhi⟩⟩
  constructor
  · have hu : 0 < ProposedStationaryRealScale.userCost .H :=
      ProposedStationaryRealScale.userCost_pos .H
    have hbaseLo :
        (224297440 / 100000000 : ℝ) <
          (10201 / 72000 : ℝ) /
            ProposedStationaryRealScale.userCost .H := by
      apply (lt_div_iff₀ hu).2
      linarith only [huHhi]
    have hbaseHi :
        (10201 / 72000 : ℝ) /
            ProposedStationaryRealScale.userCost .H <
          (224297448 / 100000000 : ℝ) := by
      apply (div_lt_iff₀ hu).2
      linarith only [huHlo]
    have hpowLo :
        (224297440 / 100000000 : ℝ) ^ (5 : ℕ) <
          ((10201 / 72000 : ℝ) /
            ProposedStationaryRealScale.userCost .H) ^ (5 : ℕ) := by
      gcongr
    have hpowHi :
        ((10201 / 72000 : ℝ) /
            ProposedStationaryRealScale.userCost .H) ^ (5 : ℕ) <
          (224297448 / 100000000 : ℝ) ^ (5 : ℕ) := by
      gcongr
    have hcap :
        ProposedStationaryRealScale.capitalScale .H =
          ((10201 / 72000 : ℝ) /
            ProposedStationaryRealScale.userCost .H) ^ (5 : ℕ) := by
      unfold ProposedStationaryRealScale.capitalScale
      norm_num [ProposedStationaryRealScale.profitCoefficient,
        ProposedStationaryRealScale.technology]
    rw [hcap]
    constructor
    · exact lt_trans (by norm_num) hpowLo
    · exact lt_trans hpowHi (by norm_num)
  · have hu : 0 < ProposedStationaryRealScale.userCost .L :=
      ProposedStationaryRealScale.userCost_pos .L
    have hbaseLo :
        (248265659 / 100000000 : ℝ) <
          (5 / 36 : ℝ) /
            ProposedStationaryRealScale.userCost .L := by
      apply (lt_div_iff₀ hu).2
      linarith only [huLhi]
    have hbaseHi :
        (5 / 36 : ℝ) /
            ProposedStationaryRealScale.userCost .L <
          (248265669 / 100000000 : ℝ) := by
      apply (div_lt_iff₀ hu).2
      linarith only [huLlo]
    have hpowLo :
        (248265659 / 100000000 : ℝ) ^ (5 : ℕ) <
          ((5 / 36 : ℝ) /
            ProposedStationaryRealScale.userCost .L) ^ (5 : ℕ) := by
      gcongr
    have hpowHi :
        ((5 / 36 : ℝ) /
            ProposedStationaryRealScale.userCost .L) ^ (5 : ℕ) <
          (248265669 / 100000000 : ℝ) ^ (5 : ℕ) := by
      gcongr
    have hcap :
        ProposedStationaryRealScale.capitalScale .L =
          ((5 / 36 : ℝ) /
            ProposedStationaryRealScale.userCost .L) ^ (5 : ℕ) := by
      unfold ProposedStationaryRealScale.capitalScale
      norm_num [ProposedStationaryRealScale.profitCoefficient,
        ProposedStationaryRealScale.technology]
    rw [hcap]
    constructor
    · exact lt_trans (by norm_num) hpowLo
    · exact lt_trans hpowHi (by norm_num)

/-- The lower-end capital installation inequality from the *SOURCE*
economic functions. Source-specific positivity and the sharp firm
capital envelopes discharge the numerical bracket premise. -/
theorem boundary_capital_cost_lo_box_from_source :
    (266849 / 100000 : ℝ) <
      normalizedCapitalCost boundaryLo := by
  rcases boundary_source_user_cost_sharp_boxes with
    ⟨_, ⟨huLlo, _⟩⟩
  have hden :
      0 < 2 * continuationReturn .L -
        (41 / 40 : ℝ) * boundaryLo := by
    dsimp [continuationReturn,
      ProposedStationaryRealScale.liquidationValue,
      ProposedStationaryRealScale.capitalPrice, boundaryLo]
    linarith only [huLlo]
  have hsHi :
      boundaryCapitalScale boundaryLo <
        (989728731 / 1000000000 : ℝ) := by
    rw [boundaryCapitalScale_rewrite boundaryLo
      (by norm_num [boundaryLo])]
    apply (div_lt_iff₀ hden).2
    dsimp [continuationReturn,
      ProposedStationaryRealScale.liquidationValue,
      ProposedStationaryRealScale.capitalPrice, boundaryLo]
    linarith only [huLlo]
  have hRmem : boundaryLo ∈ boundaryInterval :=
    ⟨le_refl _, le_of_lt boundaryLo_lt_boundaryHi⟩
  have hspos : 0 < boundaryCapitalScale boundaryLo :=
    (boundary_scale_and_investment_domain hRmem).1
  have hfour :
      4 * boundaryCapitalScale boundaryLo <
        4 * (989728731 / 1000000000 : ℝ) := by
    nlinarith only [hsHi]
  have hinv :
      (1 : ℝ) / (4 * (989728731 / 1000000000 : ℝ)) <
        1 / (4 * boundaryCapitalScale boundaryLo) :=
    one_div_lt_one_div_of_lt (mul_pos (by norm_num) hspos) hfour
  have hfactor :
      (3532417 / 100000000 : ℝ) <
        (41 / 80 : ℝ) +
          1 / (4 * boundaryCapitalScale boundaryLo) -
          (4719 / 6400 : ℝ) * boundaryCapitalScale boundaryLo := by
    have hrat :
        (3532417 / 100000000 : ℝ) <
          (41 / 80 : ℝ) +
            1 / (4 * (989728731 / 1000000000 : ℝ)) -
            (4719 / 6400 : ℝ) * (989728731 / 1000000000 : ℝ) := by
      norm_num
    linarith only [hinv, hsHi, hrat]
  have hKlo :
      (7554294 / 100000 : ℝ) <
        ProposedStationaryRealScale.average
          ProposedStationaryRealScale.capitalScale := by
    rcases boundary_source_capital_scales_sharp_boxes with
      ⟨⟨hHlo, _⟩, ⟨hLlo, _⟩⟩
    unfold ProposedStationaryRealScale.average
    linarith only [hHlo, hLlo]
  have hKpos : 0 <
      ProposedStationaryRealScale.average
        ProposedStationaryRealScale.capitalScale :=
    ProposedStationaryRealScale.aggregate_scales_pos.1
  unfold normalizedCapitalCost
  calc
    (266849 / 100000 : ℝ) <
        (7554294 / 100000 : ℝ) *
          (3532417 / 100000000 : ℝ) := by norm_num
    _ < ProposedStationaryRealScale.average
          ProposedStationaryRealScale.capitalScale *
            (3532417 / 100000000 : ℝ) :=
      mul_lt_mul_of_pos_right hKlo (by norm_num)
    _ < _ := mul_lt_mul_of_pos_left hfactor hKpos

/-- Three endpoints remain unverified from source: two fifteenth-root
output boxes and one lower-end worker consumption inequality. -/
structure BoundaryRemainingThreeBoxes : Prop where
  Ylo_upper : normalizedOutput boundaryLo < 1327678 / 100000
  CWlo_lower : 793630 / 100000 < normalizedWorkerConsumption boundaryLo
  Yhi_lower : 1340498 / 100000 < normalizedOutput boundaryHi

theorem boundary_four_boxes_from_three
    (h : BoundaryRemainingThreeBoxes) : BoundaryRemainingFourBoxes := by
  exact ⟨h.Ylo_upper, h.CWlo_lower,
    boundary_capital_cost_lo_box_from_source, h.Yhi_lower⟩

/-- Literal scalar rate uniqueness plus the reduced 33-row prefix;
no infinite-horizon competitive equilibrium is implied. -/
theorem boundary_unique_reduced_prefix_rate_of_three
    (G : ℝ) (h : BoundaryRemainingThreeBoxes) :
    ∃! R : ℝ,
      boundaryLo ≤ R ∧ R ≤ boundaryHi ∧
      boundaryResourceResidual R = 0 ∧
      ∀ branch : LocalPrefixBranch,
        LocalReducedPrefixEquationsHold branch
          (boundaryPrimitives G R)
          (boundaryInitialState G R)
          (boundaryCoordinates R) .dateOne .recurrent boundaryTail := by
  exact boundary_unique_reduced_prefix_rate_of_four G
    (boundary_four_boxes_from_three h)

/-- A strictly positive lower SOURCE enclosure of stationary worker
consumption after wage^5 normalization. Each input remains tied to
the original bank and firm primitives, including the common loan rate. -/
theorem boundary_worker_consumption_scale_lower :
    (8038062 / 1000000 : ℝ) <
      ProposedStationaryRealScale.workerConsumptionScale := by
  rcases boundary_source_user_cost_sharp_boxes with
    ⟨⟨huHlo, _⟩, ⟨huLlo, _⟩⟩
  rcases boundary_source_capital_scales_sharp_boxes with
    ⟨⟨hkHlo, _⟩, ⟨hkLlo, _⟩⟩
  rcases boundary_source_loan_rate_sharp_box with ⟨hrlo, hrhi⟩
  have hkHpos := ProposedStationaryRealScale.capitalScale_pos .H
  have hkLpos := ProposedStationaryRealScale.capitalScale_pos .L
  have hprodH :
      (63166370 / 1000000000 : ℝ) * (5677035 / 100000 : ℝ) <
        ProposedStationaryRealScale.userCost .H *
          ProposedStationaryRealScale.capitalScale .H := by
    calc
      _ < (63166370 / 1000000000 : ℝ) *
            ProposedStationaryRealScale.capitalScale .H :=
        mul_lt_mul_of_pos_left hkHlo (by norm_num)
      _ < _ := mul_lt_mul_of_pos_right huHlo hkHpos
  have hprodL :
      (55943655 / 1000000000 : ℝ) * (9431553 / 100000 : ℝ) <
        ProposedStationaryRealScale.userCost .L *
          ProposedStationaryRealScale.capitalScale .L := by
    calc
      _ < (55943655 / 1000000000 : ℝ) *
            ProposedStationaryRealScale.capitalScale .L :=
        mul_lt_mul_of_pos_left hkLlo (by norm_num)
      _ < _ := mul_lt_mul_of_pos_right huLlo hkLpos
  have hYformula :
      ProposedStationaryRealScale.outputScale =
        (3 / 2 : ℝ) *
          (ProposedStationaryRealScale.userCost .H *
              ProposedStationaryRealScale.capitalScale .H +
            ProposedStationaryRealScale.userCost .L *
              ProposedStationaryRealScale.capitalScale .L) := by
    unfold ProposedStationaryRealScale.outputScale
      ProposedStationaryRealScale.average
    ring
  have hYlo :
      (1329349 / 100000 : ℝ) <
        ProposedStationaryRealScale.outputScale := by
    rw [hYformula]
    have hsum := add_lt_add hprodH hprodL
    linarith only [hsum]
  have hKlo :
      (7554294 / 100000 : ℝ) <
        ProposedStationaryRealScale.average
          ProposedStationaryRealScale.capitalScale := by
    unfold ProposedStationaryRealScale.average
    linarith only [hkHlo, hkLlo]
  have hrpos : 0 < ProposedStationaryBank.loanRate :=
    ProposedStationaryRealScale.loanRate_pos
  have hcreditScaled :
      ProposedStationaryRealScale.creditScale *
          ProposedStationaryBank.loanRate =
        ((3 / 20 : ℝ) * (3159 / 3200 : ℝ) *
            ProposedStationaryRealScale.capitalScale .H +
          (2 / 5 : ℝ) * (3159 / 3200 : ℝ) *
            ProposedStationaryRealScale.capitalScale .L) / 2 := by
    unfold ProposedStationaryRealScale.creditScale
      ProposedStationaryRealScale.average
      ProposedStationaryRealScale.pledgeability
      ProposedStationaryRealScale.liquidationValue
      ProposedStationaryRealScale.capitalPrice
    field_simp [ne_of_gt hrpos] <;> ring
  have hcreditScaledLower :
      (2255292 / 100000 : ℝ) *
          (101204823808 / 100000000000 : ℝ) <
        ((3 / 20 : ℝ) * (3159 / 3200 : ℝ) *
            ProposedStationaryRealScale.capitalScale .H +
          (2 / 5 : ℝ) * (3159 / 3200 : ℝ) *
            ProposedStationaryRealScale.capitalScale .L) / 2 := by
    linarith only [hkHlo, hkLlo]
  have hcreditLower :
      (2255292 / 100000 : ℝ) <
        ProposedStationaryRealScale.creditScale := by
    by_contra hn
    have hle :
        ProposedStationaryRealScale.creditScale ≤
          (2255292 / 100000 : ℝ) := le_of_not_gt hn
    have hm := mul_le_mul_of_nonneg_right hle hrpos.le
    rw [hcreditScaled] at hm
    linarith only [hm, hrhi, hcreditScaledLower]
  have hloanAboveOne : 0 < ProposedStationaryBank.loanRate - 1 :=
    sub_pos.mpr ProposedStationaryRealScale.loanRate_gt_one
  have hcreditProductLower :
      ((101204823607 / 100000000000 : ℝ) - 1) *
          (2255292 / 100000 : ℝ) <
        (ProposedStationaryBank.loanRate - 1) *
          ProposedStationaryRealScale.creditScale := by
    calc
      _ < (ProposedStationaryBank.loanRate - 1) *
            (2255292 / 100000 : ℝ) :=
        mul_lt_mul_of_pos_right (by linarith only [hrlo]) (by norm_num)
      _ < _ := mul_lt_mul_of_pos_left hcreditLower hloanAboveOne
  have hrat :
      (8038062 / 1000000 : ℝ) <
        (7 / 12 : ℝ) * (1329349 / 100000 : ℝ) +
          (7554294 / 100000 : ℝ) / 6400 +
          ((101204823607 / 100000000000 : ℝ) - 1) *
            (2255292 / 100000 : ℝ) := by
    norm_num
  unfold ProposedStationaryRealScale.workerConsumptionScale
  linarith only [hYlo, hKlo, hcreditProductLower, hrat]

/-- Strict rational upper enclosure for the lower boundary's SOURCE
deposit rate, derived from the OTC slope micro-boxes and positive
settlement denominators. -/
theorem boundary_deposit_rate_lo_source_upper :
    boundaryDepositRate boundaryLo <
      (1023052874 / 1000000000 : ℝ) := by
  rcases boundary_source_slope_rational_micro_boxes with
    ⟨⟨hmlo, hmhi⟩, ⟨hglo, hghi⟩⟩
  have hRmem : boundaryLo ∈ boundaryInterval :=
    ⟨le_refl _, le_of_lt boundaryLo_lt_boundaryHi⟩
  have hrrpos : 0 < boundaryReserveRate boundaryLo :=
    (boundary_rate_domain hRmem).2
  have hpaypos : 0 < boundaryPaymentTerm := by
    unfold boundaryPaymentTerm
    linarith only [hglo]
  have hnum :
      boundaryReserveRate boundaryLo +
        (9 / 10 : ℝ) * ProposedStationaryBank.meanSlope +
        (1 / 10 : ℝ) * boundaryPaymentTerm <
      (1024285357182 / 1000000000000 : ℝ) := by
    unfold boundaryReserveRate boundaryPaymentTerm boundaryLo
    linarith only [hmlo, hmhi, hghi]
  have hfrac :
      (1204711925 / 1000000000000 : ℝ) <
        boundaryPaymentTerm / boundaryReserveRate boundaryLo := by
    apply (lt_div_iff₀ hrrpos).2
    unfold boundaryPaymentTerm boundaryReserveRate boundaryLo
    linarith only [hmlo, hglo]
  have hdenlo :
      (1001204711925 / 1000000000000 : ℝ) <
        1 + boundaryPaymentTerm / boundaryReserveRate boundaryLo := by
    linarith only [hfrac]
  have hdenpos :
      0 < 1 + boundaryPaymentTerm / boundaryReserveRate boundaryLo := by
    have hdiv := div_pos hpaypos hrrpos
    linarith only [hdiv]
  change (boundaryReserveRate boundaryLo +
      (9 / 10 : ℝ) * ProposedStationaryBank.meanSlope +
      (1 / 10 : ℝ) * boundaryPaymentTerm) /
    (1 + boundaryPaymentTerm / boundaryReserveRate boundaryLo) <
      (1023052874 / 1000000000 : ℝ)
  apply (div_lt_iff₀ hdenpos).2
  calc
    boundaryReserveRate boundaryLo +
        (9 / 10 : ℝ) * ProposedStationaryBank.meanSlope +
        (1 / 10 : ℝ) * boundaryPaymentTerm <
      (1024285357182 / 1000000000000 : ℝ) := hnum
    _ < (1023052874 / 1000000000 : ℝ) *
          (1001204711925 / 1000000000000 : ℝ) := by norm_num
    _ < (1023052874 / 1000000000 : ℝ) *
          (1 + boundaryPaymentTerm / boundaryReserveRate boundaryLo) :=
      mul_lt_mul_of_pos_left hdenlo (by norm_num)

/-- Strict SOURCE proof of the *lower* worker-consumption endpoint:
not a fitted resource residual or a postulated component box. -/
theorem boundary_worker_lo_box_from_source :
    (793630 / 100000 : ℝ) <
      normalizedWorkerConsumption boundaryLo := by
  have hw := boundary_worker_consumption_scale_lower
  have hrd := boundary_deposit_rate_lo_source_upper
  have hRmem : boundaryLo ∈ boundaryInterval :=
    ⟨le_refl _, le_of_lt boundaryLo_lt_boundaryHi⟩
  have hden : 0 < (99 / 100 : ℝ) * boundaryDepositRate boundaryLo :=
    mul_pos (by norm_num) (boundaryDepositRate_pos hRmem)
  unfold normalizedWorkerConsumption
  apply (lt_div_iff₀ hden).2
  have hrate :
      (99 / 100 : ℝ) * boundaryDepositRate boundaryLo <
        (99 / 100 : ℝ) * (1023052874 / 1000000000 : ℝ) :=
    mul_lt_mul_of_pos_left hrd (by norm_num)
  have hprod :
      (793630 / 100000 : ℝ) *
          ((99 / 100 : ℝ) * boundaryDepositRate boundaryLo) <
        (793630 / 100000 : ℝ) *
          ((99 / 100 : ℝ) * (1023052874 / 1000000000 : ℝ)) :=
    mul_lt_mul_of_pos_left hrate (by norm_num)
  calc
    _ < (793630 / 100000 : ℝ) *
        ((99 / 100 : ℝ) * (1023052874 / 1000000000 : ℝ)) := hprod
    _ < (8038062 / 1000000 : ℝ) := by norm_num
    _ < _ := hw

/-- Only the two SOURCE output root enclosures remain for certifying
the scalar resource residual's opposite signs. -/
structure BoundaryRemainingTwoBoxes : Prop where
  Ylo_upper : normalizedOutput boundaryLo < 1327678 / 100000
  Yhi_lower : 1340498 / 100000 < normalizedOutput boundaryHi

theorem boundary_three_boxes_from_two
    (h : BoundaryRemainingTwoBoxes) : BoundaryRemainingThreeBoxes := by
  exact ⟨h.Ylo_upper, boundary_worker_lo_box_from_source, h.Yhi_lower⟩

/-- Conditional uniqueness of the scalar SOURCE rate and 33-row
reduced system. The final two output boxes remain explicit premises. -/
theorem boundary_unique_reduced_prefix_rate_of_two
    (G : ℝ) (h : BoundaryRemainingTwoBoxes) :
    ∃! R : ℝ,
      boundaryLo ≤ R ∧ R ≤ boundaryHi ∧
      boundaryResourceResidual R = 0 ∧
      ∀ branch : LocalPrefixBranch,
        LocalReducedPrefixEquationsHold branch
          (boundaryPrimitives G R)
          (boundaryInitialState G R)
          (boundaryCoordinates R) .dateOne .recurrent boundaryTail := by
  exact boundary_unique_reduced_prefix_rate_of_three G
    (boundary_three_boxes_from_two h)

/-- Sharp stationary SOURCE output scale from the two firm cost and
capital enclosures. Both inequalities are consequences of the common
bank loan rate and the technology/pledgeability primitives. -/
theorem boundary_source_output_scale_sharp_box :
    (13293498 / 1000000 : ℝ) <
      ProposedStationaryRealScale.outputScale ∧
    ProposedStationaryRealScale.outputScale <
      (13293504 / 1000000 : ℝ) := by
  rcases boundary_source_user_cost_sharp_boxes with
    ⟨⟨huHlo, huHhi⟩, ⟨huLlo, huLhi⟩⟩
  rcases boundary_source_capital_scales_sharp_boxes with
    ⟨⟨hkHlo, hkHhi⟩, ⟨hkLlo, hkLhi⟩⟩
  have huHpos := ProposedStationaryRealScale.userCost_pos .H
  have huLpos := ProposedStationaryRealScale.userCost_pos .L
  have hkHpos := ProposedStationaryRealScale.capitalScale_pos .H
  have hkLpos := ProposedStationaryRealScale.capitalScale_pos .L
  have hprodHlo :
      (63166370 / 1000000000 : ℝ) * (5677035 / 100000 : ℝ) <
        ProposedStationaryRealScale.userCost .H *
          ProposedStationaryRealScale.capitalScale .H := by
    calc
      _ < (63166370 / 1000000000 : ℝ) *
            ProposedStationaryRealScale.capitalScale .H :=
        mul_lt_mul_of_pos_left hkHlo (by norm_num)
      _ < _ := mul_lt_mul_of_pos_right huHlo hkHpos
  have hprodLlo :
      (55943655 / 1000000000 : ℝ) * (9431553 / 100000 : ℝ) <
        ProposedStationaryRealScale.userCost .L *
          ProposedStationaryRealScale.capitalScale .L := by
    calc
      _ < (55943655 / 1000000000 : ℝ) *
            ProposedStationaryRealScale.capitalScale .L :=
        mul_lt_mul_of_pos_left hkLlo (by norm_num)
      _ < _ := mul_lt_mul_of_pos_right huLlo hkLpos
  have hprodHhi :
      ProposedStationaryRealScale.userCost .H *
        ProposedStationaryRealScale.capitalScale .H <
        (63166372 / 1000000000 : ℝ) * (5677037 / 100000 : ℝ) := by
    calc
      _ < (63166372 / 1000000000 : ℝ) *
            ProposedStationaryRealScale.capitalScale .H :=
        mul_lt_mul_of_pos_right huHhi hkHpos
      _ < _ := mul_lt_mul_of_pos_left hkHhi (by norm_num)
  have hprodLhi :
      ProposedStationaryRealScale.userCost .L *
        ProposedStationaryRealScale.capitalScale .L <
        (55943657 / 1000000000 : ℝ) * (9431556 / 100000 : ℝ) := by
    calc
      _ < (55943657 / 1000000000 : ℝ) *
            ProposedStationaryRealScale.capitalScale .L :=
        mul_lt_mul_of_pos_right huLhi hkLpos
      _ < _ := mul_lt_mul_of_pos_left hkLhi (by norm_num)
  have hYformula :
      ProposedStationaryRealScale.outputScale =
        (3 / 2 : ℝ) *
          (ProposedStationaryRealScale.userCost .H *
              ProposedStationaryRealScale.capitalScale .H +
            ProposedStationaryRealScale.userCost .L *
              ProposedStationaryRealScale.capitalScale .L) := by
    unfold ProposedStationaryRealScale.outputScale
      ProposedStationaryRealScale.average
    ring
  rw [hYformula]
  constructor
  · have hsum := add_lt_add hprodHlo hprodLlo
    linarith only [hsum]
  · have hsum := add_lt_add hprodHhi hprodLhi
    linarith only [hsum]

/-- Fifteenth-root upper box at the lower SOURCE bracket endpoint.
The root is bounded by an exact fifteenth-power comparison, not by
approximating Real.rpow or postulating an endpoint sign. -/
theorem boundary_output_lo_box_from_source :
    normalizedOutput boundaryLo < (1327678 / 100000 : ℝ) := by
  rcases boundary_source_output_scale_sharp_box with ⟨_, hYhi⟩
  rcases boundary_source_user_cost_sharp_boxes with
    ⟨_, ⟨huLlo, _⟩⟩
  have hRmem : boundaryLo ∈ boundaryInterval :=
    ⟨le_refl _, le_of_lt boundaryLo_lt_boundaryHi⟩
  have hspos : 0 < boundaryCapitalScale boundaryLo :=
    (boundary_scale_and_investment_domain hRmem).1
  have hrdpos : 0 < boundaryDepositRate boundaryLo :=
    boundaryDepositRate_pos hRmem
  have hden :
      0 < 2 * continuationReturn .L -
        (41 / 40 : ℝ) * boundaryLo := by
    dsimp [continuationReturn,
      ProposedStationaryRealScale.liquidationValue,
      ProposedStationaryRealScale.capitalPrice, boundaryLo]
    linarith only [huLlo]
  have hsHi :
      boundaryCapitalScale boundaryLo <
        (989728731 / 1000000000 : ℝ) := by
    rw [boundaryCapitalScale_rewrite boundaryLo
      (by norm_num [boundaryLo])]
    apply (div_lt_iff₀ hden).2
    dsimp [continuationReturn,
      ProposedStationaryRealScale.liquidationValue,
      ProposedStationaryRealScale.capitalPrice, boundaryLo]
    linarith only [huLlo]
  have hrdHi := boundary_deposit_rate_lo_source_upper
  have hdepositScaled :
      (99 / 100 : ℝ) * boundaryDepositRate boundaryLo <
        (99 / 100 : ℝ) * (1023052874 / 1000000000 : ℝ) :=
    mul_lt_mul_of_pos_left hrdHi (by norm_num)
  have hspow :
      boundaryCapitalScale boundaryLo ^ (8 : ℕ) <
        (989728731 / 1000000000 : ℝ) ^ (8 : ℕ) := by
    gcongr
  have hdpow :
      ((99 / 100 : ℝ) * boundaryDepositRate boundaryLo) ^ (5 : ℕ) <
        ((99 / 100 : ℝ) *
          (1023052874 / 1000000000 : ℝ)) ^ (5 : ℕ) := by
    gcongr
  let x : ℝ :=
    boundaryCapitalScale boundaryLo ^ (8 : ℕ) *
      ((99 / 100 : ℝ) * boundaryDepositRate boundaryLo) ^ (5 : ℕ)
  have hx : 0 ≤ x := by
    dsimp [x]
    exact mul_nonneg (pow_nonneg hspos.le _)
      (pow_nonneg (mul_nonneg (by norm_num) hrdpos.le) _)
  have hpoly :
      x ≤ (998741401 / 1000000000 : ℝ) ^ (15 : ℕ) := by
    dsimp [x]
    have hfactorPos :
        0 < ((99 / 100 : ℝ) * boundaryDepositRate boundaryLo) ^
          (5 : ℕ) :=
      pow_pos (mul_pos (by norm_num) hrdpos) (5 : ℕ)
    have hm1 :
        boundaryCapitalScale boundaryLo ^ (8 : ℕ) *
            ((99 / 100 : ℝ) * boundaryDepositRate boundaryLo) ^ (5 : ℕ) <
          (989728731 / 1000000000 : ℝ) ^ (8 : ℕ) *
            ((99 / 100 : ℝ) * boundaryDepositRate boundaryLo) ^ (5 : ℕ) :=
      mul_lt_mul_of_pos_right hspow hfactorPos
    have hm2 :
        (989728731 / 1000000000 : ℝ) ^ (8 : ℕ) *
            ((99 / 100 : ℝ) * boundaryDepositRate boundaryLo) ^ (5 : ℕ) <
          (989728731 / 1000000000 : ℝ) ^ (8 : ℕ) *
            ((99 / 100 : ℝ) *
              (1023052874 / 1000000000 : ℝ)) ^ (5 : ℕ) :=
      mul_lt_mul_of_pos_left hdpow
        (by norm_num :
          (0 : ℝ) < (989728731 / 1000000000 : ℝ) ^ (8 : ℕ))
    exact (lt_trans (lt_trans hm1 hm2) (by norm_num)).le
  have hroot :
      x ^ (1 / 15 : ℝ) ≤ (998741401 / 1000000000 : ℝ) :=
    (fifteenth_root_between 0
      (998741401 / 1000000000 : ℝ) x
      (by norm_num) (by norm_num) hx
      (by simpa using hx) hpoly).2
  have hYpos : 0 < ProposedStationaryRealScale.outputScale :=
    ProposedStationaryRealScale.aggregate_scales_pos.2.1
  change ProposedStationaryRealScale.outputScale *
    x ^ (1 / 15 : ℝ) < (1327678 / 100000 : ℝ)
  calc
    _ ≤ ProposedStationaryRealScale.outputScale *
          (998741401 / 1000000000 : ℝ) :=
      mul_le_mul_of_nonneg_left hroot hYpos.le
    _ < (13293504 / 1000000 : ℝ) *
          (998741401 / 1000000000 : ℝ) :=
      mul_lt_mul_of_pos_right hYhi (by norm_num)
    _ < (1327678 / 100000 : ℝ) := by norm_num

/-- Fifteenth-root lower box at the upper SOURCE bracket endpoint;
uses the exact production power and the previously source-derived
deposit-remuneration and capital-scale enclosures. -/
theorem boundary_output_hi_box_from_source :
    (1340498 / 100000 : ℝ) < normalizedOutput boundaryHi := by
  rcases boundary_source_output_scale_sharp_box with ⟨hYlo, _⟩
  rcases boundary_source_user_cost_sharp_boxes with
    ⟨_, ⟨huLlo, huLhi⟩⟩
  have hRmem : boundaryHi ∈ boundaryInterval :=
    ⟨le_of_lt boundaryLo_lt_boundaryHi, le_refl _⟩
  have hspos : 0 < boundaryCapitalScale boundaryHi :=
    (boundary_scale_and_investment_domain hRmem).1
  have hrdpos : 0 < boundaryDepositRate boundaryHi :=
    boundaryDepositRate_pos hRmem
  have hden :
      0 < 2 * continuationReturn .L -
        (41 / 40 : ℝ) * boundaryHi := by
    dsimp [continuationReturn,
      ProposedStationaryRealScale.liquidationValue,
      ProposedStationaryRealScale.capitalPrice, boundaryHi]
    linarith only [huLlo]
  have hsLo :
      (1003439781 / 1000000000 : ℝ) <
        boundaryCapitalScale boundaryHi := by
    rw [boundaryCapitalScale_rewrite boundaryHi
      (by norm_num [boundaryHi])]
    apply (lt_div_iff₀ hden).2
    dsimp [continuationReturn,
      ProposedStationaryRealScale.liquidationValue,
      ProposedStationaryRealScale.capitalPrice, boundaryHi]
    linarith only [huLhi]
  have hrdLo := boundary_deposit_rate_hi_source_lower
  have hdepositScaled :
      (99 / 100 : ℝ) * (10300529 / 10000000 : ℝ) <
        (99 / 100 : ℝ) * boundaryDepositRate boundaryHi :=
    mul_lt_mul_of_pos_left hrdLo (by norm_num)
  have hspow :
      (1003439781 / 1000000000 : ℝ) ^ (8 : ℕ) <
        boundaryCapitalScale boundaryHi ^ (8 : ℕ) := by
    gcongr
  have hdpow :
      ((99 / 100 : ℝ) *
        (10300529 / 10000000 : ℝ)) ^ (5 : ℕ) <
        ((99 / 100 : ℝ) * boundaryDepositRate boundaryHi) ^ (5 : ℕ) := by
    gcongr
  let x : ℝ :=
    boundaryCapitalScale boundaryHi ^ (8 : ℕ) *
      ((99 / 100 : ℝ) * boundaryDepositRate boundaryHi) ^ (5 : ℕ)
  have hx : 0 ≤ x := by
    dsimp [x]
    exact mul_nonneg (pow_nonneg hspos.le _)
      (pow_nonneg (mul_nonneg (by norm_num) hrdpos.le) _)
  have hpoly :
      (1008386313 / 1000000000 : ℝ) ^ (15 : ℕ) ≤ x := by
    dsimp [x]
    have hm1 :=
      mul_lt_mul_of_pos_right hspow
        (by norm_num :
          (0 : ℝ) <
            ((99 / 100 : ℝ) * (10300529 / 10000000 : ℝ)) ^ (5 : ℕ))
    have hm2 :=
      mul_lt_mul_of_pos_left hdpow
        (pow_pos hspos (8 : ℕ))
    exact (lt_trans (by norm_num) (lt_trans hm1 hm2)).le
  have hroot :
      (1008386313 / 1000000000 : ℝ) ≤
        x ^ (1 / 15 : ℝ) := by
    have h := Real.rpow_le_rpow
      (pow_nonneg (by norm_num :
        (0 : ℝ) ≤ (1008386313 / 1000000000 : ℝ)) (15 : ℕ))
      hpoly (by norm_num : (0 : ℝ) ≤ 1 / 15)
    calc
      (1008386313 / 1000000000 : ℝ) =
          ((1008386313 / 1000000000 : ℝ) ^ (15 : ℕ)) ^
            (1 / 15 : ℝ) := by
        simpa only [one_div] using
          (Real.pow_rpow_inv_natCast
            (by norm_num :
              (0 : ℝ) ≤ (1008386313 / 1000000000 : ℝ))
            (by norm_num : (15 : ℕ) ≠ 0)).symm
      _ ≤ x ^ (1 / 15 : ℝ) := h
  have hYpos : 0 < ProposedStationaryRealScale.outputScale :=
    ProposedStationaryRealScale.aggregate_scales_pos.2.1
  change (1340498 / 100000 : ℝ) <
    ProposedStationaryRealScale.outputScale * x ^ (1 / 15 : ℝ)
  calc
    (1340498 / 100000 : ℝ) <
        (13293498 / 1000000 : ℝ) *
          (1008386313 / 1000000000 : ℝ) := by norm_num
    _ < ProposedStationaryRealScale.outputScale *
          (1008386313 / 1000000000 : ℝ) :=
      mul_lt_mul_of_pos_right hYlo (by norm_num)
    _ ≤ _ := mul_le_mul_of_nonneg_left hroot hYpos.le

/-- All ten source endpoint inequalities are now consequences of the
literal bank/firm/worker/production equations. This statement is
separate from the equilibrium proposition of the paper. -/
theorem boundary_component_boxes_from_source : BoundaryComponentBoxes := by
  have htwo : BoundaryRemainingTwoBoxes :=
    ⟨boundary_output_lo_box_from_source,
      boundary_output_hi_box_from_source⟩
  have hthree := boundary_three_boxes_from_two htwo
  have hfour := boundary_four_boxes_from_three hthree
  have hfive := boundary_five_boxes_from_four hfour
  have hsix := boundary_six_boxes_from_five hfive
  have height := boundary_eight_boxes_from_six hsix
  exact boundary_component_boxes_from_eight height

/-- An unconditional SOURCE scalar frontier rate has a unique root on
the bracket with all 33 reduced-prefix identities. Not a proof of
full infinite-horizon competitive equilibrium or branch selection. -/
theorem boundary_unique_reduced_prefix_rate_from_source
    (G : ℝ) :
    ∃! R : ℝ,
      boundaryLo ≤ R ∧ R ≤ boundaryHi ∧
      boundaryResourceResidual R = 0 ∧
      ∀ branch : LocalPrefixBranch,
        LocalReducedPrefixEquationsHold branch
          (boundaryPrimitives G R)
          (boundaryInitialState G R)
          (boundaryCoordinates R) .dateOne .recurrent boundaryTail := by
  exact boundary_unique_reduced_prefix_rate_of_two G
    ⟨boundary_output_lo_box_from_source,
      boundary_output_hi_box_from_source⟩

/-- Named mathematical SOURCE boundary rate for use by subsequent full
allocation construction. This is the scalar resource root, not a
complete intervention equilibrium object. -/
noncomputable def boundarySourceRate : ℝ :=
  boundaryRoot boundary_analyticPackage
    (endpointSigns_of_boxes boundary_component_boxes_from_source)

/-- The named rate is bracketed and solves the *source* resource
equation, not merely a normalized numerical surrogate. -/
theorem boundarySourceRate_spec :
    boundaryLo ≤ boundarySourceRate ∧
    boundarySourceRate ≤ boundaryHi ∧
    boundaryResourceResidual boundarySourceRate = 0 := by
  simpa only [boundarySourceRate] using
    (boundaryRoot_spec boundary_analyticPackage
      (endpointSigns_of_boxes boundary_component_boxes_from_source))

/-- All 33 reduced equations hold at the named SOURCE root in either
formal prefix branch. A full history-indexed allocation, individual
optimality and terminal checks must still be supplied. -/
theorem boundarySourceRate_reduced_prefix
    (G : ℝ) (branch : LocalPrefixBranch) :
    LocalReducedPrefixEquationsHold branch
      (boundaryPrimitives G boundarySourceRate)
      (boundaryInitialState G boundarySourceRate)
      (boundaryCoordinates boundarySourceRate)
      .dateOne .recurrent boundaryTail := by
  simpa only [boundarySourceRate] using
    (boundary_reduced_prefix_from_endpoint_boxes
      G boundary_component_boxes_from_source branch)


/-- Economic admissibility of the named SOURCE frontier rate.
All statements concern the explicit boundary date-zero construction,
not an unconstructed infinite-horizon competitive allocation. -/
theorem boundarySourceRate_positiveRealDomain :
    0 < boundarySourceRate ∧
    0 < boundaryReserveRate boundarySourceRate ∧
    0 < boundaryDepositRate boundarySourceRate ∧
    0 < boundaryCapitalScale boundarySourceRate ∧
    boundaryCapitalScale boundarySourceRate < (40 / 39 : ℝ) ∧
    0 < boundaryInvestment boundarySourceRate := by
  have hmem : boundarySourceRate ∈ boundaryInterval :=
    ⟨boundarySourceRate_spec.1, boundarySourceRate_spec.2.1⟩
  rcases boundary_rate_domain hmem with ⟨hr, hrr⟩
  rcases boundary_scale_and_investment_domain hmem with ⟨hs, hbound, hi⟩
  exact ⟨hr, hrr, boundaryDepositRate_pos hmem,
    hs, hbound, hi⟩

/-- Named-root SOURCE bank stocks and the reserve/deposit ratio are
strictly admissible at date zero. This proves positive bank balance
components but does not discharge bank portfolio optimality or TVCs. -/
theorem boundarySourceRate_bankDomain :
    0 < boundaryBankEquity boundarySourceRate ∧
    0 < boundaryBankDeposits boundarySourceRate ∧
    0 < boundaryReservesPre boundarySourceRate ∧
    0 < boundaryReserveDepositRatio boundarySourceRate ∧
    boundaryReserveDepositRatio boundarySourceRate < 1 ∧
    boundaryBankEquity boundarySourceRate <
      boundaryBankLoans boundarySourceRate := by
  have hmem : boundarySourceRate ∈ boundaryInterval :=
    ⟨boundarySourceRate_spec.1, boundarySourceRate_spec.2.1⟩
  rcases boundaryBankScale_pos hmem with ⟨he, hd, hm⟩
  rcases boundaryReserveDepositRatio_bounds hmem with ⟨hpos, hlt⟩
  exact ⟨he, hd, hm, hpos, hlt,
    boundaryBankLoans_gt_equity hmem⟩


/-- The named SOURCE rate separates the financially constrained firm
from the boundary firm: H has strictly valuable collateral and
L has binding collateral but zero shadow value. Neither classification
is an assertion about nearby perturbed equilibria. -/
theorem boundarySourceRate_firmRegime :
    ValuableCollateralLoan boundarySourceRate
      (ProposedStationaryRealScale.pledgeability .H *
        ProposedStationaryRealScale.liquidationValue)
      (ProposedStationaryRealScale.capital .H)
      (boundarySDF boundarySourceRate .H)
      (ProposedStationaryRealScale.firmFace .H)
      (boundaryDual boundarySourceRate .H) ∧
    ActiveCollateralZeroDual boundarySourceRate
      (ProposedStationaryRealScale.pledgeability .L *
        ProposedStationaryRealScale.liquidationValue)
      (ProposedStationaryRealScale.capital .L)
      (boundarySDF boundarySourceRate .L)
      (ProposedStationaryRealScale.firmFace .L)
      (boundaryDual boundarySourceRate .L) := by
  have hr : 0 < boundarySourceRate :=
    boundarySourceRate_positiveRealDomain.1
  exact ⟨boundary_H_valuable boundarySourceRate hr,
    boundary_L_active_zero_dual boundarySourceRate hr⟩

/-- Strict firm consumption and the two collateral shadow values
at the SOURCE boundary date zero; no claim about firm optimality at
all later dates follows from these local signs. -/
theorem boundarySourceRate_firmSigns :
    0 < boundaryConsumption boundarySourceRate .H ∧
    0 < boundaryConsumption boundarySourceRate .L ∧
    0 < boundaryDual boundarySourceRate .H ∧
    boundaryDual boundarySourceRate .L = 0 := by
  have hr : 0 < boundarySourceRate :=
    boundarySourceRate_positiveRealDomain.1
  exact ⟨boundaryConsumption_pos boundarySourceRate hr .H,
    boundaryConsumption_pos boundarySourceRate hr .L,
    boundaryDual_H_pos boundarySourceRate hr,
    boundaryDual_L boundarySourceRate hr⟩


/-- The initial SOURCE worker is positive and satisfies the *literal*
static labor-supply condition at the named frontier rate. This is
only a date-zero first-order condition, not an infinite household
optimality certificate. -/
theorem boundarySourceRate_workerLabor :
    0 < boundaryWorkerConsumption boundarySourceRate ∧
    0 < boundaryWage boundarySourceRate ∧
    boundaryWage boundarySourceRate =
      boundaryWorkerConsumption boundarySourceRate *
        boundaryAggregateLabor boundarySourceRate := by
  have hmem : boundarySourceRate ∈ boundaryInterval :=
    ⟨boundarySourceRate_spec.1, boundarySourceRate_spec.2.1⟩
  exact ⟨boundaryWorkerConsumption_pos hmem,
    boundaryWage_pos hmem,
    boundary_worker_labor_equation hmem⟩


/-- The unique source frontier root is certified for the exact paper
ExactRootOn interface, with the literal economic resource residual.
This closes the scalar carrier obligation, not full equilibrium. -/
theorem boundarySourceRate_exactRootOn :
    ExactRootOn boundaryResourceResidual boundaryLo boundaryHi := by
  exact boundary_exactRootOn boundary_analyticPackage
    (endpointSigns_of_boxes boundary_component_boxes_from_source)

/-- Any root of the literal source residual inside the interval equals
the same SOURCE rate used to construct the 33 reduced prefix rows. -/
theorem boundarySourceRate_unique_of_source_root
    (R : ℝ) (hlo : boundaryLo ≤ R) (hhi : R ≤ boundaryHi)
    (hzero : boundaryResourceResidual R = 0) :
    R = boundarySourceRate := by
  obtain ⟨root, _hroot, huniq⟩ := boundarySourceRate_exactRootOn
  have hR : R = root := huniq R ⟨hlo, hhi, hzero⟩
  have hStar : boundarySourceRate = root :=
    huniq boundarySourceRate boundarySourceRate_spec
  exact hR.trans hStar.symm

/-- A paper-level boundary witness, IF independently constructed for the
same source primitives and inherited state, discharges the original paper
Proposition 4.1 interface with Phi fixed to the resource residual. Its
existence and global optimality remain OPEN obligations. -/
theorem boundary_paper_spec_of_source_full_witness
    (G : ℝ) (X : Allocation LocalBridgePhase)
    (hX : BoundaryEquilibriumCandidate
      (boundaryPrimitives G boundarySourceRate)
      (boundaryInitialState G boundarySourceRate) X) :
    boundaryEquilibriumSpec := by
  refine ⟨LocalBridgePhase, inferInstance, inferInstance,
    boundaryPrimitives G boundarySourceRate,
    boundaryInitialState G boundarySourceRate,
    X, boundaryResourceResidual, ?_, hX⟩
  have ha : (1.025 : ℝ) = boundaryLo := by norm_num [boundaryLo]
  have hb : (1.032 : ℝ) = boundaryHi := by norm_num [boundaryHi]
  rw [ha, hb]
  exact boundarySourceRate_exactRootOn

#print axioms boundarySourceRate_exactRootOn
#print axioms boundarySourceRate_unique_of_source_root
#print axioms boundary_paper_spec_of_source_full_witness

#print axioms boundarySourceRate_workerLabor

#print axioms boundarySourceRate_firmRegime
#print axioms boundarySourceRate_firmSigns

#print axioms boundarySourceRate_positiveRealDomain
#print axioms boundarySourceRate_bankDomain

#print axioms boundarySourceRate_spec
#print axioms boundarySourceRate_reduced_prefix

#print axioms boundary_source_output_scale_sharp_box
#print axioms boundary_output_lo_box_from_source
#print axioms boundary_output_hi_box_from_source
#print axioms boundary_component_boxes_from_source
#print axioms boundary_unique_reduced_prefix_rate_from_source

#print axioms boundary_worker_consumption_scale_lower
#print axioms boundary_deposit_rate_lo_source_upper
#print axioms boundary_worker_lo_box_from_source
#print axioms boundary_unique_reduced_prefix_rate_of_two

#print axioms boundary_source_user_cost_sharp_boxes
#print axioms boundary_source_capital_scales_sharp_boxes
#print axioms boundary_capital_cost_lo_box_from_source
#print axioms boundary_unique_reduced_prefix_rate_of_three

#print axioms boundary_worker_consumption_scale_upper
#print axioms boundary_deposit_rate_hi_source_lower
#print axioms boundary_worker_hi_box_from_source
#print axioms boundary_unique_reduced_prefix_rate_of_four

#print axioms boundary_capital_cost_hi_box_from_source
#print axioms boundary_unique_reduced_prefix_rate_of_five

#print axioms boundary_firm_H_endpoint_boxes_from_source
#print axioms boundary_unique_reduced_prefix_rate_of_six

#print axioms boundary_source_capital_scale_H_rational_box
#print axioms boundary_source_firm_H_coefficient_rational_box

#print axioms boundary_source_capital_scale_L_sharp_lower
#print axioms boundary_firm_L_endpoint_boxes_from_source
#print axioms boundary_unique_reduced_prefix_rate_of_eight

#print axioms boundary_source_capital_scale_L_rational_box
#print axioms boundary_firm_L_endpoint_boxes_of_coefficient_box

#print axioms boundary_source_stationary_capital_scale_order

#print axioms boundary_source_user_cost_micro_boxes
#print axioms boundary_source_productivity_collateral_cost_wedge

#print axioms boundary_source_reserve_rate_micro_box
#print axioms boundary_source_loan_rate_micro_box

#print axioms boundary_weight_rational_micro_box
#print axioms boundary_source_slope_rational_micro_boxes

#print axioms boundary_unique_reduced_prefix_rate_of_boxes

#print axioms normalized_output_eq_from_source
#print axioms endpointSigns_of_boxes
#print axioms boundary_reduced_prefix_from_endpoint_boxes

end ProposedBoundaryNormalizationBridge
end Ventura26LiquidityAllocation
