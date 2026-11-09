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
    · apply (mul_lt_mul_right hpos).mp
      rw [hscaledH]
      linarith only [hrlo]
    · apply (mul_lt_mul_right hpos).mp
      rw [hscaledH]
      linarith only [hrhi]
  · constructor
    · apply (mul_lt_mul_right hpos).mp
      rw [hscaledL]
      linarith only [hrlo]
    · apply (mul_lt_mul_right hpos).mp
      rw [hscaledL]
      linarith only [hrhi]

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
  unfold ProposedStationaryRealScale.capitalScale
  gcongr

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
