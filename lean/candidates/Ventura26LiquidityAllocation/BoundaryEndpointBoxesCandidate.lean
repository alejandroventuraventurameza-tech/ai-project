import Ventura26LiquidityAllocation.BoundaryAnalyticPackageCandidate

/-!
# Extreme-sign rational boxes for the economic frontier

UNCOMPILED LEAN CANDIDATE. Pinned source:
  repo: alejandroventuraventurameza-tech/ai-project
  branch: work/chat-continuity
  commit: 16e24fe828a5a0002ef13bb82bae9e295f190f86
  Mathlib: 5450b53e5ddc75d46418fabb605edbf36bd0beb6

This module separates THREE levels:
  (1) economic normalization by stationary wage^5;
  (2) rational boxes for each normalized term at the two *exact* endpoints;
  (3) the elementary linear sign argument from those boxes.

The boxes themselves are NOT accepted here as theorems: they are explicit
premises. Their exact-rational external enclosure audit is supplied in
BoundaryEndpointRationalCertificate.json and exact_endpoint_box_builder.py.
This file does NOT call that script or import its numerical output as an axiom.
The remaining Lean obligations are precisely the five source-scaling
identities and the ten component box proofs.

No claim of Lean elaboration or kernel certification is made.
-/

namespace Ventura26LiquidityAllocation
namespace ProposedBoundaryEndpointBoxes

open ProposedStationaryRealScale
open ProposedStationaryProductionBridge
open ProposedBoundaryBridge
open ProposedBoundaryResourceRoot
open ProposedBoundaryAnalyticPackage

/-- Generic, exact root-enclosure bridge: rational bounds on the 15th
    powers imply bounds on the positive 15th root. The antecedents can be
    proved with `norm_num` after replacing all operands by rational boxes. -/
theorem fifteenth_root_between (a b x : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hx : 0 ≤ x)
    (hlo : a ^ (15 : ℕ) ≤ x) (hhi : x ≤ b ^ (15 : ℕ)) :
    a ≤ x ^ (1 / 15 : ℝ) ∧ x ^ (1 / 15 : ℝ) ≤ b := by
  constructor
  · have h := Real.rpow_le_rpow (pow_nonneg ha _) hlo
      (by norm_num : (0 : ℝ) ≤ 1 / 15)
    rw [Real.pow_rpow_inv_natCast ha (by norm_num : (15 : ℕ) ≠ 0)] at h
    exact h
  · have h := Real.rpow_le_rpow hx hhi
      (by norm_num : (0 : ℝ) ≤ 1 / 15)
    rw [Real.pow_rpow_inv_natCast hb (by norm_num : (15 : ℕ) ≠ 0)] at h
    exact h

/-- Same positive parent coefficient used by the exact rational audit.
    The stationary consumption times wage^5. -/
noncomputable def firmCoefficient (i : FirmType) : ℝ :=
  (5 / 12) * (userCost i * capitalScale i / (1 / 3)) -
    (1 / 40) * capitalPrice * capitalScale i -
    (ProposedStationaryBank.loanRate - 1) *
      pledgeability i * liquidationValue * capitalScale i /
        ProposedStationaryBank.loanRate

/-- Let z^15=s^8*(betaW*RD)^5. All bases are positive on the bracket. -/
noncomputable def boundaryOutputRoot15 (R : ℝ) : ℝ :=
  (boundaryCapitalScale R ^ (8 : ℕ) *
    ((99 / 100 : ℝ) * boundaryDepositRate R) ^ (5 : ℕ)) ^ (1 / 15 : ℝ)

noncomputable def normalizedOutput (R : ℝ) : ℝ :=
  outputScale * boundaryOutputRoot15 R

noncomputable def normalizedWorkerConsumption (R : ℝ) : ℝ :=
  workerConsumptionScale / ((99 / 100) * boundaryDepositRate R)

noncomputable def normalizedFirmConsumption (R : ℝ) (i : FirmType) : ℝ :=
  match i with
  | .H => firmCoefficient .H *
      (continuationReturn .L - pledgeability .H * liquidationValue) /
        (R * parentEffectivePrice .H)
  | .L => firmCoefficient .L / ((24 / 25) * R)

noncomputable def normalizedCapitalCost (R : ℝ) : ℝ :=
  average capitalScale *
    (41 / 80 + 1 / (4 * boundaryCapitalScale R) -
      (4719 / 6400) * boundaryCapitalScale R)

noncomputable def normalizedResourceResidual (R : ℝ) : ℝ :=
  normalizedOutput R - normalizedWorkerConsumption R -
    (normalizedFirmConsumption R .H + normalizedFirmConsumption R .L) / 2 -
      normalizedCapitalCost R

/-- The source-level normalization is decomposed into five identities.
    Unlike taking a `Phi` sign as a premise, each is a specific equality
    following from stationary scaling, production, and a 15th-root identity. -/
structure BoundaryScaleIdentities (R : ℝ) : Prop where
  output : wage ^ (5 : ℕ) * boundaryAggregateOutput R = normalizedOutput R
  worker : wage ^ (5 : ℕ) * boundaryWorkerConsumption R =
    normalizedWorkerConsumption R
  firmH : wage ^ (5 : ℕ) * boundaryConsumption R .H =
    normalizedFirmConsumption R .H
  firmL : wage ^ (5 : ℕ) * boundaryConsumption R .L =
    normalizedFirmConsumption R .L
  capital : wage ^ (5 : ℕ) * boundaryCapitalCost R =
    normalizedCapitalCost R

/-- Once the five source-scaling identities are established, this is a pure
    ring identity; no independent economic residual is postulated. -/
theorem normalizedResidual_eq_wage_pow_mul
    (R : ℝ) (h : BoundaryScaleIdentities R) :
    normalizedResourceResidual R =
      wage ^ (5 : ℕ) * boundaryResourceResidual R := by
  unfold normalizedResourceResidual boundaryResourceResidual
  unfold ProposedStationaryRealScale.average
  calc
    normalizedOutput R - normalizedWorkerConsumption R -
        (normalizedFirmConsumption R .H + normalizedFirmConsumption R .L) / 2 -
        normalizedCapitalCost R =
      wage ^ (5 : ℕ) * boundaryAggregateOutput R -
        wage ^ (5 : ℕ) * boundaryWorkerConsumption R -
        (wage ^ (5 : ℕ) * boundaryConsumption R .H +
          wage ^ (5 : ℕ) * boundaryConsumption R .L) / 2 -
        wage ^ (5 : ℕ) * boundaryCapitalCost R := by
          rw [← h.output, ← h.worker, ← h.firmH, ← h.firmL, ← h.capital]
    _ = _ := by ring

/-- Ten independent, coarse endpoint enclosures. Each is a rational
    inequality on a source-derived normalized quantity. They are *not*
    postulated to be true without proof in the final theorem. -/
structure BoundaryComponentBoxes : Prop where
  Ylo_upper : normalizedOutput boundaryLo < 1327678 / 100000
  CWlo_lower : 793630 / 100000 < normalizedWorkerConsumption boundaryLo
  CHlo_lower : 296932 / 100000 < normalizedFirmConsumption boundaryLo .H
  CLlo_lower : 382592 / 100000 < normalizedFirmConsumption boundaryLo .L
  GammaLo_lower : 266849 / 100000 < normalizedCapitalCost boundaryLo
  Yhi_lower : 1340498 / 100000 < normalizedOutput boundaryHi
  CWhi_upper : normalizedWorkerConsumption boundaryHi < 788240 / 100000
  CHhi_upper : normalizedFirmConsumption boundaryHi .H < 294921 / 100000
  CLhi_upper : normalizedFirmConsumption boundaryHi .L < 380000 / 100000
  GammaHi_upper : normalizedCapitalCost boundaryHi < 164406 / 100000

/-- The component boxes imply considerably more than nonzero endpoints.
    Proof is rational linear arithmetic: no roots, rates or divisions remain. -/
theorem normalized_endpoint_strict_margins (h : BoundaryComponentBoxes) :
    normalizedResourceResidual boundaryLo < -(7 / 10) ∧
      (1 / 2 : ℝ) < normalizedResourceResidual boundaryHi := by
  constructor
  · unfold normalizedResourceResidual
    linarith [h.Ylo_upper, h.CWlo_lower, h.CHlo_lower,
      h.CLlo_lower, h.GammaLo_lower]
  · unfold normalizedResourceResidual
    linarith [h.Yhi_lower, h.CWhi_upper, h.CHhi_upper,
      h.CLhi_upper, h.GammaHi_upper]

/-- Final kernel target from component inequalities and the source bridge.
    The two hypotheses remain exposed until their independent Lean proofs
    are supplied: this is NOT the final theorem `BoundaryEndpointSigns`. -/
theorem endpointSigns_of_verified_components
    (hbridgeLo : BoundaryScaleIdentities boundaryLo)
    (hbridgeHi : BoundaryScaleIdentities boundaryHi)
    (hboxes : BoundaryComponentBoxes) :
    BoundaryEndpointSigns := by
  rcases normalized_endpoint_strict_margins hboxes with ⟨hlo, hhi⟩
  have hw : 0 < wage ^ (5 : ℕ) := pow_pos wage_pos _
  constructor
  · have hprod : wage ^ (5 : ℕ) * boundaryResourceResidual boundaryLo < 0 := by
      rw [← normalizedResidual_eq_wage_pow_mul boundaryLo hbridgeLo]
      linarith
    by_contra hnot
    have hnonneg : 0 ≤ boundaryResourceResidual boundaryLo := le_of_not_gt hnot
    have hnonnegProd := mul_nonneg hw.le hnonneg
    linarith
  · have hprod : 0 < wage ^ (5 : ℕ) * boundaryResourceResidual boundaryHi := by
      rw [← normalizedResidual_eq_wage_pow_mul boundaryHi hbridgeHi]
      linarith
    by_contra hnot
    have hnonpos : boundaryResourceResidual boundaryHi ≤ 0 := le_of_not_gt hnot
    have hnonposProd := mul_nonpos_of_nonneg_of_nonpos hw.le hnonpos
    linarith

end ProposedBoundaryEndpointBoxes
end Ventura26LiquidityAllocation
