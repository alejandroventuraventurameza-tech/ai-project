import Ventura26LiquidityAllocation.EconomicModel

/-!
# Exact collateral-pledge elimination in the linearized Euler representation

The 16-row hand stencil applies the nominal pledge identity before
linearizing the binding firm capital Euler residual. The separate
nonlinear Python evaluator keeps a face Jnext and the pledge row g.

The apparently missing future-inflation, face and capital-price coefficients
differ by an elementary row shear. This module proves:
1. the algebraic difference of the two Euler presentations;
2. their exact zero-set agreement when the pledge identity holds;
3. the invertibility-on-zeros of the elementary row operation;
4. an actual SOURCE localReducedFirmCapitalEulerResidual simplification.

This does NOT connect all 34 SOURCE rows to the Python reduction, and
does not establish the differential of the nonlinear SOURCE operator.
-/

namespace Ventura26LiquidityAllocation
namespace ProposedHandStencilPledgeRowEquivalence

/-- Raw capital Euler residual retaining a separately varying nominal
per-unit collateral face Jnext. This is a local expression, not a
new structural equilibrium or policy rule. -/
noncomputable def sourceFaceEuler
    (qNow loanRate sdf ukNext ad qNext theta Jnext piNext : ℝ) : ℝ :=
  qNow - theta * Jnext / loanRate -
    sdf * (ukNext + ad * qNext - theta * Jnext / piNext)

/-- The algebraically reduced capital Euler, where the pledge identity
Jnext = ad*piNext*qNext has already been used in the continuation payoff. -/
noncomputable def reducedFaceEuler
    (qNow loanRate sdf ukNext ad qNext theta Jnext : ℝ) : ℝ :=
  qNow - theta * Jnext / loanRate -
    sdf * (ukNext + (1 - theta) * ad * qNext)

/-- Exact source-minus-hand residual, with NO first-order approximation. -/
theorem source_sub_reduced_is_sdf_pledge_gap
    (qNow loanRate sdf ukNext ad qNext theta Jnext piNext : ℝ) :
    sourceFaceEuler qNow loanRate sdf ukNext ad qNext theta Jnext piNext -
      reducedFaceEuler qNow loanRate sdf ukNext ad qNext theta Jnext =
      sdf * theta * (Jnext / piNext - ad * qNext) := by
  dsimp [sourceFaceEuler, reducedFaceEuler]
  ring

/-- Pledge-clearing makes the two Euler residuals literally equal.
The only denominator restriction used here is piNext nonzero. -/
theorem source_eq_reduced_of_pledge_face
    (qNow loanRate sdf ukNext ad qNext theta Jnext piNext : ℝ)
    (hpi : piNext ≠ 0)
    (hface : Jnext = ad * piNext * qNext) :
    sourceFaceEuler qNow loanRate sdf ukNext ad qNext theta Jnext piNext =
      reducedFaceEuler qNow loanRate sdf ukNext ad qNext theta Jnext := by
  have hratio : Jnext / piNext = ad * qNext := by
    rw [hface]
    field_simp [hpi]
  have hdiff :=
    source_sub_reduced_is_sdf_pledge_gap
      qNow loanRate sdf ukNext ad qNext theta Jnext piNext
  rw [hratio] at hdiff
  nlinarith only [hdiff]

/-- An elementary row shear has the same zero set as the unmodified
system when the pledge-identity residual is also imposed. -/
theorem row_shear_preserves_zero_set
    (fH fL g lambdaH lambdaL : ℝ) :
    ((fH + lambdaH * g = 0) ∧
     (fL + lambdaL * g = 0) ∧ g = 0) ↔
    (fH = 0 ∧ fL = 0 ∧ g = 0) := by
  constructor
  · rintro ⟨hH, hL, hg⟩
    constructor
    · simpa [hg] using hH
    constructor
    · simpa [hg] using hL
    · exact hg
  · rintro ⟨hH, hL, hg⟩
    simpa [hH, hL, hg]

/-- In the actual EconomicModel source, the pledge-per-unit value is
already defined as theta*(1-delta)*Pi_next*q_next. Thus the binding
capital Euler expression can be written in the hand reduced form
whenever source future gross inflation is nonzero. -/
theorem source_binding_euler_reduces_using_original_pledge
    {S : Type*} [Fintype S] [DecidableEq S]
    (P : Primitives S) (d : LocalPrefixDateData) (i : FirmType)
    (hpi : d.nextControls.inflation ≠ 0) :
    localReducedFirmCapitalEulerResidual LocalPrefixBranch.binding P d i =
      d.controls.capitalPrice -
        localPrefixPledgeUnit P d i / d.controls.loanRate -
        localPrefixEntrepreneurSDF P d i *
          (localPrefixNextMarginalProduct P d i +
            (1 - P.pledgeability i) *
              (1 - P.depreciation) * d.nextControls.capitalPrice) := by
  have hpledge :
      localPrefixPledgeUnit P d i / d.nextControls.inflation =
        P.pledgeability i * (1 - P.depreciation) *
          d.nextControls.capitalPrice := by
    dsimp [localPrefixPledgeUnit]
    field_simp [hpi]
  dsimp [localReducedFirmCapitalEulerResidual]
  rw [hpledge]
  ring

/-- The *literal* binding-regime residual is exactly the restriction
that the nominal face equals the collateralized face. -/
theorem source_binding_regime_zero_iff_nominal_face
    {S : Type*} [Fintype S] [DecidableEq S]
    (P : Primitives S) (d : LocalPrefixDateData) (i : FirmType) :
    localReducedFirmRegimeResidual LocalPrefixBranch.binding P d i = 0 ↔
      d.nextFace i =
        localPrefixPledgeUnit P d i * d.nextCapital i := by
  change (d.nextFace i -
    localPrefixPledgeUnit P d i * d.nextCapital i = 0) ↔
      (d.nextFace i =
        localPrefixPledgeUnit P d i * d.nextCapital i)
  exact sub_eq_zero

/-- With nominal collateral binding, the actual SOURCE firm budget
equals its effective-capital-price representation. This statement
uses the literal original budget residual, without any extra firm
optimality or positivity assumption. -/
theorem source_firm_budget_effective_price_of_face
    {S : Type*} [Fintype S] [DecidableEq S]
    (P : Primitives S) (d : LocalPrefixDateData) (i : FirmType)
    (hface : d.nextFace i =
      localPrefixPledgeUnit P d i * d.nextCapital i) :
    localReducedFirmBudgetResidual P d i =
      localPrefixFirmConsumption d.controls i +
        (d.controls.capitalPrice -
          localPrefixPledgeUnit P d i / d.controls.loanRate) *
            d.nextCapital i -
        localPrefixFirmWealth P d i := by
  dsimp [localReducedFirmBudgetResidual]
  rw [hface]
  ring

/-- The source B-regime row alone gives the face equality needed
to reconstruct the effective price inside the source budget. -/
theorem source_firm_budget_effective_price_of_binding_regime_zero
    {S : Type*} [Fintype S] [DecidableEq S]
    (P : Primitives S) (d : LocalPrefixDateData) (i : FirmType)
    (hreg :
      localReducedFirmRegimeResidual LocalPrefixBranch.binding P d i = 0) :
    localReducedFirmBudgetResidual P d i =
      localPrefixFirmConsumption d.controls i +
        (d.controls.capitalPrice -
          localPrefixPledgeUnit P d i / d.controls.loanRate) *
            d.nextCapital i -
        localPrefixFirmWealth P d i := by
  apply source_firm_budget_effective_price_of_face P d i
  exact (source_binding_regime_zero_iff_nominal_face P d i).mp hreg

#print axioms source_binding_regime_zero_iff_nominal_face
#print axioms source_firm_budget_effective_price_of_face
#print axioms source_firm_budget_effective_price_of_binding_regime_zero

/-- The financing-adjusted capital price after substituting the
binding nominal collateral face. This is a PRICE wedge, not a
claim that the resulting investment allocation is optimal. -/
noncomputable def sourceEffectiveCapitalPrice
    {S : Type*} [Fintype S] [DecidableEq S]
    (P : Primitives S) (d : LocalPrefixDateData) (i : FirmType) : ℝ :=
  d.controls.capitalPrice -
    localPrefixPledgeUnit P d i / d.controls.loanRate

/-- A source-identity, evaluated under a COMMON loan rate and common
next-period capital price/inflation, but firm-specific pledgeability.
No numerical calibration is assumed. -/
theorem source_effective_price_wedge_H_minus_L
    {S : Type*} [Fintype S] [DecidableEq S]
    (P : Primitives S) (d : LocalPrefixDateData) :
    sourceEffectiveCapitalPrice P d FirmType.H -
      sourceEffectiveCapitalPrice P d FirmType.L =
      (P.pledgeability FirmType.L - P.pledgeability FirmType.H) *
        ((1 - P.depreciation) * d.nextControls.inflation *
          d.nextControls.capitalPrice / d.controls.loanRate) := by
  dsimp [sourceEffectiveCapitalPrice, localPrefixPledgeUnit]
  ring

/-- Under an explicitly SMALLER H collateral share, a strictly
positive collateral price and a positive COMMON gross loan rate,
firm H faces a strictly HIGHER effective investment price.
H's higher productivity is recorded separately by P.productivity_order,
but does not enter this pure budget identity. No total policy
derivative, equilibrium investment ranking, or growth claim follows. -/
theorem source_less_pledgeable_H_higher_effective_price
    {S : Type*} [Fintype S] [DecidableEq S]
    (P : Primitives S) (d : LocalPrefixDateData)
    (hpledge : P.pledgeability FirmType.H < P.pledgeability FirmType.L)
    (hdepr : P.depreciation < 1)
    (hpi : 0 < d.nextControls.inflation)
    (hq : 0 < d.nextControls.capitalPrice)
    (hloan : 0 < d.controls.loanRate) :
    sourceEffectiveCapitalPrice P d FirmType.L <
      sourceEffectiveCapitalPrice P d FirmType.H := by
  have hspread : 0 <
      P.pledgeability FirmType.L - P.pledgeability FirmType.H :=
    sub_pos.mpr hpledge
  have hnondepr : 0 < 1 - P.depreciation := sub_pos.mpr hdepr
  have hunit : 0 < (1 - P.depreciation) *
      d.nextControls.inflation * d.nextControls.capitalPrice /
      d.controls.loanRate :=
    div_pos (mul_pos (mul_pos hnondepr hpi) hq) hloan
  have hwedge : 0 <
      sourceEffectiveCapitalPrice P d FirmType.H -
        sourceEffectiveCapitalPrice P d FirmType.L := by
    rw [source_effective_price_wedge_H_minus_L]
    exact mul_pos hspread hunit
  exact sub_pos.mp hwedge

#print axioms source_effective_price_wedge_H_minus_L
#print axioms source_less_pledgeable_H_higher_effective_price

/-! ## SOURCE/Python zero-set bridge for firm regime residuals

Python writes the L-slack and firm-binding constraints as logarithmic
ratios; EconomicModel.lean writes them as a ratio-minus-one or
a face-minus-collateral product. Positivity is essential. These
lemmas establish identical ZERO SETS for the source-constructed
expressions. They do NOT prove equality of numerical residual values
or of raw Jacobian rows. -/

/-- A log residual and a ratio-minus-one residual have the same zeros
on the strictly positive real domain. -/
theorem positive_log_zero_iff_ratio_minus_one_zero
    (x : ℝ) (hx : 0 < x) :
    Real.log x = 0 ↔ x - 1 = 0 := by
  constructor
  · intro hlog
    have hexp := congrArg Real.exp hlog
    have hx1 : x = 1 := by
      simpa [Real.exp_log hx] using hexp
    exact sub_eq_zero.mpr hx1
  · intro hsub
    have hx1 : x = 1 := sub_eq_zero.mp hsub
    simpa [hx1]

/-- A log face-ratio residual has the same zeros as a level face gap
if both its numerator and denominator are strictly positive. -/
theorem positive_log_ratio_zero_iff_face_difference_zero
    (face capacity : ℝ) (hface : 0 < face) (hcapacity : 0 < capacity) :
    Real.log (face / capacity) = 0 ↔ face - capacity = 0 := by
  constructor
  · intro hlog
    have hratio : face / capacity - 1 = 0 :=
      (positive_log_zero_iff_ratio_minus_one_zero
        (face / capacity) (div_pos hface hcapacity)).mp hlog
    have hquot : face / capacity = 1 := sub_eq_zero.mp hratio
    have hface_eq : face = capacity := by
      have h := (div_eq_iff (ne_of_gt hcapacity)).mp hquot
      simpa using h
    exact sub_eq_zero.mpr hface_eq
  · intro hgap
    have hface_eq : face = capacity := sub_eq_zero.mp hgap
    simpa [hface_eq, ne_of_gt hcapacity]

/-- In the source economic L-slack regime, the Python-style log
funding Euler is zero iff the original source level/rational Euler
is zero. The factor is the L entrepreneur's literal source SDF. -/
theorem source_L_slack_log_row_zero_iff_source_regime_row_zero
    {S : Type*} [Fintype S] [DecidableEq S]
    (P : Primitives S) (d : LocalPrefixDateData)
    (hrate : 0 < d.controls.loanRate)
    (hsdf : 0 < localPrefixEntrepreneurSDF P d FirmType.L)
    (hpi : 0 < d.nextControls.inflation) :
    Real.log
        (d.controls.loanRate *
          localPrefixEntrepreneurSDF P d FirmType.L /
          d.nextControls.inflation) = 0 ↔
      localReducedFirmRegimeResidual LocalPrefixBranch.slack
        P d FirmType.L = 0 := by
  change Real.log
      (d.controls.loanRate *
        localPrefixEntrepreneurSDF P d FirmType.L /
        d.nextControls.inflation) = 0 ↔
    (d.controls.loanRate *
      localPrefixEntrepreneurSDF P d FirmType.L /
      d.nextControls.inflation - 1 = 0)
  exact positive_log_zero_iff_ratio_minus_one_zero _
    (div_pos (mul_pos hrate hsdf) hpi)

/-- In the source binding regime for either firm, the Python-style
log face-to-collateral ratio is zero iff the original nominal-face
SOURCE regime gap is zero. Neither residual can replace the other
outside the positive domain. -/
theorem source_firm_binding_log_row_zero_iff_source_regime_row_zero
    {S : Type*} [Fintype S] [DecidableEq S]
    (P : Primitives S) (d : LocalPrefixDateData) (i : FirmType)
    (hface : 0 < d.nextFace i)
    (hcollateral : 0 <
      localPrefixPledgeUnit P d i * d.nextCapital i) :
    Real.log
        (d.nextFace i /
          (localPrefixPledgeUnit P d i * d.nextCapital i)) = 0 ↔
      localReducedFirmRegimeResidual LocalPrefixBranch.binding
        P d i = 0 := by
  change Real.log
      (d.nextFace i /
        (localPrefixPledgeUnit P d i * d.nextCapital i)) = 0 ↔
      (d.nextFace i -
        localPrefixPledgeUnit P d i * d.nextCapital i = 0)
  exact positive_log_ratio_zero_iff_face_difference_zero _ _
    hface hcollateral

#print axioms positive_log_zero_iff_ratio_minus_one_zero
#print axioms positive_log_ratio_zero_iff_face_difference_zero
#print axioms source_L_slack_log_row_zero_iff_source_regime_row_zero
#print axioms source_firm_binding_log_row_zero_iff_source_regime_row_zero

#print axioms source_sub_reduced_is_sdf_pledge_gap
#print axioms source_eq_reduced_of_pledge_face
#print axioms row_shear_preserves_zero_set
#print axioms source_binding_euler_reduces_using_original_pledge

end ProposedHandStencilPledgeRowEquivalence
end Ventura26LiquidityAllocation
