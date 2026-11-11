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

/-! ## Source collateral complementarity and the common recurrent pledge

The source's 34th scalar condition is a *marginal funding dual*.
At a B interior active branch, that dual may be STRICTLY positive
while the collateral slack is zero. Complementarity does not demand
both be zero. The special augmented boundary problem imposes dual=0
only to locate the regime SWITCH, not throughout the B solution.
-/

/-- For source scalar KKT complementarity, strictly positive unused
collateral capacity forces zero funding dual. -/
theorem source_L_strict_slack_implies_funding_dual_zero
    {S : Type*} [Fintype S] [DecidableEq S]
    (P : Primitives S) (Z : LocalPrefixCoordinates)
    (hcomp : LocalScalarComplementarityL P Z)
    (hslack : 0 < localNormalizedSlackL P Z) :
    localNormalizedCollateralDualL P Z = 0 := by
  have hprod :
      localNormalizedSlackL P Z *
        localNormalizedCollateralDualL P Z = 0 := hcomp.2.2
  rcases mul_eq_zero.mp hprod with hzero | hzero
  · exact (ne_of_gt hslack hzero).elim
  · exact hzero

/-- A strictly positive source funding dual forces the collateral
slack to be zero. This is KKT NECESSITY, not global optimality. -/
theorem source_L_strict_funding_dual_implies_binding
    {S : Type*} [Fintype S] [DecidableEq S]
    (P : Primitives S) (Z : LocalPrefixCoordinates)
    (hcomp : LocalScalarComplementarityL P Z)
    (hdual : 0 < localNormalizedCollateralDualL P Z) :
    localNormalizedSlackL P Z = 0 := by
  have hprod :
      localNormalizedSlackL P Z *
        localNormalizedCollateralDualL P Z = 0 := hcomp.2.2
  rcases mul_eq_zero.mp hprod with hzero | hzero
  · exact hzero
  · exact (ne_of_gt hdual hzero).elim

/-- Source KKT permits a B interior with binding collateral and
STRICTLY positive funding dual. The 34th augmented-boundary zero
condition must not be imposed at such a B observation. -/
theorem source_L_binding_positive_dual_is_complementary
    {S : Type*} [Fintype S] [DecidableEq S]
    (P : Primitives S) (Z : LocalPrefixCoordinates)
    (hbinding : localNormalizedSlackL P Z = 0)
    (hdual : 0 < localNormalizedCollateralDualL P Z) :
    LocalScalarComplementarityL P Z := by
  refine ⟨le_of_eq hbinding.symm, le_of_lt hdual, ?_⟩
  simp [hbinding]

/-- The common date-one pledge is a SOURCE level residual. Under
strict positivity it has the same ZERO SET as the recurrent Python
log of the common pledge ratio. It is not a theorem about the
linearized tail being an exact nonlinear solution. -/
theorem source_common_pledge_one_log_zero_iff_original_row_zero
    {S : Type*} [Fintype S] [DecidableEq S]
    (P : Primitives S) (I : InheritedState)
    (Z : LocalPrefixCoordinates) (dateOne recurrent : S)
    (tail : LocalPrefixContinuationRule)
    (hface : 0 < Z.stateTwo.commonPledgeValue)
    (hcapacity : 0 <
      (1 - P.depreciation) *
        (localPrefixDateOneData P Z dateOne recurrent tail).nextControls.inflation *
        (localPrefixDateOneData P Z dateOne recurrent tail).nextControls.capitalPrice) :
    Real.log (Z.stateTwo.commonPledgeValue /
      ((1 - P.depreciation) *
        (localPrefixDateOneData P Z dateOne recurrent tail).nextControls.inflation *
        (localPrefixDateOneData P Z dateOne recurrent tail).nextControls.capitalPrice)) = 0 ↔
      localReducedPrefixResidual LocalPrefixBranch.binding P I Z
        dateOne recurrent tail LocalPrefixEquation.commonPledgeOne = 0 := by
  change Real.log (Z.stateTwo.commonPledgeValue /
      ((1 - P.depreciation) *
        (localPrefixDateOneData P Z dateOne recurrent tail).nextControls.inflation *
        (localPrefixDateOneData P Z dateOne recurrent tail).nextControls.capitalPrice)) = 0 ↔
      (Z.stateTwo.commonPledgeValue -
        (1 - P.depreciation) *
          (localPrefixDateOneData P Z dateOne recurrent tail).nextControls.inflation *
          (localPrefixDateOneData P Z dateOne recurrent tail).nextControls.capitalPrice = 0)
  exact positive_log_ratio_zero_iff_face_difference_zero _ _
    hface hcapacity

#print axioms source_L_strict_slack_implies_funding_dual_zero
#print axioms source_L_strict_funding_dual_implies_binding
#print axioms source_L_binding_positive_dual_is_complementary
#print axioms source_common_pledge_one_log_zero_iff_original_row_zero

/-! ## Three further log/level row conversions from actual SOURCE

These are generic, source-literal ZERO-SET equivalences, not a
numerical calibration or a theorem that all 33 Jacobian rows match.
The worker expression retains the SOURCE's generic elasticities;
Python's hardcoded unity elasticities require a separate parameter
identification.
-/

/-- The SOURCE household deposit Euler uses one minus the ratio,
while the Python system uses the log of that ratio. The factor has
the opposite SIGN, despite identical zeros on the positive domain. -/
theorem source_household_euler_log_zero_iff_original_row_zero
    {S : Type*} [Fintype S] [DecidableEq S]
    (P : Primitives S) (d : LocalPrefixDateData)
    (hpositive : 0 <
      d.controls.depositRate *
        (P.workerDiscount *
          crraMarginal P.workerRiskAversion d.nextControls.workerConsumption /
          crraMarginal P.workerRiskAversion d.controls.workerConsumption) /
          d.nextControls.inflation) :
    Real.log
        (d.controls.depositRate *
          (P.workerDiscount *
            crraMarginal P.workerRiskAversion d.nextControls.workerConsumption /
            crraMarginal P.workerRiskAversion d.controls.workerConsumption) /
          d.nextControls.inflation) = 0 ↔
      localReducedRemainingResidual P d 4 = 0 := by
  change Real.log
      (d.controls.depositRate *
        (P.workerDiscount *
          crraMarginal P.workerRiskAversion d.nextControls.workerConsumption /
          crraMarginal P.workerRiskAversion d.controls.workerConsumption) /
        d.nextControls.inflation) = 0 ↔
    (1 -
      (P.workerDiscount *
        crraMarginal P.workerRiskAversion d.nextControls.workerConsumption /
        crraMarginal P.workerRiskAversion d.controls.workerConsumption) *
      d.controls.depositRate / d.nextControls.inflation = 0)
  have hswap :
      (P.workerDiscount *
        crraMarginal P.workerRiskAversion d.nextControls.workerConsumption /
        crraMarginal P.workerRiskAversion d.controls.workerConsumption) *
      d.controls.depositRate / d.nextControls.inflation =
      d.controls.depositRate *
        (P.workerDiscount *
          crraMarginal P.workerRiskAversion d.nextControls.workerConsumption /
          crraMarginal P.workerRiskAversion d.controls.workerConsumption) /
        d.nextControls.inflation := by
    ring
  rw [hswap]
  have h := positive_log_zero_iff_ratio_minus_one_zero _ hpositive
  constructor
  · intro hz
    have heq := h.mp hz
    linarith only [heq]
  · intro hz
    apply h.mpr
    linarith only [hz]

/-- The original SOURCE labor-supply row is a WAGE minus its exact
CRRA/Frisch marginal-disutility expression. Its log-ratio has the
same zero set under strictly positive wage and labor-cost value. -/
theorem source_worker_labor_log_zero_iff_original_row_zero
    {S : Type*} [Fintype S] [DecidableEq S]
    (P : Primitives S) (d : LocalPrefixDateData)
    (hwage : 0 < d.controls.wage)
    (hcost : 0 <
      P.laborScale *
        d.controls.workerConsumption ^ P.workerRiskAversion *
        localPrefixAggregateLabor P d ^ P.laborCurvature) :
    Real.log (d.controls.wage /
        (P.laborScale *
          d.controls.workerConsumption ^ P.workerRiskAversion *
          localPrefixAggregateLabor P d ^ P.laborCurvature)) = 0 ↔
      localReducedRemainingResidual P d 3 = 0 := by
  change Real.log (d.controls.wage /
      (P.laborScale *
        d.controls.workerConsumption ^ P.workerRiskAversion *
        localPrefixAggregateLabor P d ^ P.laborCurvature)) = 0 ↔
    (d.controls.wage -
      P.laborScale *
        d.controls.workerConsumption ^ P.workerRiskAversion *
        localPrefixAggregateLabor P d ^ P.laborCurvature = 0)
  exact positive_log_ratio_zero_iff_face_difference_zero _ _
    hwage hcost

/-- The SOURCE nominal bank-face transition and the Python log
transition have identical zeros under strict face positivity.
No bank KKT, resource feasibility, or stochastic OTC claim is made. -/
theorem source_bank_face_log_zero_iff_original_row_zero
    {S : Type*} [Fintype S] [DecidableEq S]
    (P : Primitives S) (d : LocalPrefixDateData)
    (hnext : 0 < d.nextBankFace)
    (hpred : 0 <
      bankRenewalFactor P * d.controls.loanRate *
        d.currentBankFace / d.controls.inflation) :
    Real.log (d.nextBankFace /
      (bankRenewalFactor P * d.controls.loanRate *
        d.currentBankFace / d.controls.inflation)) = 0 ↔
      localReducedRemainingResidual P d 0 = 0 := by
  change Real.log (d.nextBankFace /
      (bankRenewalFactor P * d.controls.loanRate *
        d.currentBankFace / d.controls.inflation)) = 0 ↔
    (d.nextBankFace -
      bankRenewalFactor P * d.controls.loanRate *
        d.currentBankFace / d.controls.inflation = 0)
  exact positive_log_ratio_zero_iff_face_difference_zero _ _
    hnext hpred

#print axioms source_household_euler_log_zero_iff_original_row_zero
#print axioms source_worker_labor_log_zero_iff_original_row_zero
#print axioms source_bank_face_log_zero_iff_original_row_zero

#print axioms source_sub_reduced_is_sdf_pledge_gap
#print axioms source_eq_reduced_of_pledge_face
#print axioms row_shear_preserves_zero_set
#print axioms source_binding_euler_reduces_using_original_pledge


/-! ## SOURCE date-one firm budget and floating-pledge Euler

The finite Python date-one state has its own common nominal pledged face
J2, whereas literal EconomicModel SOURCE Euler uses the physical face
(1-delta)*Pi2*q2. Only the pledge level gap separates the two Eulers.
These are identities of SOURCE algebra, not a proof of the full economy. -/

/-- Companion expression for a nominal face J independent of the
physical pledge rule, retaining the actual SOURCE entrepreneurial SDF
and marginal product. -/
noncomputable def sourceEulerWithFloatingCommonFace
    {S : Type*} [Fintype S] [DecidableEq S]
    (P : Primitives S) (d : LocalPrefixDateData) (i : FirmType) (J : ℝ) : ℝ :=
  d.controls.capitalPrice -
    P.pledgeability i * J / d.controls.loanRate -
    localPrefixEntrepreneurSDF P d i *
      (localPrefixNextMarginalProduct P d i +
        (1 - P.depreciation) * d.nextControls.capitalPrice -
        P.pledgeability i * J / d.nextControls.inflation)

/-- Literal SOURCE-minus-floating-Euler difference: exactly a common
pledge row shear. No equilibrium, positive chart or differentiation is
presupposed. -/
theorem source_binding_euler_minus_common_face_is_pledge_shear
    {S : Type*} [Fintype S] [DecidableEq S]
    (P : Primitives S) (d : LocalPrefixDateData) (i : FirmType) (J : ℝ) :
    localReducedFirmCapitalEulerResidual LocalPrefixBranch.binding P d i -
      sourceEulerWithFloatingCommonFace P d i J =
      P.pledgeability i *
        (J - (1 - P.depreciation) * d.nextControls.inflation *
          d.nextControls.capitalPrice) *
        (1 / d.controls.loanRate -
          localPrefixEntrepreneurSDF P d i / d.nextControls.inflation) := by
  dsimp [localReducedFirmCapitalEulerResidual,
    sourceEulerWithFloatingCommonFace, localPrefixPledgeUnit]
  ring

/-- Firm budget under a common nominal face J when the firm-specific
SOURCE face is theta_i*J*k. This is a conditional budget identity. -/
theorem source_firm_budget_with_common_face
    {S : Type*} [Fintype S] [DecidableEq S]
    (P : Primitives S) (d : LocalPrefixDateData) (i : FirmType) (J : ℝ)
    (hface : d.nextFace i =
      P.pledgeability i * J * d.nextCapital i) :
    localReducedFirmBudgetResidual P d i =
      localPrefixFirmConsumption d.controls i +
        (d.controls.capitalPrice -
          P.pledgeability i * J / d.controls.loanRate) *
          d.nextCapital i -
        localPrefixFirmWealth P d i := by
  dsimp [localReducedFirmBudgetResidual]
  rw [hface]
  ring

#print axioms source_binding_euler_minus_common_face_is_pledge_shear
#print axioms source_firm_budget_with_common_face


/-! ## Original SOURCE 33-coordinate log chart: exact round-trip.

Unlike the still-open economic source/Python operator equivalence, these
are literal identities of the original SOURCE chart and its positive domain.
-/

/-- The original Fin 33 coordinate unpacker and flattener are exact
two-sided inverses in the vector-to-record-to-vector direction. -/
theorem source_prefix_coordinate_vector_roundtrip
    (w : Fin 33 → ℝ) :
    localPrefixCoordinatesVector (localPrefixCoordinatesOfVector w) = w := by
  funext j
  fin_cases j <;> rfl

/-- The actual SOURCE log chart has the diagonal exponential form
at *every* coordinate, not only at a stationary root. -/
theorem source_prefix_log_chart_each_coordinate
    (Z0 : LocalPrefixCoordinates) (z : Fin 33 → ℝ)
    (j : Fin 33) :
    localPrefixCoordinatesVector (localPrefixLogChart Z0 z) j =
      localPrefixCoordinatesVector Z0 j * Real.exp (z j) := by
  change localPrefixCoordinatesVector
    (localPrefixCoordinatesOfVector
      (fun k => localPrefixCoordinatesVector Z0 k * Real.exp (z k))) j =
    localPrefixCoordinatesVector Z0 j * Real.exp (z j)
  exact congrFun (source_prefix_coordinate_vector_roundtrip
    (fun k => localPrefixCoordinatesVector Z0 k * Real.exp (z k))) j

/-- Positivity of the 33 baseline coordinates propagates throughout the
SOURCE logarithmic chart; it does not confer bank or household feasibility. -/
theorem source_prefix_log_chart_positive
    (Z0 : LocalPrefixCoordinates) (z : Fin 33 → ℝ)
    (hpositive : LocalPrefixCoordinatesPositive Z0) :
    LocalPrefixCoordinatesPositive (localPrefixLogChart Z0 z) := by
  intro j
  rw [source_prefix_log_chart_each_coordinate]
  exact mul_pos (hpositive j) (Real.exp_pos _)

#print axioms source_prefix_coordinate_vector_roundtrip
#print axioms source_prefix_log_chart_each_coordinate
#print axioms source_prefix_log_chart_positive


/-! ## Exact inverse of the candidate 33-row scaling-plus-pledge shear

The SOURCE/Python row correspondence is an OPEN separate hypothesis.
This theorem states only that the finite-dimensional map associated
with nine nonzero scaling factors and the two date-one Euler pledge
shears has an explicit inverse, for arbitrary values of its coefficients. -/

/-- Algebraic forward transform in SOURCE row order, with the two
date-one Euler rows using the common-pledge row 21. -/
noncomputable def candidateSourceRowTransform
    (d : Fin 33 → ℝ) (aH aL : ℝ)
    (x : Fin 33 → ℝ) (j : Fin 33) : ℝ :=
  if j = 19 then
    d 19 * x 19 - aH * (d 21 * x 21)
  else if j = 20 then
    d 20 * x 20 - aL * (d 21 * x 21)
  else
    d j * x j

/-- Algebraic inverse D^-1(I-K), where K has only entries
K[19,21]=-aH and K[20,21]=-aL. -/
noncomputable def candidateSourceRowInverse
    (d : Fin 33 → ℝ) (aH aL : ℝ)
    (y : Fin 33 → ℝ) (j : Fin 33) : ℝ :=
  if j = 19 then
    (y 19 + aH * y 21) / d 19
  else if j = 20 then
    (y 20 + aL * y 21) / d 20
  else
    y j / d j

/-- Explicit left inverse on all 33 coordinates when the diagonal
normalizations are nonzero. The theorem assumes no model equilibrium. -/
theorem candidate_source_row_left_inverse
    (d : Fin 33 → ℝ) (aH aL : ℝ)
    (hd : ∀ j, d j ≠ 0) :
    Function.LeftInverse
      (candidateSourceRowInverse d aH aL)
      (candidateSourceRowTransform d aH aL) := by
  intro x
  funext j
  by_cases hH : j = (19 : Fin 33)
  · subst j
    simp [candidateSourceRowInverse, candidateSourceRowTransform] <;>
      field_simp [hd (19 : Fin 33), hd (21 : Fin 33)] <;> ring
  · by_cases hL : j = (20 : Fin 33)
    · subst j
      simp [candidateSourceRowInverse, candidateSourceRowTransform] <;>
        field_simp [hd (20 : Fin 33), hd (21 : Fin 33)] <;> ring
    · simp [candidateSourceRowInverse, candidateSourceRowTransform, hH, hL] <;>
        field_simp [hd j] <;> ring

/-- Explicit right inverse of the same full 33-row candidate map. -/
theorem candidate_source_row_right_inverse
    (d : Fin 33 → ℝ) (aH aL : ℝ)
    (hd : ∀ j, d j ≠ 0) :
    Function.RightInverse
      (candidateSourceRowInverse d aH aL)
      (candidateSourceRowTransform d aH aL) := by
  intro y
  funext j
  by_cases hH : j = (19 : Fin 33)
  · subst j
    simp [candidateSourceRowInverse, candidateSourceRowTransform] <;>
      field_simp [hd (19 : Fin 33), hd (21 : Fin 33)] <;> ring
  · by_cases hL : j = (20 : Fin 33)
    · subst j
      simp [candidateSourceRowInverse, candidateSourceRowTransform] <;>
        field_simp [hd (20 : Fin 33), hd (21 : Fin 33)] <;> ring
    · simp [candidateSourceRowInverse, candidateSourceRowTransform, hH, hL] <;>
        field_simp [hd j] <;> ring

#print axioms candidate_source_row_left_inverse
#print axioms candidate_source_row_right_inverse


/-! ## Literal four-instrument SOURCE timing: initial-only support

These lemmas interrogate the actual initialIntervenedPrimitives and
the original two localPrefixDateData constructors. They rule out
direct contamination of date-one policy announcements by date-zero
interventions. This is not a theorem that equilibrium responses
in date one vanish: prices and states can respond endogenously.
-/

/-- The two innovation coordinates enter only at the initial Markov state. -/
theorem source_initial_policy_innovation_pair
    {S : Type*} [Fintype S] [DecidableEq S]
    (P : Primitives S) (v : InitialPolicyIntervention) :
    (initialIntervenedPrimitives P v).reserveRateInnovation P.tree.initial =
       P.reserveRateInnovation P.tree.initial + v.reserveRateInnovation ∧
    (initialIntervenedPrimitives P v).reserveQuantityInnovation P.tree.initial =
       P.reserveQuantityInnovation P.tree.initial + v.reserveQuantityInnovation := by
  simp [initialIntervenedPrimitives]

/-- At every noninitial Markov state the two innovation functions
are unchanged, not merely their stationary values. -/
theorem source_noninitial_policy_innovations_unchanged
    {S : Type*} [Fintype S] [DecidableEq S]
    (P : Primitives S) (v : InitialPolicyIntervention)
    (s : S) (hs : s ≠ P.tree.initial) :
    (initialIntervenedPrimitives P v).reserveRateInnovation s =
       P.reserveRateInnovation s ∧
    (initialIntervenedPrimitives P v).reserveQuantityInnovation s =
       P.reserveQuantityInnovation s := by
  simp [initialIntervenedPrimitives, hs]

/-- Reserve requirement and corridor width are perturbed together
at date zero, for every supplied history. -/
theorem source_initial_policy_path_pair
    {S : Type*} [Fintype S] [DecidableEq S]
    (P : Primitives S) (v : InitialPolicyIntervention)
    (h : History S 0) :
    (initialIntervenedPrimitives P v).reserveRequirementPath 0 h =
       P.reserveRequirementPath 0 h + v.reserveRequirement ∧
    (initialIntervenedPrimitives P v).corridorWidthPath 0 h =
       P.corridorWidthPath 0 h + v.corridorWidth := by
  simp [initialIntervenedPrimitives]

/-- Both path instruments are unchanged at every later date,
irrespective of the history argument. -/
theorem source_future_policy_paths_unchanged
    {S : Type*} [Fintype S] [DecidableEq S]
    (P : Primitives S) (v : InitialPolicyIntervention)
    (t : ℕ) (h : History S t) (ht : t ≠ 0) :
    (initialIntervenedPrimitives P v).reserveRequirementPath t h =
       P.reserveRequirementPath t h ∧
    (initialIntervenedPrimitives P v).corridorWidthPath t h =
       P.corridorWidthPath t h := by
  simp [initialIntervenedPrimitives, ht]

/-- The original date-one reduced data are literally unchanged at
fixed coordinates by a date-zero announcement, provided dateOne
is not the initial Markov state. Equilibrium date-one effects can
still be nonzero when coordinates respond endogenously. -/
theorem source_dateone_prefix_data_fixed_coordinates_unaffected
    {S : Type*} [Fintype S] [DecidableEq S]
    (P : Primitives S) (v : InitialPolicyIntervention)
    (Z : LocalPrefixCoordinates) (dateOne recurrent : S)
    (tail : LocalPrefixContinuationRule)
    (hdate : dateOne ≠ P.tree.initial) :
    localPrefixDateOneData (initialIntervenedPrimitives P v)
        Z dateOne recurrent tail =
      localPrefixDateOneData P Z dateOne recurrent tail := by
  simp [localPrefixDateOneData, initialIntervenedPrimitives,
    localPrefixStateSixFace, bridgeDateOneHistory, bridgeDateZeroHistory,
    hdate]

#print axioms source_initial_policy_innovation_pair
#print axioms source_noninitial_policy_innovations_unchanged
#print axioms source_initial_policy_path_pair
#print axioms source_future_policy_paths_unchanged
#print axioms source_dateone_prefix_data_fixed_coordinates_unaffected


/-! ## SOURCE date-one economic row functions at fixed data/coordinates

The four changed primitive fields are announcement functions or paths.
The actual firm budget, firm capital Euler and 11 other remaining row
formulas read those announcements through LocalPrefixDateData rather
than directly through P. This extra layer is needed before making a
rigorous fixed-coordinate derivative statement for the full prefix.
-/

/-- The original SOURCE entrepreneur budget formula reads only unaffected
economic primitives when its LocalPrefixDateData argument is fixed. -/
theorem source_fixed_data_firm_budget_unaffected
    {S : Type*} [Fintype S] [DecidableEq S]
    (P : Primitives S) (v : InitialPolicyIntervention)
    (d : LocalPrefixDateData) (i : FirmType) :
    localReducedFirmBudgetResidual (initialIntervenedPrimitives P v) d i =
      localReducedFirmBudgetResidual P d i := by
  rfl

/-- Same statement for both capital Euler regimes. -/
theorem source_fixed_data_firm_euler_unaffected
    {S : Type*} [Fintype S] [DecidableEq S]
    (P : Primitives S) (v : InitialPolicyIntervention)
    (d : LocalPrefixDateData) (i : FirmType)
    (branch : LocalPrefixBranch) :
    localReducedFirmCapitalEulerResidual branch
        (initialIntervenedPrimitives P v) d i =
      localReducedFirmCapitalEulerResidual branch P d i := by
  rfl

/-- All 11 literal non-firm SOURCE row functions read unchanged P fields
at a fixed LocalPrefixDateData, including the two policy rule formulas:
their innovations are passed in the data record. -/
theorem source_fixed_data_all_remaining_rows_unaffected
    {S : Type*} [Fintype S] [DecidableEq S]
    (P : Primitives S) (v : InitialPolicyIntervention)
    (d : LocalPrefixDateData) (row : Fin 11) :
    localReducedRemainingResidual (initialIntervenedPrimitives P v) d row =
      localReducedRemainingResidual P d row := by
  rfl

/-- At fixed coordinates all 11 date-one remaining SOURCE rows are
unchanged by an initial policy announcement; no claim is made about
the endogenous date-one equilibrium path. -/
theorem source_dateone_remaining_rows_unaffected
    {S : Type*} [Fintype S] [DecidableEq S]
    (P : Primitives S) (v : InitialPolicyIntervention)
    (Z : LocalPrefixCoordinates) (dateOne recurrent : S)
    (tail : LocalPrefixContinuationRule) (row : Fin 11)
    (hdate : dateOne ≠ P.tree.initial) :
    localReducedRemainingResidual (initialIntervenedPrimitives P v)
        (localPrefixDateOneData (initialIntervenedPrimitives P v)
          Z dateOne recurrent tail) row =
      localReducedRemainingResidual P
        (localPrefixDateOneData P Z dateOne recurrent tail) row := by
  rw [source_dateone_prefix_data_fixed_coordinates_unaffected
    P v Z dateOne recurrent tail hdate]
  exact source_fixed_data_all_remaining_rows_unaffected P v _ row

/-- Both date-one SOURCE entrepreneur budgets are unchanged at
fixed coordinates. -/
theorem source_dateone_firm_budgets_unaffected
    {S : Type*} [Fintype S] [DecidableEq S]
    (P : Primitives S) (v : InitialPolicyIntervention)
    (Z : LocalPrefixCoordinates) (dateOne recurrent : S)
    (tail : LocalPrefixContinuationRule) (i : FirmType)
    (hdate : dateOne ≠ P.tree.initial) :
    localReducedFirmBudgetResidual (initialIntervenedPrimitives P v)
        (localPrefixDateOneData (initialIntervenedPrimitives P v)
          Z dateOne recurrent tail) i =
      localReducedFirmBudgetResidual P
        (localPrefixDateOneData P Z dateOne recurrent tail) i := by
  rw [source_dateone_prefix_data_fixed_coordinates_unaffected
    P v Z dateOne recurrent tail hdate]
  exact source_fixed_data_firm_budget_unaffected P v _ i

/-- Both date-one SOURCE binding Euler rows are unchanged at
fixed coordinates: the policy acts through the endogenous state. -/
theorem source_dateone_binding_eulers_unaffected
    {S : Type*} [Fintype S] [DecidableEq S]
    (P : Primitives S) (v : InitialPolicyIntervention)
    (Z : LocalPrefixCoordinates) (dateOne recurrent : S)
    (tail : LocalPrefixContinuationRule) (i : FirmType)
    (hdate : dateOne ≠ P.tree.initial) :
    localReducedFirmCapitalEulerResidual LocalPrefixBranch.binding
        (initialIntervenedPrimitives P v)
        (localPrefixDateOneData (initialIntervenedPrimitives P v)
          Z dateOne recurrent tail) i =
      localReducedFirmCapitalEulerResidual LocalPrefixBranch.binding P
        (localPrefixDateOneData P Z dateOne recurrent tail) i := by
  rw [source_dateone_prefix_data_fixed_coordinates_unaffected
    P v Z dateOne recurrent tail hdate]
  exact source_fixed_data_firm_euler_unaffected P v _
    i LocalPrefixBranch.binding

/-- The date-one common physical pledge formula also uses only the
unaffected depreciation primitive and fixed date-one controls. -/
theorem source_dateone_common_pledge_unaffected
    {S : Type*} [Fintype S] [DecidableEq S]
    (P : Primitives S) (v : InitialPolicyIntervention)
    (Z : LocalPrefixCoordinates) (dateOne recurrent : S)
    (tail : LocalPrefixContinuationRule)
    (hdate : dateOne ≠ P.tree.initial) :
    Z.stateTwo.commonPledgeValue -
      (1 - (initialIntervenedPrimitives P v).depreciation) *
        (localPrefixDateOneData (initialIntervenedPrimitives P v)
          Z dateOne recurrent tail).nextControls.inflation *
        (localPrefixDateOneData (initialIntervenedPrimitives P v)
          Z dateOne recurrent tail).nextControls.capitalPrice =
    Z.stateTwo.commonPledgeValue -
      (1 - P.depreciation) *
        (localPrefixDateOneData P Z dateOne recurrent tail).nextControls.inflation *
        (localPrefixDateOneData P Z dateOne recurrent tail).nextControls.capitalPrice := by
  rw [source_dateone_prefix_data_fixed_coordinates_unaffected
    P v Z dateOne recurrent tail hdate]
  rfl

#print axioms source_fixed_data_firm_budget_unaffected
#print axioms source_fixed_data_firm_euler_unaffected
#print axioms source_fixed_data_all_remaining_rows_unaffected
#print axioms source_dateone_remaining_rows_unaffected
#print axioms source_dateone_firm_budgets_unaffected
#print axioms source_dateone_binding_eulers_unaffected
#print axioms source_dateone_common_pledge_unaffected


/-! ## SOURCE OTC Leontief/Nash mapping to the Python half-match share

The Python illustration has aa=1/2, meaning the SOURCE effective
matching share a_lambda = 1-exp(-lambda), not lambda itself.
The correct primitive mapping is lambda = log 2. On tightness <= 1,
the SOURCE OTC Nash weight and both slope formulas then equal the
literal Python expressions. The SOURCE has a DIFFERENT formula for
tightness > 1, so this equality has no global extrapolation.
-/

/-- Matching intensity log 2 induces exactly one-half cumulative
matching share, not a structural matching intensity of one-half. -/
theorem source_otc_log_two_share :
    otcMatchIntensityShare (Real.log (2 : ℝ)) = (1 / 2 : ℝ) := by
  unfold otcMatchIntensityShare
  rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  norm_num

/-- Source Nash weight equals Python's weight on the low-tightness
branch. No regularity or derivative claim is hidden in this equality. -/
theorem source_otc_log_two_weight_low_tightness
    (tau : ℝ) (htau : tau ≤ 1) :
    otcCorridorWeight (Real.log (2 : ℝ)) tau =
      1 / (1 + Real.sqrt (2 - tau)) := by
  have hexp : Real.exp (Real.log (2 : ℝ)) = 2 :=
    Real.exp_log (by norm_num : (0 : ℝ) < 2)
  have hrad : tau + (1 - tau) * (2 : ℝ) = 2 - tau := by
    ring
  simp [otcCorridorWeight, htau, hexp, hrad]

/-- The literal SOURCE deficit slope is Python's corridor*(1-aa+aa*w)
when the effective matching share aa=1/2 and tau <= 1. -/
theorem source_otc_deficit_slope_matches_python_low_tightness
    (reserveRate corridor tau : ℝ) (htau : tau ≤ 1) :
    otcDeficitSlope reserveRate
        (otcNegotiatedRate reserveRate (reserveRate + corridor)
          (Real.log (2 : ℝ)) tau)
        (reserveRate + corridor) (Real.log (2 : ℝ)) tau =
      corridor * (1 - (1 / 2 : ℝ) +
        (1 / 2 : ℝ) * (1 / (1 + Real.sqrt (2 - tau)))) := by
  have hfrac :
      otcDeficitMatchFraction (Real.log (2 : ℝ)) tau = (1 / 2 : ℝ) := by
    simp [otcDeficitMatchFraction, htau, source_otc_log_two_share]
  have hw := source_otc_log_two_weight_low_tightness tau htau
  unfold otcDeficitSlope otcNegotiatedRate
  rw [hfrac, hw]
  ring

/-- The literal SOURCE surplus slope is Python's
corridor*tau*aa*w with aa=1/2 on the same low-tightness branch. -/
theorem source_otc_surplus_slope_matches_python_low_tightness
    (reserveRate corridor tau : ℝ) (htau : tau ≤ 1) :
    otcSurplusSlope reserveRate
        (otcNegotiatedRate reserveRate (reserveRate + corridor)
          (Real.log (2 : ℝ)) tau)
        (Real.log (2 : ℝ)) tau =
      corridor * tau * (1 / 2 : ℝ) *
        (1 / (1 + Real.sqrt (2 - tau))) := by
  have hfrac :
      otcSurplusMatchFraction (Real.log (2 : ℝ)) tau = tau / 2 := by
    simp [otcSurplusMatchFraction, htau, source_otc_log_two_share]
  have hw := source_otc_log_two_weight_low_tightness tau htau
  unfold otcSurplusSlope otcNegotiatedRate
  rw [hfrac, hw]
  ring

#print axioms source_otc_log_two_share
#print axioms source_otc_log_two_weight_low_tightness
#print axioms source_otc_deficit_slope_matches_python_low_tightness
#print axioms source_otc_surplus_slope_matches_python_low_tightness

end ProposedHandStencilPledgeRowEquivalence
end Ventura26LiquidityAllocation
