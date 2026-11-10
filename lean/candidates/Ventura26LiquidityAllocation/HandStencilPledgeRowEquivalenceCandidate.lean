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

#print axioms source_sub_reduced_is_sdf_pledge_gap
#print axioms source_eq_reduced_of_pledge_face
#print axioms row_shear_preserves_zero_set
#print axioms source_binding_euler_reduces_using_original_pledge

end ProposedHandStencilPledgeRowEquivalence
end Ventura26LiquidityAllocation
