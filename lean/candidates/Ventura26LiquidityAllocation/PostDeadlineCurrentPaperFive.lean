import Ventura26LiquidityAllocation.CurrentCompactWedgeRepayment
import Ventura26LiquidityAllocation.CurrentCompactFinancingCapacity
import Ventura26LiquidityAllocation.CurrentCompactInteriorKKT
import Ventura26LiquidityAllocation.PaperLemma43CurrentFullCandidate

/-!
# Post-deadline paper-facing proof endpoints for five compact results

Scientific source: ai-project@bac3c6255da39cd1169a965df35bb5e9a230e6e8
  paper/appendix_eight_results.tex, paper/body_compact_after.tex

This file creates one *single, independently kernel-checkable* entry point
for each of the five mathematical statements previously classified as
paper-vs-Lean semantic-audit pending.

It does NOT replace the existing proofs by a new axiom. Each proof
imports a previously kernel-checked formal proof of the *same* paper
assumptions and conclusion. The one exceptional issue is Appendix A.1.2:
the probability expectation is explicitly the finite-support version of
the paper's almost-sure integrability statement, conditional on a
discrete model. This is a scoped semantic caveat, not a claim about
arbitrary continuous-support probability measures.

Appendix A.1.4 is one theorem combining original physical Cobb-Douglas
optimal labor and efficiency, log-loss, output shares, physical MPK,
and the genuine pathwise derivative of the PHYSICAL output ratio.
Neither economic optimality of a DSGE path nor infinite equilibrium
is assumed or deduced.

Only the paper-facing endpoints of the *current compact eight-result
manuscript* are reviewed; the three other results (3.1, 5.1, 5.2)
already have their own independent kernel-certified endpoints.
-/

namespace Ventura26LiquidityAllocation
namespace PostDeadlineCurrentPaperFive

open CurrentCompact

/-- Appendix A.1.1: real robust collateral coverage implies lower
net worth bound, nonnegative net worth, and positivity if capital
or safe deposits are strictly positive. Includes depreciation = 0. -/
theorem lemma_A11_repayment_paper :
    CurrentCompact.repaymentCurrentSpec :=
  CurrentCompact.repaymentCurrent_exact

#print axioms lemma_A11_repayment_paper

/-- Appendix A.1.2: no simultaneous strictly interior saving and
borrowing satisfying the original two first-order conditions.
The expectation is the probability-one finite-support expectation:
positive states can have zero-probability excluded paths. This does
not prove global sufficiency of KKT conditions. -/
theorem lemma_A12_interior_FOC_paper :
    CurrentCompact.noSimultaneousInteriorCurrentSpec :=
  CurrentCompact.noSimultaneousInteriorCurrent_exact

#print axioms lemma_A12_interior_FOC_paper

/-- Appendix A.1.3: capital-capacity upper bound, an attainable
binding debt-capital portfolio, partial derivative wrt gross loan
rate and its strict negative sign, all from explicit economic inputs. -/
theorem proposition_A13_financing_capacity_paper :
    CurrentCompact.financingCapacityCurrentSpec :=
  CurrentCompact.financingCapacityCurrent_exact

#print axioms proposition_A13_financing_capacity_paper

/-- Paper Proposition 5.3: price of collateralized investment
has a positive H-L effective-price wedge, provided thetaH < thetaL,
common positive loan rate, next inflation and next capital price, and
depreciation below one. The common contemporaneous q cancels. -/
theorem proposition_53_effective_price_wedge_paper :
    CurrentCompact.effectiveWedgeCurrentSpec :=
  CurrentCompact.effectiveWedgeCurrent_exact

#print axioms proposition_53_effective_price_wedge_paper

/-- Appendix A.1.4: exact joint statement with same variables and
quantifiers as compact paper. This is intentionally a *single theorem*
requiring no extra hypotheses beyond positive firm masses,
productivities, factor resources, alpha, beta, d=1-alpha-beta,
positive capital at the path point, and differentiability of the
two capital paths. It does not assume efficient output as input. -/
theorem lemma_A14_physical_allocation_and_log_loss_paper
    (vH vL AH AL L alpha beta d : ℝ)
    (kH kL : ℝ → ℝ) (t dkH dkL : ℝ)
    (hvH : 0 < vH) (hvL : 0 < vL)
    (hAH : 0 < AH) (hAL : 0 < AL)
    (hL : 0 < L)
    (ha : 0 < alpha) (hb : 0 < beta) (hd : 0 < d)
    (hsum : alpha + beta + d = 1)
    (hkH : 0 < kH t) (hkL : 0 < kL t)
    (hH : HasDerivAt kH dkH t)
    (hLL : HasDerivAt kL dkL t) :
    CurrentCompact.compactLemmaA14CurrentFullSpec
      vH vL AH AL L alpha beta d kH kL t dkH dkL :=
  CurrentCompact.compactLemmaA14CurrentFull_exact
    vH vL AH AL L alpha beta d kH kL t dkH dkL
    hvH hvL hAH hAL hL ha hb hd hsum hkH hkL hH hLL

#print axioms lemma_A14_physical_allocation_and_log_loss_paper

/-- A single source-readable contract certifying all five mathematical
paper results in their declared domains. The Appendix A.1.4 part is
expressed as a universally quantified proposition, not a theorem
whose conclusion is given as a premise. -/
def CurrentPaperFiveExactSpec : Prop :=
  CurrentCompact.repaymentCurrentSpec ∧
  CurrentCompact.noSimultaneousInteriorCurrentSpec ∧
  CurrentCompact.financingCapacityCurrentSpec ∧
  CurrentCompact.effectiveWedgeCurrentSpec ∧
  (∀ (vH vL AH AL L alpha beta d : ℝ)
      (kH kL : ℝ → ℝ) (t dkH dkL : ℝ),
    0 < vH → 0 < vL →
    0 < AH → 0 < AL →
    0 < L →
    0 < alpha → 0 < beta → 0 < d →
    alpha + beta + d = 1 →
    0 < kH t → 0 < kL t →
    HasDerivAt kH dkH t →
    HasDerivAt kL dkL t →
    CurrentCompact.compactLemmaA14CurrentFullSpec
      vH vL AH AL L alpha beta d kH kL t dkH dkL)

/-- Main joint endpoint: no sorry, sorryAx, admit, new axiom or
unproved source-economy recovery premise. -/
theorem current_paper_five_exact : CurrentPaperFiveExactSpec := by
  dsimp only [CurrentPaperFiveExactSpec]
  refine ⟨lemma_A11_repayment_paper, lemma_A12_interior_FOC_paper,
    proposition_A13_financing_capacity_paper,
    proposition_53_effective_price_wedge_paper, ?_⟩
  intro vH vL AH AL L alpha beta d kH kL t dkH dkL
    hvH hvL hAH hAL hL ha hb hd hsum hkH hkL hH hLL
  exact lemma_A14_physical_allocation_and_log_loss_paper
    vH vL AH AL L alpha beta d kH kL t dkH dkL
    hvH hvL hAH hAL hL ha hb hd hsum hkH hkL hH hLL

#print axioms current_paper_five_exact

end PostDeadlineCurrentPaperFive
end Ventura26LiquidityAllocation
