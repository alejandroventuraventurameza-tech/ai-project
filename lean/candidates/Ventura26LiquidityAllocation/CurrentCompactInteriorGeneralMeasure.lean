import Mathlib

/-!
# Appendix A.1.2, arbitrary probability space: integral rather than finite sum

Scientific text: ai-project@bac3c6255da39cd1169a965df35bb5e9a230e6e8,
paper/appendix_eight_results.tex (Lemma A.1.2).

This is a genuinely new general measure-theoretic extension of the
existing finite-support CurrentCompactInteriorKKT theorem.
The probability space can have infinite or continuous support.

Crucial domain assumptions from the source:
* μ is a probability measure on an arbitrary measurable state space;
* V'_N and Π' are positive μ-almost everywhere;
* V'_N / Π' is integrable (finite real expectation);
* common nonrandom positive gross loan/deposit rates;
* both interior FOCs are taken as hypotheses, not sufficient KKT conditions.

No implication about existence of a dynamic equilibrium, KKT sufficiency,
or the SOURCE 33x33 system is made here.
-/

namespace Ventura26LiquidityAllocation.CurrentCompact

open MeasureTheory

/-- Strict positivity of a real-valued integrable expectation when its
integrand is positive almost surely on a probability space. The proof rules
out a zero integral via the a.e.-zero characterization, without any finite
state-space hypothesis. -/
theorem integral_pos_of_ae_pos_probability
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ]
    (f : Ω → ℝ)
    (hfi : Integrable f μ)
    (hpos : ∀ᵐ ω ∂μ, 0 < f ω) :
    0 < ∫ ω, f ω ∂μ := by
  have hnonneg : 0 ≤ᵐ[μ] f :=
    hpos.mono (fun _ hf => hf.le)
  have hnonnegint : 0 ≤ ∫ ω, f ω ∂μ :=
    integral_nonneg_of_ae hnonneg
  rcases eq_or_lt_of_le hnonnegint with heq | hlt
  · have hae : f =ᵐ[μ] (0 : Ω → ℝ) :=
      (integral_eq_zero_iff_of_nonneg_ae hnonneg hfi).mp heq.symm
    obtain ⟨ω, hp, hz⟩ := (hpos.and hae).exists
    exact False.elim ((ne_of_gt hp) (by simpa using hz))
  · exact hlt

/-- State-independent gross rates factor out of a Bochner integral,
including for distributions with infinite support. -/
theorem integral_marginal_rate_factor
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (marginalValue inflationNext : Ω → ℝ) (grossRate : ℝ) :
    (∫ ω, marginalValue ω * grossRate / inflationNext ω ∂μ) =
      (∫ ω, marginalValue ω / inflationNext ω ∂μ) * grossRate := by
  calc
    (∫ ω, marginalValue ω * grossRate / inflationNext ω ∂μ)
        = ∫ ω, (marginalValue ω / inflationNext ω) * grossRate ∂μ := by
            congr 1
            funext ω
            ring
    _ = (∫ ω, marginalValue ω / inflationNext ω ∂μ) * grossRate :=
      integral_mul_const grossRate (fun ω => marginalValue ω / inflationNext ω)

/-- The entire original Appendix A.1.2 financial argument over an arbitrary
probability measure. No Fintype, finite support, PMF, or sums occur in this
specification. The integrability assumption is on the real marginal
V'_N/Π', which is exactly what appears in both FOCs. -/
def noSimultaneousInteriorGeneralSpec : Prop :=
  ∀ {Ω : Type*} [MeasurableSpace Ω]
      (μ : Measure Ω) [IsProbabilityMeasure μ]
      (marginalValue inflationNext : Ω → ℝ)
      (entrepreneurDiscount lambda loanRate depositRate collateralDual
       deposit loan : ℝ),
    (∀ᵐ ω ∂μ, 0 < marginalValue ω) →
    (∀ᵐ ω ∂μ, 0 < inflationNext ω) →
    Integrable (fun ω => marginalValue ω / inflationNext ω) μ →
    0 < entrepreneurDiscount →
    0 < depositRate →
    depositRate < loanRate →
    0 ≤ collateralDual →
    0 < deposit →
    0 < loan →
    lambda = entrepreneurDiscount *
      (∫ ω, marginalValue ω * depositRate / inflationNext ω ∂μ) →
    lambda = entrepreneurDiscount *
      (∫ ω, marginalValue ω * loanRate / inflationNext ω ∂μ) +
        collateralDual * loanRate →
    False

/-- General measure version of the interior saving-borrowing incompatibility.
The proof needs no finite-support assumption and imports no source-economy
equilibrium existence premise. -/
theorem noSimultaneousInteriorGeneral_exact :
    noSimultaneousInteriorGeneralSpec := by
  intro Ω inst μ instprob marginalValue inflationNext
    entrepreneurDiscount lambda loanRate depositRate collateralDual
    deposit loan hmarginal hinflation hintegrable hdiscount
    hdepositRate hspread hdual hdeposit hloan
    hdepositFOC hloanFOC
  let f : Ω → ℝ := fun ω => marginalValue ω / inflationNext ω
  let E : ℝ := ∫ ω, f ω ∂μ
  have hfpos : ∀ᵐ ω ∂μ, 0 < f ω := by
    filter_upwards [hmarginal, hinflation] with ω hm hi
    exact div_pos hm hi
  have hE : 0 < E :=
    integral_pos_of_ae_pos_probability μ f hintegrable hfpos
  have hnorm : 0 < entrepreneurDiscount * E :=
    mul_pos hdiscount hE
  have hrate : 0 < loanRate := lt_trans hdepositRate hspread
  have hstrict :
      (entrepreneurDiscount * E) * depositRate <
        (entrepreneurDiscount * E) * loanRate :=
    mul_lt_mul_of_pos_left hspread hnorm
  have hdualTerm : 0 ≤ collateralDual * loanRate :=
    mul_nonneg hdual hrate.le
  have hfactorDeposit :=
    integral_marginal_rate_factor μ marginalValue inflationNext depositRate
  have hfactorLoan :=
    integral_marginal_rate_factor μ marginalValue inflationNext loanRate
  rw [hfactorDeposit] at hdepositFOC
  rw [hfactorLoan] at hloanFOC
  change lambda = entrepreneurDiscount * (E * depositRate)
    at hdepositFOC
  change lambda = entrepreneurDiscount * (E * loanRate) +
      collateralDual * loanRate at hloanFOC
  nlinarith [hstrict, hdualTerm, hdepositFOC, hloanFOC]

#print axioms integral_pos_of_ae_pos_probability
#print axioms integral_marginal_rate_factor
#print axioms noSimultaneousInteriorGeneral_exact

end Ventura26LiquidityAllocation.CurrentCompact
