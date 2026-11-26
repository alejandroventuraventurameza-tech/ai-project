import Mathlib

/-!
# Source-anchored proposition A.1.3 (capacity)

Exact paper: ai-project@bac3c6255da39cd1169a965df35bb5e9a230e6e8,
paper/appendix_eight_results.tex, prop:v0m_original_6_3.

The source asserts the *maximum feasible capital* and its negative
partial derivative, not just a calculus identity. The nonnegative
financing portfolio and binding feasible witness are included below.
This does not assert equilibrium investment or global optimality.
-/

namespace Ventura26LiquidityAllocation.CurrentCompact

/-- Complete one-period funding-capacity assertion, including the
feasible upper bound, an attainable binding portfolio, and derivative. -/
def financingCapacityCurrentSpec : Prop :=
  ∀ (ownResources capitalPrice collateral loanRate : ℝ),
    0 < ownResources →
    0 < capitalPrice →
    0 < collateral →
    0 < loanRate →
    collateral / loanRate < capitalPrice →
    (∀ capital loan : ℝ,
        0 ≤ capital →
        0 ≤ loan →
        capitalPrice * capital = ownResources + loan →
        loanRate * loan ≤ collateral * capital →
        capital ≤ ownResources / (capitalPrice - collateral / loanRate)) ∧
    (∃ capital loan : ℝ,
        capital = ownResources / (capitalPrice - collateral / loanRate) ∧
        0 ≤ capital ∧
        0 ≤ loan ∧
        capitalPrice * capital = ownResources + loan ∧
        loanRate * loan = collateral * capital) ∧
    HasDerivAt
      (fun rate : ℝ => ownResources / (capitalPrice - collateral / rate))
      (-ownResources * collateral /
        (loanRate ^ 2 * (capitalPrice - collateral / loanRate) ^ 2))
      loanRate ∧
    -ownResources * collateral /
      (loanRate ^ 2 * (capitalPrice - collateral / loanRate) ^ 2) < 0

theorem financingCapacityCurrent_exact : financingCapacityCurrentSpec := by
  intro ownResources capitalPrice collateral loanRate
    hresources hcapitalPrice hcollateral hloanRate hbounded
  have hdenomPos : 0 < capitalPrice - collateral / loanRate :=
    sub_pos.mpr hbounded
  have hdenomNe : capitalPrice - collateral / loanRate ≠ 0 :=
    hdenomPos.ne'
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro capital loan hcapital hloan hbudget hpledge
    have hloanUpper : loan ≤ collateral * capital / loanRate := by
      apply (le_div_iff₀ hloanRate).2
      nlinarith [hpledge]
    have hcapitalBound :
        (capitalPrice - collateral / loanRate) * capital ≤ ownResources := by
      calc
        (capitalPrice - collateral / loanRate) * capital =
          capitalPrice * capital - (collateral / loanRate) * capital := by ring
        _ = ownResources + loan - (collateral / loanRate) * capital := by
          rw [hbudget]
        _ ≤ ownResources := by
          have hring :
              (collateral / loanRate) * capital =
                collateral * capital / loanRate := by ring
          rw [hring]
          linarith [hloanUpper]
    exact (le_div_iff₀ hdenomPos).2 (by nlinarith [hcapitalBound])
  · let maxCapital := ownResources / (capitalPrice - collateral / loanRate)
    let maxLoan := collateral * maxCapital / loanRate
    have hmaxCapital : 0 < maxCapital := by
      dsimp [maxCapital]
      exact div_pos hresources hdenomPos
    have hmaxLoan : 0 ≤ maxLoan := by
      dsimp [maxLoan]
      positivity
    have hpledgeEq : loanRate * maxLoan = collateral * maxCapital := by
      dsimp [maxLoan]
      field_simp [hloanRate.ne']
    have hdenomEq :
        (capitalPrice - collateral / loanRate) * maxCapital =
          ownResources := by
      dsimp [maxCapital]
      exact mul_div_cancel₀ ownResources hdenomNe
    have hbudgetEq : capitalPrice * maxCapital =
        ownResources + maxLoan := by
      calc
        capitalPrice * maxCapital =
          (capitalPrice - collateral / loanRate) * maxCapital +
            (collateral / loanRate) * maxCapital := by ring
        _ = ownResources + maxLoan := by
          rw [hdenomEq]
          dsimp [maxLoan]
          ring
    exact ⟨maxCapital, maxLoan, rfl, le_of_lt hmaxCapital, hmaxLoan,
      hbudgetEq, hpledgeEq⟩
  · have hquotRaw := (hasDerivAt_inv hloanRate.ne').const_mul collateral
    have hquot : HasDerivAt
        (fun rate : ℝ => collateral / rate)
        (-collateral / loanRate ^ 2) loanRate := by
      simpa [div_eq_mul_inv] using hquotRaw
    have hinner : HasDerivAt
        (fun rate : ℝ => capitalPrice - collateral / rate)
        (collateral / loanRate ^ 2) loanRate := by
      unfold HasDerivAt HasDerivAtFilter at hquot ⊢
      convert hquot.const_sub capitalPrice using 1
      ext
      simp [div_eq_mul_inv]
    have hderiv :=
      (hasDerivAt_const loanRate ownResources).div hinner hdenomNe
    have hcoef :
        -ownResources * collateral /
            (loanRate ^ 2 * (capitalPrice - collateral / loanRate) ^ 2) =
          (0 * (capitalPrice - collateral / loanRate) -
              ownResources * (collateral / loanRate ^ 2)) /
            (capitalPrice - collateral / loanRate) ^ 2 := by
      field_simp [hloanRate.ne', hdenomNe]
      ring
    rw [hcoef]
    exact hderiv
  · have hnumNeg : -ownResources * collateral < 0 :=
      mul_neg_of_neg_of_pos (neg_neg_of_pos hresources) hcollateral
    have hdenomSqPos :
        0 < loanRate ^ 2 *
          (capitalPrice - collateral / loanRate) ^ 2 := by
      exact mul_pos (sq_pos_of_pos hloanRate) (sq_pos_of_pos hdenomPos)
    exact div_neg_of_neg_of_pos hnumNeg hdenomSqPos

#print axioms financingCapacityCurrent_exact

end Ventura26LiquidityAllocation.CurrentCompact
