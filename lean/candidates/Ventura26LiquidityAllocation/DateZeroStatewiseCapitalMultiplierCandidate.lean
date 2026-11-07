import Ventura26LiquidityAllocation.DateZeroOneSidedEulerInequalityCandidate
import Ventura26LiquidityAllocation.Proposition42KKTIdentificationCandidate

/-!
# Stochastic date-zero capital direction: a sparse statewise dual certificate

The source FirmOptimal under feasible nonnegative capital perturbations
implies a SINGLE EXPECTED first-order inequality. In a finite Markov economy
with robust statewise collateral constraints, multipliers naturally form a
vector indexed by successors. If one constraint is active with a positive
collateral coefficient, a sparse nonnegative vector can represent the
nonnegative expected capital gradient and satisfy complementary slackness.

This is a CAPITAL-DIRECTION-only algebraic certificate. It is NOT a full
KKT system for loans, deposits, labour and all dates, and it does not
identify the original Allocation.collateralDual scalar carrier or assert
state-by-state Euler equalities.
-/

namespace Ventura26LiquidityAllocation
namespace ProposedDateZeroStatewiseCapitalMultiplier

open ProposedDateZeroOneSidedEulerInequality
open ProposedDateZeroCapitalExpectedEuler
open ProposedProposition42KKTIdentification

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- Construct a single-support dual vector for one nonnegative scalar gap. -/
theorem exists_sparse_nonnegative_statewise_multiplier
    (gap : ℝ) (gamma slack : S → ℝ) (sStar : S)
    (hgap : 0 ≤ gap)
    (hgamma : 0 < gamma sStar)
    (hactive : slack sStar = 0) :
    ∃ mu : S → ℝ,
      (∀ s, 0 ≤ mu s) ∧
      (∀ s, mu s * slack s = 0) ∧
      (∑ s, mu s * gamma s) = gap := by
  refine ⟨fun s => if s = sStar then gap / gamma sStar else 0,
    ?_, ?_, ?_⟩
  · intro s
    by_cases hs : s = sStar
    · simp [hs, div_nonneg hgap (le_of_lt hgamma)]
    · simp [hs]
  · intro s
    by_cases hs : s = sStar
    · subst s
      simp [hactive]
    · simp [hs]
  · rw [Finset.sum_eq_single sStar]
    · have hcancel : (gap / gamma sStar) * gamma sStar = gap := by
        field_simp [ne_of_gt hgamma] <;> ring
      simpa using hcancel
    · intro s _ hs
      simp [hs]
    · simp

/-- The derivative of the source infinite-horizon objective is nonpositive
    along a feasible right capital direction. One active state suffices for
    a sparse nonnegative vector of collateral-direction dual coefficients. -/
theorem firmOptimal_exists_statewise_capitalDirectionMultiplier
    (P : Primitives S) (I : InheritedState)
    (X : Allocation S) (i : FirmType)
    (hopt : FirmOptimal P I X i)
    (hcapital : ∀ h : History S 0,
      FirmHistoryAdmissible P 0 h → 0 < X.capital i 0 h)
    (hcoeff : ∀ h : History S 0,
      FirmHistoryAdmissible P 0 h → ∀ s : S,
      0 < P.tree.transition (currentState h) s →
      0 ≤ P.pledgeability i * (1 - P.depreciation) *
        (X.inflation 1 (childHistory h s) *
          X.capitalPrice 1 (childHistory h s)))
    (sStar : S)
    (hunit : 0 < capitalEulerCollateralUnit P X i 0
      (rootHistory P.tree) sStar)
    (hactive : capitalEulerCollateralUnit P X i 0
        (rootHistory P.tree) sStar *
          X.capital i 0 (rootHistory P.tree) -
        X.loanRate 0 (rootHistory P.tree) *
          X.loan i 0 (rootHistory P.tree) = 0) :
    ∃ mu : S → ℝ,
      (∀ s, 0 ≤ mu s) ∧
      (∀ s, mu s *
        (capitalEulerCollateralUnit P X i 0 (rootHistory P.tree) s *
          X.capital i 0 (rootHistory P.tree) -
          X.loanRate 0 (rootHistory P.tree) *
            X.loan i 0 (rootHistory P.tree)) = 0) ∧
      (∑ s, mu s *
        capitalEulerCollateralUnit P X i 0 (rootHistory P.tree) s) =
      -expectedCapitalEulerGradient P X i (firmPlanOfAllocation X i) := by
  have hgrad := firmOptimal_expectedCapitalEuler_gradient_nonpos
    P I X i hopt hcapital hcoeff
  exact exists_sparse_nonnegative_statewise_multiplier
    (-expectedCapitalEulerGradient P X i (firmPlanOfAllocation X i))
    (fun s => capitalEulerCollateralUnit P X i 0 (rootHistory P.tree) s)
    (fun s =>
      capitalEulerCollateralUnit P X i 0 (rootHistory P.tree) s *
        X.capital i 0 (rootHistory P.tree) -
      X.loanRate 0 (rootHistory P.tree) *
        X.loan i 0 (rootHistory P.tree))
    sStar (neg_nonneg.mpr hgrad) hunit hactive

/-- The existing source DateZeroBindingBorrower supplies an active successor.
    Positivity of the unit on supported successors is an explicit assumption;
    it cannot be inferred from nonnegative pledgeability alone. -/
theorem firmOptimal_binding_exists_statewise_capitalDirectionMultiplier
    (P : Primitives S) (I : InheritedState)
    (X : Allocation S) (i : FirmType)
    (hopt : FirmOptimal P I X i)
    (hbinding : DateZeroBindingBorrower P X i)
    (hcapital : ∀ h : History S 0,
      FirmHistoryAdmissible P 0 h → 0 < X.capital i 0 h)
    (hcoeff : ∀ h : History S 0,
      FirmHistoryAdmissible P 0 h → ∀ s : S,
      0 < P.tree.transition (currentState h) s →
      0 ≤ P.pledgeability i * (1 - P.depreciation) *
        (X.inflation 1 (childHistory h s) *
          X.capitalPrice 1 (childHistory h s)))
    (hunit : ∀ s : S,
      0 < P.tree.transition P.tree.initial s →
        0 < capitalEulerCollateralUnit P X i 0
          (rootHistory P.tree) s) :
    ∃ mu : S → ℝ,
      (∀ s, 0 ≤ mu s) ∧
      (∀ s, mu s *
        (capitalEulerCollateralUnit P X i 0 (rootHistory P.tree) s *
          X.capital i 0 (rootHistory P.tree) -
          X.loanRate 0 (rootHistory P.tree) *
            X.loan i 0 (rootHistory P.tree)) = 0) ∧
      (∑ s, mu s *
        capitalEulerCollateralUnit P X i 0 (rootHistory P.tree) s) =
      -expectedCapitalEulerGradient P X i (firmPlanOfAllocation X i) := by
  obtain ⟨sStar, hs, heq⟩ :=
    (hbinding (rootHistory P.tree)).2.2.2
  have hspos : 0 < P.tree.transition P.tree.initial sStar := by
    simpa [rootHistory, currentState] using hs
  have hactive : capitalEulerCollateralUnit P X i 0
      (rootHistory P.tree) sStar *
        X.capital i 0 (rootHistory P.tree) -
      X.loanRate 0 (rootHistory P.tree) *
        X.loan i 0 (rootHistory P.tree) = 0 := by
    unfold capitalEulerCollateralUnit
    nlinarith [heq]
  exact firmOptimal_exists_statewise_capitalDirectionMultiplier
    P I X i hopt hcapital hcoeff sStar (hunit sStar hspos) hactive

end ProposedDateZeroStatewiseCapitalMultiplier
end Ventura26LiquidityAllocation
