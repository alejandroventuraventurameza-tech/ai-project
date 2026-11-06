import Ventura26LiquidityAllocation.Proposition42KKTIdentificationCandidate
import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-!
# From literal dynamic firm optimality to feasible first-order stationarity

This module separates two statements:
(A) a negative identification result. In the PINNED source, FirmOptimal
    is independent of the freely stored collateralDual. Therefore FirmOptimal
    cannot, by itself, imply that the capital Euler residual with that
    arbitrary dual is zero, even when the collateral coefficient is nonzero.
(B) a positive first-order condition, genuinely DERIVED from FirmOptimal:
    every differentiable, feasible, two-sided plan variation through the
    selected plan has zero derivative of discounted firm utility.

The missing substantive tasks for a source KKT theorem are constructing
such variations, differentiating the discounted objective/constraints,
identifying the resulting endogenous shadow price and proving the usual
constraint qualifications. Neither an Euler residual nor KKT is assumed
in the positive variation-stationarity theorem.

No original source/checkpoint edits, sorry, admit or added axioms.
-/

namespace Ventura26LiquidityAllocation
namespace ProposedFirmOptimalVariation

open Filter Topology
open ProposedContinuationContractAudit
open ProposedProposition42KKTIdentification

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- Changing only the free multiplier carrier does not change firm feasibility,
    objective, the source terminal condition, or comparison optimality. -/
theorem firmOptimal_replaceCollateralDual_iff
    (P : Primitives S) (I : InheritedState) (X : Allocation S)
    (dual : FirmType → AdaptedProcess S) (i : FirmType) :
    FirmOptimal P I (replaceCollateralDual X dual) i ↔
      FirmOptimal P I X i := by
  rfl

/-- Pointwise obstruction: given one optimal allocation and a nonzero
    collateral unit, there EXISTS an equally optimal allocation (same
    primals) whose stored-dual capital Euler residual is NOT zero. -/
theorem exists_firmOptimal_without_capitalEuler
    (P : Primitives S) (I : InheritedState) (X : Allocation S)
    (i : FirmType) (t : ℕ) (h : History S t) (s : S)
    (hopt : FirmOptimal P I X i)
    (hunit : capitalEulerCollateralUnit P X i t h s ≠ 0) :
    ∃ Y : Allocation S, FirmOptimal P I Y i ∧
      localFirmCapitalEulerResidual P Y i t h s ≠ 0 := by
  by_cases hz : localFirmCapitalEulerResidual P X i t h s = 0
  · let dual : FirmType → AdaptedProcess S :=
      fun j k hk ↦ X.collateralDual j k hk + 1
    let Y := replaceCollateralDual X dual
    refine ⟨Y, (firmOptimal_replaceCollateralDual_iff P I X dual i).2 hopt, ?_⟩
    intro hy
    have heq := capitalEuler_dual_unique_of_same_primal
      P X dual i t h s hz hy hunit
    change X.collateralDual i t h = X.collateralDual i t h + 1 at heq
    linarith
  · exact ⟨X, hopt, hz⟩

/-- A formal counterexample to any blanket claim that literal FirmOptimal
    implies the currently stored collateralDual Euler residual. -/
theorem not_all_firmOptimal_have_capitalEuler
    (P : Primitives S) (I : InheritedState) (X : Allocation S)
    (i : FirmType) (t : ℕ) (h : History S t) (s : S)
    (hopt : FirmOptimal P I X i)
    (hunit : capitalEulerCollateralUnit P X i t h s ≠ 0) :
    ¬ (∀ Y : Allocation S,
      FirmOptimal P I Y i →
        localFirmCapitalEulerResidual P Y i t h s = 0) := by
  intro hall
  obtain ⟨Y, hY, hne⟩ :=
    exists_firmOptimal_without_capitalEuler P I X i t h s hopt hunit
  exact hne (hall Y hY)

/-- Literal objective dominance for an arbitrary feasible and well-defined
    one-parameter variation through the optimum. -/
theorem firmOptimal_variation_bound
    (P : Primitives S) (I : InheritedState) (X : Allocation S)
    (i : FirmType) (variation : ℝ → FirmPlan S)
    (hopt : FirmOptimal P I X i)
    (hzero : variation 0 = firmPlanOfAllocation X i)
    (radius : ℝ) (hradius : 0 < radius)
    (hadmissible : ∀ ε : ℝ, |ε| < radius →
      FirmFeasible P I X i (variation ε) ∧
      FirmObjectiveWellDefined P (variation ε)) :
    ∀ ε : ℝ, |ε| < radius →
      discountedFirmUtility P (variation ε) ≤
        discountedFirmUtility P (variation 0) := by
  intro ε hε
  have h := hopt.2.2.2 (variation ε)
    (hadmissible ε hε).1 (hadmissible ε hε).2
  simpa [hzero] using h

/-- Fermat's theorem applied to the ACTUAL discounted dynamic objective.
    No Euler or KKT conclusion is postulated, and no derivative is asserted
    to exist unless given by an explicit analytic regularity hypothesis. -/
theorem firmOptimal_twoSidedVariation_derivative_zero
    (P : Primitives S) (I : InheritedState) (X : Allocation S)
    (i : FirmType) (variation : ℝ → FirmPlan S)
    (hopt : FirmOptimal P I X i)
    (hzero : variation 0 = firmPlanOfAllocation X i)
    (radius : ℝ) (hradius : 0 < radius)
    (hadmissible : ∀ ε : ℝ, |ε| < radius →
      FirmFeasible P I X i (variation ε) ∧
      FirmObjectiveWellDefined P (variation ε))
    (d : ℝ)
    (hderiv : HasDerivAt
      (fun ε : ℝ ↦ discountedFirmUtility P (variation ε)) d 0) :
    d = 0 := by
  have hbound := firmOptimal_variation_bound P I X i variation
    hopt hzero radius hradius hadmissible
  have hball : Set.Ioo (-radius) radius ∈ 𝓝 (0 : ℝ) := by
    apply isOpen_Ioo.mem_nhds
    constructor <;> linarith
  have hmax : IsLocalMax
      (fun ε : ℝ ↦ discountedFirmUtility P (variation ε)) 0 := by
    change ∀ᶠ ε : ℝ in 𝓝 (0 : ℝ),
      discountedFirmUtility P (variation ε) ≤
        discountedFirmUtility P (variation 0)
    filter_upwards [hball] with ε hε
    exact hbound ε (abs_lt.mpr hε)
  exact hmax.hasDerivAt_eq_zero hderiv

end ProposedFirmOptimalVariation
end Ventura26LiquidityAllocation
