import Ventura26LiquidityAllocation.Proposition42PrimalRepairCandidate

/-!
# Genuine separation of collateral regimes modulo free duals

The original two-branch statement distinguishes strict collateral slack
for firm L in S from a binding constraint for L in B. This file demonstrates
that the two regimes cannot be equal even after erasing collateralDual
provided they are compared on all admissible histories.

The proof uses the economic inequalities in DateZeroSlackBorrower and
DateZeroBindingBorrower, and the primitive positive-probability support.
No existence of an equilibrium, continuation, KKT necessity/sufficiency,
or uniqueness of equilibrium is presupposed.

The final normalized Euler identity identifies a scalar multiplier
conditional on a marginal equation; it does NOT identify the unconstrained
Allocation.collateralDual field or prove KKT for CompetitiveEquilibrium.

This is a candidate module. Do not claim kernel verification until CI succeeds.
-/

namespace Ventura26LiquidityAllocation
namespace ProposedProposition42PrimalSeparation

open ProposedContinuationContractAudit
open ProposedProposition42PrimalRepair

variable {S : Type*} [Fintype S] [DecidableEq S]

private theorem eq_of_abs_difference_lt_every_pos_radius
    (x y : ℝ) (h : ∀ radius : ℝ, 0 < radius → |x - y| < radius) :
    x = y := by
  by_contra hxy
  have hpos : 0 < |x - y| := abs_pos.mpr (sub_ne_zero.mpr hxy)
  exact (lt_irrefl (|x - y|)) (h _ hpos)

/-- Economically relevant field distances extracted from the source's
    FULL neighborhood after dropping only the freely carried multiplier. -/
private theorem primal_fields_near
    (P : Primitives S) (radius : ℝ) (X Y : Allocation S)
    (t : ℕ) (h : History S t)
    (hn : AllocationPrimalNear P radius X Y)
    (hadm : FirmHistoryAdmissible P t h) :
    (∀ i, |X.capital i t h - Y.capital i t h| < radius) ∧
    (∀ i, |X.loan i t h - Y.loan i t h| < radius) ∧
    |X.inflation t h - Y.inflation t h| < radius ∧
    |X.capitalPrice t h - Y.capitalPrice t h| < radius ∧
    |X.loanRate t h - Y.loanRate t h| < radius := by
  rcases (hn.2 t h hadm) with
    ⟨_, _, _, hcapital, _, _, hloan, _, _, _, _, _, _, hinflation,
      hcapitalPrice, hloanRate, _⟩
  exact ⟨hcapital, hloan, hinflation, hcapitalPrice, hloanRate⟩

/-- Equality on admissible histories of the five primal coordinates
    entering the firm's robust collateral inequality. -/
theorem primal_agreement_collateral_fields_eq
    (P : Primitives S) (X Y : Allocation S)
    (t : ℕ) (h : History S t)
    (hadm : FirmHistoryAdmissible P t h)
    (hag : AllocationPrimalAgreementOnSupport P X Y) :
    (∀ i, X.capital i t h = Y.capital i t h) ∧
    (∀ i, X.loan i t h = Y.loan i t h) ∧
    X.inflation t h = Y.inflation t h ∧
    X.capitalPrice t h = Y.capitalPrice t h ∧
    X.loanRate t h = Y.loanRate t h := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro i
    apply eq_of_abs_difference_lt_every_pos_radius
    intro radius hradius
    exact (primal_fields_near P radius X Y t h (hag radius hradius) hadm).1 i
  · intro i
    apply eq_of_abs_difference_lt_every_pos_radius
    intro radius hradius
    exact (primal_fields_near P radius X Y t h (hag radius hradius) hadm).2.1 i
  · apply eq_of_abs_difference_lt_every_pos_radius
    intro radius hradius
    exact (primal_fields_near P radius X Y t h (hag radius hradius) hadm).2.2.1
  · apply eq_of_abs_difference_lt_every_pos_radius
    intro radius hradius
    exact (primal_fields_near P radius X Y t h (hag radius hradius) hadm).2.2.2.1
  · apply eq_of_abs_difference_lt_every_pos_radius
    intro radius hradius
    exact (primal_fields_near P radius X Y t h (hag radius hradius) hadm).2.2.2.2

/-- The deterministic initial history has probability one. -/
private theorem root_history_admissible (P : Primitives S) :
    FirmHistoryAdmissible P 0 (rootHistory P.tree) := by
  simp [FirmHistoryAdmissible, FiniteMarkovTree.historyWeight, rootHistory,
    currentState]

/-- An initially reachable positive-probability successor remains in
    the domain on which full-primal coincidence is asserted. -/
private theorem child_history_admissible
    (P : Primitives S) (s : S)
    (hs : 0 < P.tree.transition P.tree.initial s) :
    FirmHistoryAdmissible P 1 (childHistory (rootHistory P.tree) s) := by
  have hprev :
      previousHistory (childHistory (rootHistory P.tree) s) =
        rootHistory P.tree := by
    funext j
    rfl
  change 0 <
    (FiniteMarkovTree.historyWeight P.tree 0
      (previousHistory (childHistory (rootHistory P.tree) s))) *
    P.tree.transition
      (currentState (previousHistory (childHistory (rootHistory P.tree) s)))
      (currentState (childHistory (rootHistory P.tree) s))
  rw [hprev]
  change 0 < FiniteMarkovTree.historyWeight P.tree 0 (rootHistory P.tree) *
    P.tree.transition P.tree.initial s
  simpa [FiniteMarkovTree.historyWeight, rootHistory, currentState] using hs

/-- S and B are economically different on support: no arbitrary difference
    in free collateral-dual certificates is used for this conclusion. -/
theorem strict_slack_and_binding_primal_disjoint
    (P : Primitives S) (Xs Xb : Allocation S)
    (hslack : DateZeroSlackBorrower P Xs FirmType.L)
    (hbinding : DateZeroBindingBorrower P Xb FirmType.L) :
    ¬ AllocationPrimalAgreementOnSupport P Xs Xb := by
  intro hag
  let h0 : History S 0 := rootHistory P.tree
  have hadm0 : FirmHistoryAdmissible P 0 h0 :=
    root_history_admissible P
  rcases hbinding h0 with ⟨_, _, _, s, hspos, heq⟩
  have hadm1 : FirmHistoryAdmissible P 1 (childHistory h0 s) :=
    child_history_admissible P s hspos
  obtain ⟨hcap0, hloan0, _, _, hrate0⟩ :=
    primal_agreement_collateral_fields_eq P Xs Xb 0 h0 hadm0 hag
  obtain ⟨_, _, hinfl1, hprice1, _⟩ :=
    primal_agreement_collateral_fields_eq
      P Xs Xb 1 (childHistory h0 s) hadm1 hag
  have hstrict := (hslack h0).2.2 s hspos
  rw [hrate0, hloan0 FirmType.L, hcap0 FirmType.L,
    hinfl1, hprice1] at hstrict
  exact (ne_of_lt hstrict) heq

/-- For the explicit finite-prefix scalar multiplier equation, the reduced
    dual is uniquely fixed by the observable consumption/return terms.
    This is conditional on the Euler equation, not an equilibrium KKT result. -/
theorem reduced_dual_unique_of_euler
    (P : Primitives S) (Z : LocalPrefixCoordinates) (mu : ℝ)
    (heuler :
      1 / Z.controlsZero.loanRate =
        (P.entrepreneurDiscount *
          crraMarginal P.entrepreneurRiskAversion Z.controlsOne.consumptionL /
          crraMarginal P.entrepreneurRiskAversion Z.controlsZero.consumptionL) /
          Z.controlsOne.inflation + mu) :
    mu = localNormalizedCollateralDualL P Z := by
  unfold localNormalizedCollateralDualL
  linarith

/-- Scalar complementary slackness: strictly slack collateral forces
    the reduced multiplier to vanish. -/
theorem reduced_dual_zero_of_strict_slack
    (P : Primitives S) (Z : LocalPrefixCoordinates)
    (hkkt : LocalScalarComplementarityL P Z)
    (hs : 0 < localNormalizedSlackL P Z) :
    localNormalizedCollateralDualL P Z = 0 := by
  exact (mul_eq_zero.mp hkkt.2.2).resolve_left (ne_of_gt hs)

/-- A strictly positive reduced multiplier forces a binding constraint. -/
theorem reduced_slack_zero_of_positive_dual
    (P : Primitives S) (Z : LocalPrefixCoordinates)
    (hkkt : LocalScalarComplementarityL P Z)
    (hmu : 0 < localNormalizedCollateralDualL P Z) :
    localNormalizedSlackL P Z = 0 := by
  exact (mul_eq_zero.mp hkkt.2.2).resolve_right (ne_of_gt hmu)

end ProposedProposition42PrimalSeparation
end Ventura26LiquidityAllocation
