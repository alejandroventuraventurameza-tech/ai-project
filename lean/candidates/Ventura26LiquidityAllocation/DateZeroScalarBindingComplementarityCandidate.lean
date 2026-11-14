import Ventura26LiquidityAllocation.DateZeroScalarKKTFromOptimalCandidate

/-!
# A scalar KKT-row complementarity certificate at a binding root constraint

For a source DateZeroBindingBorrower with exactly one admissible successor,
the robust collateral slack is zero at that successor. Combining the
one-sided FirmOptimal Euler inequality with the scalar residual construction
yields a nonnegative scalar multiplier, a zero capital Euler residual in a
dual-replaced carrier, and complementary slackness for the ORIGINAL primal
collateral quantity.

The constructed multiplier is NOT proved equal to X.collateralDual; a full
KKT system, multiplier interpretation, and competitive equilibrium existence
still require additional theorems.
-/

namespace Ventura26LiquidityAllocation
namespace ProposedDateZeroScalarBindingComplementarity

open ProposedDateZeroScalarKKTFromOptimal
open ProposedContinuationContractAudit

variable {S : Type*} [Fintype S] [DecidableEq S]

noncomputable def rootCollateralSlack
    (P : Primitives S) (X : Allocation S) (i : FirmType) (s : S) : ℝ :=
  P.pledgeability i * (1 - P.depreciation) *
    (X.inflation 1 (childHistory (rootHistory P.tree) s) *
      X.capitalPrice 1 (childHistory (rootHistory P.tree) s)) *
        X.capital i 0 (rootHistory P.tree) -
    X.loanRate 0 (rootHistory P.tree) *
      X.loan i 0 (rootHistory P.tree)

/-- In the single-successor regime, a source binding root collateral
    constraint binds specifically at that successor. -/
theorem rootCollateralSlack_zero_of_binding_unique_successor
    (P : Primitives S) (X : Allocation S) (i : FirmType) (s : S)
    (hbinding : DateZeroBindingBorrower P X i)
    (hothers : ∀ v : S, v ≠ s →
      P.tree.transition P.tree.initial v = 0) :
    rootCollateralSlack P X i s = 0 := by
  obtain ⟨v, hv, heq⟩ :=
    (hbinding (rootHistory P.tree)).2.2.2
  have hvpos : 0 < P.tree.transition P.tree.initial v := by
    simpa [rootHistory, currentState] using hv
  have hvs : v = s := by
    by_contra hvne
    have hz := hothers v hvne
    rw [hz] at hvpos
    exact (lt_irrefl (0 : ℝ)) hvpos
  subst v
  unfold rootCollateralSlack
  exact sub_eq_zero.mpr heq.symm

/-- The scalar capital Euler-row and complementary-slackness properties
    can be witnessed together. They do not identify the SOURCE dual. -/
theorem firmOptimal_binding_exists_scalarEulerComplementarity
    (P : Primitives S) (I : InheritedState)
    (X : Allocation S) (i : FirmType) (s : S)
    (hopt : FirmOptimal P I X i)
    (hbinding : DateZeroBindingBorrower P X i)
    (hcapital : ∀ h : History S 0,
      FirmHistoryAdmissible P 0 h → 0 < X.capital i 0 h)
    (hcoeff : ∀ h : History S 0,
      FirmHistoryAdmissible P 0 h → ∀ v : S,
      0 < P.tree.transition (currentState h) v →
      0 ≤ P.pledgeability i * (1 - P.depreciation) *
        (X.inflation 1 (childHistory h v) *
          X.capitalPrice 1 (childHistory h v)))
    (hw0 : P.tree.historyWeight 0 (rootHistory P.tree) = 1)
    (hz0 : ∀ h : History S 0, h ≠ rootHistory P.tree →
      P.tree.historyWeight 0 h = 0)
    (hw1 : P.tree.historyWeight 1
      (childHistory (rootHistory P.tree) s) = 1)
    (hz1 : ∀ h : History S 1,
      h ≠ childHistory (rootHistory P.tree) s →
      P.tree.historyWeight 1 h = 0)
    (hothers : ∀ v : S, v ≠ s →
      P.tree.transition P.tree.initial v = 0)
    (hunit : 0 < ProposedProposition42KKTIdentification.capitalEulerCollateralUnit
      P X i 0 (rootHistory P.tree) s) :
    ∃ mu : ℝ, 0 ≤ mu ∧
      localFirmCapitalEulerResidual P
        (replaceCollateralDual X (fun _ _ _ => mu))
        i 0 (rootHistory P.tree) s = 0 ∧
      0 ≤ rootCollateralSlack P X i s ∧
      mu * rootCollateralSlack P X i s = 0 := by
  obtain ⟨mu, hmu, hrow⟩ :=
    firmOptimal_oneSided_exists_nonnegative_scalarCapitalMultiplier
      P I X i s hopt hcapital hcoeff hw0 hz0 hw1 hz1 hunit
  have hbind :
      rootCollateralSlack P X i s = 0 :=
    rootCollateralSlack_zero_of_binding_unique_successor
      P X i s hbinding hothers
  refine ⟨mu, hmu, hrow, ?_, ?_⟩
  · rw [hbind]
  · rw [hbind]
    ring

end ProposedDateZeroScalarBindingComplementarity
end Ventura26LiquidityAllocation
