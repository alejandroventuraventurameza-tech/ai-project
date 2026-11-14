import Ventura26LiquidityAllocation.DateZeroJointBindingSharedDualCandidate
import Ventura26LiquidityAllocation.DateZeroBindingDualFreedomCandidate

/-!
# A genuine primal-equivalent capital/loan KKT carrier for a binding borrower

The preceding joint tangent proof constructs one common nonnegative scalar
shadow multiplier from the source infinite-horizon FirmOptimal. Here we
instantiate an Allocation whose collateralDual field stores precisely that
scalar. The resulting Allocation preserves every primal observable and
literal FirmOptimal, satisfies both root capital/loan marginal equations, and
has complementary slackness. The scalar is uniquely determined by the
positive collateral coefficient and the primal capital gap.

Crucial distinction: this construction does NOT identify the dual originally
stored in X. A strictly positive reconstructed scalar—and hence preservation
of the source's *dual-positive* binding label—requires a strictly positive
primal capital gap. This is an explicit additional condition, not something
inferred from the original arbitrarily positive stored dual.
-/

namespace Ventura26LiquidityAllocation
namespace ProposedDateZeroBindingDualRepair

open ProposedContinuationContractAudit
open ProposedFirmOptimalVariation
open ProposedProposition42KKTIdentification
open ProposedDateZeroJointBindingSharedDual
open ProposedDateZeroJointBindingMarginalBalance
open ProposedDateZeroScalarBindingComplementarity
open ProposedDateZeroBindingDualFreedom

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- A concrete dual-normalized Allocation witness with unchanged primals,
source optimality, BOTH capital and loan root KKT rows, and complementarity. -/
theorem firmOptimal_binding_exists_primalEquivalent_jointKKT_carrier
    (P : Primitives S) (I : InheritedState)
    (X : Allocation S) (i : FirmType)
    (dateOne recurrent : S)
    (hcalendar : DeterministicBridgeCalendar P dateOne recurrent)
    (hopt : FirmOptimal P I X i)
    (hbinding : DateZeroBindingBorrower P X i)
    (hcapital : ∀ h : History S 0,
      FirmHistoryAdmissible P 0 h → 0 < X.capital i 0 h)
    (hR : 0 < X.loanRate 0 (rootHistory P.tree))
    (hGamma : 0 < capitalEulerCollateralUnit
      P X i 0 (rootHistory P.tree) dateOne)
    (hpi : X.inflation 1
      (childHistory (rootHistory P.tree) dateOne) ≠ 0) :
    ∃ (mu : ℝ) (Y : Allocation S),
      0 ≤ mu ∧
      Y = replaceCollateralDual X (fun _ _ _ => mu) ∧
      FirmOptimal P I Y i ∧
      AllocationPrimalAgreementOnSupport P X Y ∧
      localFirmCapitalEulerResidual P Y i 0
        (rootHistory P.tree) dateOne = 0 ∧
      dateZeroLoanPrimalGap P Y i dateOne =
        Y.collateralDual i 0 (rootHistory P.tree) *
          Y.loanRate 0 (rootHistory P.tree) ∧
      Y.collateralDual i 0 (rootHistory P.tree) *
        rootCollateralSlack P Y i dateOne = 0 ∧
      mu = capitalEulerPrimalGap P X i 0
        (rootHistory P.tree) dateOne /
        capitalEulerCollateralUnit P X i 0
          (rootHistory P.tree) dateOne := by
  obtain ⟨mu, hmu, hcapitalGap, hloanGap, hcomp⟩ :=
    firmOptimal_sourceCalendar_binding_exists_shared_capitalLoanMultiplier
      P I X i dateOne recurrent hcalendar hopt hbinding hcapital hR hGamma hpi
  let dual : FirmType → AdaptedProcess S := fun _ _ _ => mu
  let Y : Allocation S := replaceCollateralDual X dual
  have hoptY : FirmOptimal P I Y i :=
    (firmOptimal_replaceCollateralDual_iff P I X dual i).2 hopt
  have hprimal : AllocationPrimalAgreementOnSupport P X Y :=
    primalAgreement_replaceCollateralDual P X dual
  have hrow : localFirmCapitalEulerResidual P Y i 0
      (rootHistory P.tree) dateOne = 0 := by
    rw [capitalEulerResidual_eq_primalGap_sub_dual]
    change capitalEulerPrimalGap P X i 0 (rootHistory P.tree) dateOne -
      mu * capitalEulerCollateralUnit P X i 0
        (rootHistory P.tree) dateOne = 0
    linarith [hcapitalGap]
  have hloan : dateZeroLoanPrimalGap P Y i dateOne =
      Y.collateralDual i 0 (rootHistory P.tree) *
        Y.loanRate 0 (rootHistory P.tree) := by
    change dateZeroLoanPrimalGap P X i dateOne =
      mu * X.loanRate 0 (rootHistory P.tree)
    exact hloanGap
  have hcomplementarity :
      Y.collateralDual i 0 (rootHistory P.tree) *
        rootCollateralSlack P Y i dateOne = 0 := by
    change mu * rootCollateralSlack P X i dateOne = 0
    exact hcomp
  have hratio : mu = capitalEulerPrimalGap P X i 0
      (rootHistory P.tree) dateOne /
        capitalEulerCollateralUnit P X i 0
          (rootHistory P.tree) dateOne := by
    apply (eq_div_iff (ne_of_gt hGamma)).2
    rw [hcapitalGap]
  exact ⟨mu, Y, hmu, rfl, hoptY, hprimal,
    hrow, hloan, hcomplementarity, hratio⟩

/-- At a nonzero collateral coefficient there is at most one scalar constant
carrier satisfying the exact source capital Euler row at this node. -/
theorem normalized_rootCapitalDual_unique
    (P : Primitives S) (X : Allocation S) (i : FirmType)
    (t : ℕ) (h : History S t) (s : S)
    (hunit : capitalEulerCollateralUnit P X i t h s ≠ 0)
    (mu nu : ℝ)
    (hmu : localFirmCapitalEulerResidual P
      (replaceCollateralDual X (fun _ _ _ => mu)) i t h s = 0)
    (hnu : localFirmCapitalEulerResidual P
      (replaceCollateralDual X (fun _ _ _ => nu)) i t h s = 0) :
    mu = nu := by
  have heq := capitalEuler_dual_unique_of_same_primal P
    (replaceCollateralDual X (fun _ _ _ => mu))
    (fun _ _ _ => nu) i t h s hmu (by
      change localFirmCapitalEulerResidual P
        (replaceCollateralDual X (fun _ _ _ => nu)) i t h s = 0
      exact hnu) (by
      change capitalEulerCollateralUnit P X i t h s ≠ 0
      exact hunit)
  change mu = nu at heq
  exact heq

/-- The repaired carrier is again a source-defined binding borrower when
the PRIMAL capital gap is strictly positive. Strict complementarity is not
deduced from a positive *original* stored dual. -/
theorem firmOptimal_strictPrimalGap_exists_binding_jointKKT_carrier
    (P : Primitives S) (I : InheritedState)
    (X : Allocation S) (i : FirmType)
    (dateOne recurrent : S)
    (hcalendar : DeterministicBridgeCalendar P dateOne recurrent)
    (hopt : FirmOptimal P I X i)
    (hbinding : DateZeroBindingBorrower P X i)
    (hcapital : ∀ h : History S 0,
      FirmHistoryAdmissible P 0 h → 0 < X.capital i 0 h)
    (hR : 0 < X.loanRate 0 (rootHistory P.tree))
    (hGamma : 0 < capitalEulerCollateralUnit
      P X i 0 (rootHistory P.tree) dateOne)
    (hpi : X.inflation 1
      (childHistory (rootHistory P.tree) dateOne) ≠ 0)
    (hstrict : 0 < capitalEulerPrimalGap P X i 0
      (rootHistory P.tree) dateOne) :
    ∃ (mu : ℝ) (Y : Allocation S),
      0 < mu ∧
      Y = replaceCollateralDual X (fun _ _ _ => mu) ∧
      FirmOptimal P I Y i ∧
      DateZeroBindingBorrower P Y i ∧
      localFirmCapitalEulerResidual P Y i 0
        (rootHistory P.tree) dateOne = 0 ∧
      dateZeroLoanPrimalGap P Y i dateOne =
        mu * Y.loanRate 0 (rootHistory P.tree) ∧
      mu * rootCollateralSlack P Y i dateOne = 0 := by
  obtain ⟨mu, Y, _hmu, hY, hoptY, _hprimal, hrow,
    hloan, hcomp, hratio⟩ :=
    firmOptimal_binding_exists_primalEquivalent_jointKKT_carrier
      P I X i dateOne recurrent hcalendar hopt hbinding hcapital
        hR hGamma hpi
  have hmupos : 0 < mu := by
    rw [hratio]
    exact div_pos hstrict hGamma
  have hbindingY : DateZeroBindingBorrower P Y i := by
    rw [hY]
    exact bindingBorrower_replaceCollateralDual_of_positive
      P X i (fun _ _ _ => mu) hbinding (fun _ => hmupos)
  have hloan' : dateZeroLoanPrimalGap P Y i dateOne =
      mu * Y.loanRate 0 (rootHistory P.tree) := by
    have hdual : Y.collateralDual i 0 (rootHistory P.tree) = mu := by
      rw [hY]
      rfl
    simpa only [hdual] using hloan
  have hcomp' : mu * rootCollateralSlack P Y i dateOne = 0 := by
    have hdual : Y.collateralDual i 0 (rootHistory P.tree) = mu := by
      rw [hY]
      rfl
    simpa only [hdual] using hcomp
  exact ⟨mu, Y, hmupos, hY, hoptY, hbindingY, hrow, hloan', hcomp'⟩

end ProposedDateZeroBindingDualRepair
end Ventura26LiquidityAllocation
