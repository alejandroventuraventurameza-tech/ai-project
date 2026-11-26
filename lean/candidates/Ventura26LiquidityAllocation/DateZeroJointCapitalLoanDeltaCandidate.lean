import Ventura26LiquidityAllocation.DateZeroJointCapitalLoanUtilityCandidate

/-!
# Exact two-date utility delta for the full joint capital-loan variation

Changing nominal loan face and capital at date zero affects discounted
entrepreneur utility at dates zero and one ONLY. All later terms cancel
identically: no truncation, uncontrolled infinite-horizon differentiation,
or approximate linear payoff is used. This is the analytic foundation
for the binding-tangent Fermat derivative.
-/

namespace Ventura26LiquidityAllocation
namespace ProposedDateZeroJointCapitalLoanDelta

open ProposedDateZeroJointCapitalLoanDeviation
open ProposedDateZeroJointCapitalLoanUtility

variable {S : Type*} [Fintype S] [DecidableEq S]

private theorem tsum_eq_two_terms_and_tail
    (f : ℕ → ℝ) (hf : Summable f) :
    (∑' n : ℕ, f n) =
      f 0 + f 1 + ∑' n : ℕ, f (n + 2) := by
  have htail : Summable (fun n : ℕ => f (n + 1)) :=
    (summable_nat_add_iff 1).mpr hf
  calc
    (∑' n : ℕ, f n) =
        f 0 + (∑' n : ℕ, f (n + 1)) := hf.tsum_eq_zero_add
    _ = f 0 + (f 1 + ∑' n : ℕ, f (n + 2)) := by
      rw [htail.tsum_eq_zero_add]
    _ = f 0 + f 1 + ∑' n : ℕ, f (n + 2) := by ring

/-- Discounted utility difference equals exactly the two changed utility
    terms for any joint loan-capital deviation and arbitrary Markov support. -/
theorem discountedFirmUtility_jointVariation_delta_eq
    (P : Primitives S) (X : Allocation S) (i : FirmType)
    (p : FirmPlan S) (dk db : ℝ)
    (hwell : FirmObjectiveWellDefined P p) :
    discountedFirmUtility P (jointDateZeroVariation P X i p dk db) -
      discountedFirmUtility P p =
      (firmUtilityTerm P (jointDateZeroVariation P X i p dk db) 0 -
        firmUtilityTerm P p 0) +
      (firmUtilityTerm P (jointDateZeroVariation P X i p dk db) 1 -
        firmUtilityTerm P p 1) := by
  let f : ℕ → ℝ :=
    firmUtilityTerm P (jointDateZeroVariation P X i p dk db)
  let g : ℕ → ℝ := firmUtilityTerm P p
  have hg : Summable g := hwell
  have hf : Summable f :=
    (jointVariation_objectiveWellDefined_iff P X i p dk db).2 hwell
  have hsplitf := tsum_eq_two_terms_and_tail f hf
  have hsplitg := tsum_eq_two_terms_and_tail g hg
  have htail : (∑' n : ℕ, f (n + 2)) =
      (∑' n : ℕ, g (n + 2)) :=
    tsum_congr (fun n => jointUtilityTerm_later_eq P X i p dk db n)
  change (∑' n, f n) - (∑' n, g n) =
    (f 0 - g 0) + (f 1 - g 1)
  rw [hsplitf, hsplitg, htail]
  ring

end ProposedDateZeroJointCapitalLoanDelta
end Ventura26LiquidityAllocation
