import Ventura26LiquidityAllocation.FirmOptimalVariationCandidate

/-!
# Non-identification of the source dual even within the binding-borrower regime

The source binding predicate asks for a strictly positive stored dual, but the
original firm feasibility, terminal conditions, objective and optimality are
independent of that field. Replacing the dual by another positive process
preserves both literal FirmOptimal and the binding-borrower label.

Hence an optimal binding allocation can have a nonzero source capital-Euler
residual while agreeing with the original allocation on every primal field.
This is a semantic obstruction, not a rejection of the economic KKT conditions.
No source/checkpoint files or theorem hypotheses are modified.
-/

namespace Ventura26LiquidityAllocation
namespace ProposedDateZeroBindingDualFreedom

open ProposedContinuationContractAudit
open ProposedFirmOptimalVariation
open ProposedProposition42KKTIdentification

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- Binding as defined in the source is invariant under any strictly positive
replacement of the stored dual, since the primal collateral face is unchanged. -/
theorem bindingBorrower_replaceCollateralDual_of_positive
    (P : Primitives S) (X : Allocation S) (i : FirmType)
    (dual : FirmType → AdaptedProcess S)
    (hbinding : DateZeroBindingBorrower P X i)
    (hpositive : ∀ h : History S 0, 0 < dual i 0 h) :
    DateZeroBindingBorrower P (replaceCollateralDual X dual) i := by
  intro h
  obtain ⟨hloan, _hdual, hcollateral, hactive⟩ := hbinding h
  exact ⟨hloan, hpositive h, hcollateral, hactive⟩

/-- Even increasing the source dual everywhere preserves the binding label. -/
theorem bindingBorrower_shiftCollateralDual_of_nonneg
    (P : Primitives S) (X : Allocation S) (i : FirmType)
    (epsilon : ℝ) (hepsilon : 0 ≤ epsilon)
    (hbinding : DateZeroBindingBorrower P X i) :
    DateZeroBindingBorrower P (shiftCollateralDual X epsilon) i := by
  change DateZeroBindingBorrower P
    (replaceCollateralDual X
      (fun j t h => X.collateralDual j t h + epsilon)) i
  apply bindingBorrower_replaceCollateralDual_of_positive P X
    (fun j t h => X.collateralDual j t h + epsilon) i hbinding
  intro h
  have hp : 0 < X.collateralDual i 0 h := (hbinding h).2.1
  linarith

/-- The positive-dual binding classification cannot supply the missing source
Euler row: a counterexample remains in the same primal-equivalence class. -/
theorem exists_bindingFirmOptimal_primalSame_without_sourceCapitalEuler
    (P : Primitives S) (I : InheritedState) (X : Allocation S)
    (i : FirmType) (s : S)
    (hopt : FirmOptimal P I X i)
    (hbinding : DateZeroBindingBorrower P X i)
    (hunit : capitalEulerCollateralUnit P X i 0
      (rootHistory P.tree) s ≠ 0) :
    ∃ Y : Allocation S,
      FirmOptimal P I Y i ∧
      DateZeroBindingBorrower P Y i ∧
      AllocationPrimalAgreementOnSupport P X Y ∧
      localFirmCapitalEulerResidual P Y i 0 (rootHistory P.tree) s ≠ 0 := by
  by_cases hrow :
      localFirmCapitalEulerResidual P X i 0 (rootHistory P.tree) s = 0
  · let dual : FirmType → AdaptedProcess S :=
      fun j t h => X.collateralDual j t h + 1
    let Y : Allocation S := replaceCollateralDual X dual
    have hoptY : FirmOptimal P I Y i :=
      (firmOptimal_replaceCollateralDual_iff P I X dual i).2 hopt
    have hpositive : ∀ h : History S 0, 0 < dual i 0 h := by
      intro h
      have hp : 0 < X.collateralDual i 0 h := (hbinding h).2.1
      dsimp [dual]
      linarith
    have hbindingY : DateZeroBindingBorrower P Y i :=
      bindingBorrower_replaceCollateralDual_of_positive
        P X i dual hbinding hpositive
    have hprimal : AllocationPrimalAgreementOnSupport P X Y :=
      primalAgreement_replaceCollateralDual P X dual
    refine ⟨Y, hoptY, hbindingY, hprimal, ?_⟩
    intro hY
    have heq := capitalEuler_dual_unique_of_same_primal
      P X dual i 0 (rootHistory P.tree) s hrow hY hunit
    change X.collateralDual i 0 (rootHistory P.tree) =
      X.collateralDual i 0 (rootHistory P.tree) + 1 at heq
    linarith
  · refine ⟨X, hopt, hbinding, ?_, hrow⟩
    intro radius hradius
    change AllocationFullNear P radius
      (eraseCollateralDual X) (eraseCollateralDual X)
    exact allocationFullNear_refl P radius (eraseCollateralDual X) hradius

/-- No universal source-dual Euler identification follows from optimality,
the binding label and even exact agreement of observable primal variables. -/
theorem not_all_bindingFirmOptimal_have_sourceCapitalEuler
    (P : Primitives S) (I : InheritedState) (X : Allocation S)
    (i : FirmType) (s : S)
    (hopt : FirmOptimal P I X i)
    (hbinding : DateZeroBindingBorrower P X i)
    (hunit : capitalEulerCollateralUnit P X i 0
      (rootHistory P.tree) s ≠ 0) :
    ¬ (∀ Y : Allocation S,
        FirmOptimal P I Y i →
        DateZeroBindingBorrower P Y i →
        AllocationPrimalAgreementOnSupport P X Y →
        localFirmCapitalEulerResidual P Y i 0 (rootHistory P.tree) s = 0) := by
  intro hall
  obtain ⟨Y, hY, hbindingY, hprimal, hne⟩ :=
    exists_bindingFirmOptimal_primalSame_without_sourceCapitalEuler
      P I X i s hopt hbinding hunit
  exact hne (hall Y hY hbindingY hprimal)

end ProposedDateZeroBindingDualFreedom
end Ventura26LiquidityAllocation
