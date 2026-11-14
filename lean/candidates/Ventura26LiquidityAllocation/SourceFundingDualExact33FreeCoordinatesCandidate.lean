import Ventura26LiquidityAllocation.SourceFundingDualScalarEliminationCandidate
import Mathlib.Data.Fin.Tuple.Basic

/-!
# Exactly 33 free SOURCE unknowns after stationary funding-dual elimination

Fin.removeNth 15 extracts exactly 32 free log coordinates.
Fin.insertNth 15 0 reconstructs a representative, while the
SOURCE analytic L-dual elimination replaces the provisional coordinate
15 with the exact unique scalar-zero value.

Thus the full augmented SOURCE (33+1)-equation existential root
problem is equivalent to 33 residual rows in precisely 32 free log
coordinates plus ONE reserve-remuneration innovation h.

The equivalence is CONDITIONAL on the declared sigma=1 positive
stationary SOURCE chart. It does not prove existence of the reduced
root, any cross-language Python semantic identity, validated
interval bounds, KKT feasibility or dynamic equilibrium.
-/

namespace Ventura26LiquidityAllocation

open ProposedLocalScalarAugmented34Source
open ProposedLocalScalarEconomicSlice

variable {S : Type*} [Fintype S] [DecidableEq S]

noncomputable def sourceFundingDualLift32
    (P : Primitives S) (Z0 : LocalPrefixCoordinates)
    (u : Fin 32 → ℝ) : Fin 33 → ℝ :=
  sourceDualLoanLogEliminate P Z0
    ((15 : Fin 33).insertNth (0 : ℝ) u)

/-- The 33-dimensional analytic lift agrees with the 32 given
free coordinates at all non-loan-rate positions. -/
theorem sourceFundingDualLift32_other
    (P : Primitives S) (Z0 : LocalPrefixCoordinates)
    (u : Fin 32 → ℝ) (i : Fin 32) :
    sourceFundingDualLift32 P Z0 u
      ((15 : Fin 33).succAbove i) = u i := by
  unfold sourceFundingDualLift32
  rw [sourceDualLoanLogEliminate_other
    P Z0 ((15 : Fin 33).insertNth (0 : ℝ) u)
    ((15 : Fin 33).succAbove i) (Fin.succAbove_ne _ _)]
  exact Fin.insertNth_apply_succAbove _ _ _ _

#print axioms sourceFundingDualLift32_other

/-- Insert a temporary value in row 15, then eliminate it:
the resulting SOURCE dual-zero coordinate vector is independent
of the temporary value and of the removed original coordinate. -/
theorem sourceFundingDualLift32_removeNth
    (P : Primitives S) (Z0 : LocalPrefixCoordinates)
    (z : Fin 33 → ℝ) :
    sourceFundingDualLift32 P Z0 ((15 : Fin 33).removeNth z) =
      sourceDualLoanLogEliminate P Z0 z := by
  let z0 : Fin 33 → ℝ :=
    (15 : Fin 33).insertNth (0 : ℝ) ((15 : Fin 33).removeNth z)
  have hother : ∀ i : Fin 33, i ≠ (15 : Fin 33) →
      z0 i = z i := by
    intro i hi
    obtain ⟨j, hj⟩ := Fin.exists_succAbove_eq hi
    subst i
    simp [z0, Fin.removeNth, Fin.insertNth_apply_succAbove]
  have htarget : sourceDualLoanLogTarget P Z0 z0 =
      sourceDualLoanLogTarget P Z0 z := by
    simp only [sourceDualLoanLogTarget]
    rw [hother 8 (by decide), hother 24 (by decide),
      hother 28 (by decide)]
  change sourceDualLoanLogEliminate P Z0 z0 =
    sourceDualLoanLogEliminate P Z0 z
  ext i
  by_cases hi : i = (15 : Fin 33)
  · subst i
    simp [sourceDualLoanLogEliminate, htarget]
  · simpa [sourceDualLoanLogEliminate, hi] using hother i hi

#print axioms sourceFundingDualLift32_removeNth

/-- Exact reduction with ZERO dummy log coordinates:
34 SOURCE augmented unknowns -> 32 genuine independent log
unknowns + one policy innovation h. -/
theorem source34_root_exists_iff_exact_32logs_plus_policy
    (P : Primitives S) (I : InheritedState)
    (Z0 : LocalPrefixCoordinates) (dateOne recurrent : S)
    (tail : LocalPrefixContinuationRule)
    (hsigma : P.entrepreneurRiskAversion = 1)
    (hc_same : Z0.controlsZero.consumptionL = Z0.controlsOne.consumptionL)
    (hc_positive : 0 < Z0.controlsZero.consumptionL)
    (hpi : Z0.controlsOne.inflation = 1)
    (hr : 0 < Z0.controlsZero.loanRate)
    (hbeta : 0 < P.entrepreneurDiscount) :
    (∃ (z : Fin 33 → ℝ) (h : ℝ),
      augmentedBoundaryZeroResidual P I Z0 dateOne recurrent tail z h =
        (0, 0)) ↔
    (∃ (u : Fin 32 → ℝ) (h : ℝ),
      ∀ row : Fin 33,
        localBindingResidualWithSlack P I Z0 dateOne recurrent tail
          (reserveRemunerationSlice 0 h)
          (sourceFundingDualLift32 P Z0 u) row = 0) := by
  rw [source34_root_exists_iff_33rows_on_eliminated_loanLog
    P I Z0 dateOne recurrent tail
    hsigma hc_same hc_positive hpi hr hbeta]
  constructor
  · rintro ⟨z, h, hz⟩
    refine ⟨(15 : Fin 33).removeNth z, h, ?_⟩
    simpa [sourceFundingDualLift32_removeNth] using hz
  · rintro ⟨u, h, hu⟩
    exact ⟨(15 : Fin 33).insertNth (0 : ℝ) u, h, hu⟩

#print axioms source34_root_exists_iff_exact_32logs_plus_policy

end Ventura26LiquidityAllocation
