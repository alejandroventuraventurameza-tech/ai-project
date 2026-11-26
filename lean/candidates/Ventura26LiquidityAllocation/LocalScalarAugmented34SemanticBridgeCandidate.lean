import Ventura26LiquidityAllocation.LocalScalarAugmented34FullBothCandidate

/-!
# Formal 34-row semantic contract between a surrogate and the source

A validated numerical interval box may yield a zero of a surrogate G
different from Lean's literal source residual H. The correct bridge is
pointwise equality of ZERO SETS for all 33 economic rows and the extra
firm-L funding dual, ONLY inside an explicit domain predicate. It
must include the certified Banach root and the positive source box.

This module DOES NOT assume or prove that the current Python G obeys
this contract. The contract remains an explicit, unfilled hypothesis.
It also DOES NOT create a Banach root in Lean. Its only role is to
show exactly how a certified surrogate zero would transfer to H and
then to the original B/S prefix rows once source equivalence is proved.
-/

namespace Ventura26LiquidityAllocation
namespace ProposedLocalScalarAugmented34SemanticBridge

open ProposedLocalScalarAugmented34Source
open ProposedLocalScalarAugmented34FullBoth
open ProposedLocalScalarEconomicSlice

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- Pointwise equivalence of all 34 source and surrogate equations.
There are 33 coordinate rows and an independent final funding dual
row; the numerical source mapping must justify EVERY component. -/
def SourceAugmented34ZeroSetAgreement
    (P : Primitives S) (I : InheritedState) (Z0 : LocalPrefixCoordinates)
    (dateOne recurrent : S) (tail : LocalPrefixContinuationRule)
    (Domain : (Fin 33 → ℝ) → ℝ → Prop)
    (G : (Fin 33 → ℝ) → ℝ → (Fin 33 → ℝ) × ℝ) : Prop :=
  ∀ z h, Domain z h →
    (∀ row : Fin 33,
      (G z h).1 row = 0 ↔
        (augmentedBoundaryZeroResidual
          P I Z0 dateOne recurrent tail z h).1 row = 0) ∧
    ((G z h).2 = 0 ↔
      (augmentedBoundaryZeroResidual
        P I Z0 dateOne recurrent tail z h).2 = 0)

/-- A zero of a surrogate with all 34 zero-set identities proved is
a zero of the EXACT Lean source H. This statement requires the
surrogate root as evidence; an interval JSON alone is not such a
formal Lean witness. -/
theorem source_augmented_zero_of_surrogate_zero
    (P : Primitives S) (I : InheritedState) (Z0 : LocalPrefixCoordinates)
    (dateOne recurrent : S) (tail : LocalPrefixContinuationRule)
    (Domain : (Fin 33 → ℝ) → ℝ → Prop)
    (G : (Fin 33 → ℝ) → ℝ → (Fin 33 → ℝ) × ℝ)
    (hmatch : SourceAugmented34ZeroSetAgreement
      P I Z0 dateOne recurrent tail Domain G)
    (z : Fin 33 → ℝ) (h : ℝ)
    (hDomain : Domain z h)
    (hG : G z h = (0, 0)) :
    augmentedBoundaryZeroResidual P I Z0
      dateOne recurrent tail z h = (0, 0) := by
  obtain ⟨hrows, hdual⟩ := hmatch z h hDomain
  apply Prod.ext
  · funext row
    have hzero : (G z h).1 row = 0 := by
      have hfirst := congrArg Prod.fst hG
      simpa using congrFun hfirst row
    exact (hrows row).mp hzero
  · have hzero : (G z h).2 = 0 := by
      simpa using congrArg Prod.snd hG
    exact hdual.mp hzero

/-- The precise conditional route from a surrogate 34-zero and its
source zero-set bridge to all 33 ORIGINAL binding and 33 ORIGINAL
slack prefix equations. Both sets hold AT THE SAME POINT. -/
theorem original_S_B_prefix_from_surrogate_zero
    (P : Primitives S) (I : InheritedState) (Z0 : LocalPrefixCoordinates)
    (dateOne recurrent : S) (tail : LocalPrefixContinuationRule)
    (Domain : (Fin 33 → ℝ) → ℝ → Prop)
    (G : (Fin 33 → ℝ) → ℝ → (Fin 33 → ℝ) × ℝ)
    (hmatch : SourceAugmented34ZeroSetAgreement
      P I Z0 dateOne recurrent tail Domain G)
    (z : Fin 33 → ℝ) (h : ℝ)
    (hDomain : Domain z h)
    (hG : G z h = (0, 0))
    (hbase : LocalPrefixCoordinatesPositive Z0)
    (hpledge : 0 < P.pledgeability FirmType.L)
    (hdepr : P.depreciation < 1) :
    let y := reserveRemunerationSlice 0 h
    let Pv := initialIntervenedPrimitives P (localScalarParameterIntervention y)
    let Z := localPrefixLogChart Z0 z
    (∀ row : Fin 33,
      localReducedPrefixResidual LocalPrefixBranch.binding Pv I Z
        dateOne recurrent tail (localPrefixEquationOfIndex row) = 0) ∧
    (∀ row : Fin 33,
      localReducedPrefixResidual LocalPrefixBranch.slack Pv I Z
        dateOne recurrent tail (localPrefixEquationOfIndex row) = 0) := by
  have hsource := source_augmented_zero_of_surrogate_zero
    P I Z0 dateOne recurrent tail Domain G hmatch z h hDomain hG
  exact augmented_zero_implies_all_original_S_and_B_prefix_rows
    P I Z0 dateOne recurrent tail z h hbase hpledge hdepr hsource

#print axioms source_augmented_zero_of_surrogate_zero
#print axioms original_S_B_prefix_from_surrogate_zero

end ProposedLocalScalarAugmented34SemanticBridge
end Ventura26LiquidityAllocation
