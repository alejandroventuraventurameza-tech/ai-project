import Ventura26LiquidityAllocation.SourceBinding33NonzeroRemunerationCandidate
import Ventura26LiquidityAllocation.SourceFundingDualPolicyPrimitiveInvarianceCandidate

/-!
# The genuine SOURCE 34-root conditions at nonzero remuneration innovation

The true 33+1 SOURCE residual is defined using the modified L-binding
slack on the first block and the original normalized L funding dual as
the final equation. At any h, the first block is zero iff the 33
ORIGINAL SOURCE binding-branch equations under the intervened Primitives
Pv(h) are zero, given a nonzero L pledge face.

Because the initial monetary intervention changes no CRRA primitive,
the last row is exactly the funding dual evaluated with Pv(h) as well.
This yields a single internally consistent nonzero-policy economic
boundary predicate. At such a source root the L KKT complementarity
conditions follow, but no full equilibrium or existence is proved.
-/

namespace Ventura26LiquidityAllocation

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- The SOURCE funding dual is literally invariant when calculated with
the original or intervened primitives, holding the same economic
coordinates fixed. This is a primitive-field fact, not an IRF. -/
theorem sourceReserveSlice_fundingDual_invariant
    (P : Primitives S) (Z0 : LocalPrefixCoordinates)
    (z : Fin 33 → ℝ) (h : ℝ) :
    localNormalizedCollateralDualL
      (sourceReserveSlicePrimitives P h) (localPrefixLogChart Z0 z) =
    localNormalizedCollateralDualL P (localPrefixLogChart Z0 z) := by
  rfl

#print axioms sourceReserveSlice_fundingDual_invariant

/-- A root of the genuine 34-equation SOURCE boundary system at an
ARBITRARY reserve-remuneration innovation is exactly the pair of:
(i) all 33 ORIGINAL binding-branch SOURCE equations under Pv(h), and
(ii) the same Pv(h) normalized L funding dual equal to zero.

Pledge nondegeneracy is the only extra assumption for the row-5
zero-set normalization. Both sides use the SAME inherited I and tail.
No root existence or Python/SOURCE equality is asserted. -/
theorem sourceAugmented34_nonzeroPolicy_root_iff_original_binding_boundary
    (P : Primitives S) (I : InheritedState)
    (Z0 : LocalPrefixCoordinates)
    (dateOne recurrent : S) (tail : LocalPrefixContinuationRule)
    (z : Fin 33 → ℝ) (h : ℝ)
    (hne : sourceBindingLPledgeFace (sourceReserveSlicePrimitives P h)
      (localPrefixLogChart Z0 z) ≠ 0) :
    ProposedLocalScalarAugmented34Source.augmentedBoundaryZeroResidual
      P I Z0 dateOne recurrent tail z h = (0, 0) ↔
    (∀ row : Fin 33,
      localReducedPrefixResidual LocalPrefixBranch.binding
        (sourceReserveSlicePrimitives P h) I
        (localPrefixLogChart Z0 z) dateOne recurrent tail
        (localPrefixEquationOfIndex row) = 0) ∧
    localNormalizedCollateralDualL
      (sourceReserveSlicePrimitives P h) (localPrefixLogChart Z0 z) = 0 := by
  rw [ProposedLocalScalarAugmented34Source.augmentedBoundaryZeroResidual_eq_zero_iff]
  rw [sourceBinding33_nonzeroPolicy_all_zero_iff
    P I Z0 dateOne recurrent tail z h hne]
  rw [sourceReserveSlice_fundingDual_invariant]

#print axioms sourceAugmented34_nonzeroPolicy_root_iff_original_binding_boundary

/-- Any such source boundary root automatically satisfies L's exact
normalized collateral complementarity (both factors zero). It does
NOT establish all firm-H and bank KKT constraints, feasibility of the
infinite continuation, or a complete competitive equilibrium. -/
theorem sourceAugmented34_nonzeroPolicy_root_implies_L_complementarity
    (P : Primitives S) (I : InheritedState)
    (Z0 : LocalPrefixCoordinates)
    (dateOne recurrent : S) (tail : LocalPrefixContinuationRule)
    (z : Fin 33 → ℝ) (h : ℝ)
    (hne : sourceBindingLPledgeFace (sourceReserveSlicePrimitives P h)
      (localPrefixLogChart Z0 z) ≠ 0)
    (hroot : ProposedLocalScalarAugmented34Source.augmentedBoundaryZeroResidual
      P I Z0 dateOne recurrent tail z h = (0, 0)) :
    LocalScalarComplementarityL
      (sourceReserveSlicePrimitives P h) (localPrefixLogChart Z0 z) := by
  have hboundary :=
    (sourceAugmented34_nonzeroPolicy_root_iff_original_binding_boundary
      P I Z0 dateOne recurrent tail z h hne).mp hroot
  have hraw : localReducedPrefixResidual LocalPrefixBranch.binding
      (sourceReserveSlicePrimitives P h) I
      (localPrefixLogChart Z0 z) dateOne recurrent tail
      LocalPrefixEquation.firmRegimeZeroL = 0 := by
    simpa [localPrefixEquationOfIndex] using hboundary.1 (5 : Fin 33)
  have hslack : localNormalizedSlackL
      (sourceReserveSlicePrimitives P h) (localPrefixLogChart Z0 z) = 0 :=
    (sourceBindingNormalizedSlackL_zero_iff_rawL_zero
      (sourceReserveSlicePrimitives P h) I (localPrefixLogChart Z0 z)
      dateOne recurrent tail hne).mpr hraw
  simp [LocalScalarComplementarityL, hslack, hboundary.2]

#print axioms sourceAugmented34_nonzeroPolicy_root_implies_L_complementarity

end Ventura26LiquidityAllocation
