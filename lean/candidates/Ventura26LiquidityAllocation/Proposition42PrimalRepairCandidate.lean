import Ventura26LiquidityAllocation.PaperInterface
import Ventura26LiquidityAllocation.ContinuationContractAuditCandidate

/-!
Proposed source-facing repair of local multiplicity (Proposition 4.2).

This is a SECOND, separate specification, NOT a modification or proof of the
pinned PaperInterface.localMacroMultiplicitySpec. The old version is formally
uninhabitable because it requires literal uniqueness of an Allocation with
an unconstrained collateralDual field.

The repaired version:
* compares the 13 paper-facing near processes after erasing collateralDual;
* compares all primal fields on admissible support in the exact-two clause;
* uses distinct finite-prefix vectors Zs != Zb, already separated by the
  source-backed strict-slack/binding complementarity conditions;
* preserves the same economic equilibrium and intervention predicates,
  normalization, continuation differentiability, Jacobian conditions, and
  slack/binding regime labels.

Importantly, no existence witness is proved for the repaired specification.
The data and KKT conditions that identify multipliers are separate remaining
economic obligations. This definition is a proposal for semantic review,
not an approved corrected source theorem.

No changes to the pinned model, PaperInterface, or both S/B branches.
-/

namespace Ventura26LiquidityAllocation
namespace ProposedProposition42PrimalRepair

open ProposedContinuationContractAudit

/-- Paper-facing near neighborhood (all histories) modulo the freely
    carried dual. The continuation neighborhood still uses the stronger
    on-support full-primal notion from ContinuationContractAuditCandidate. -/
def AllocationNearPrimal {S : Type*} (r : ℝ)
    (X Y : Allocation S) : Prop :=
  AllocationNear r (eraseCollateralDual X) (eraseCollateralDual Y)

theorem near_primal_replace_dual_right
    {S : Type*} (r : ℝ) (X Y : Allocation S)
    (dual : FirmType → AdaptedProcess S) :
    AllocationNearPrimal r X (replaceCollateralDual Y dual) ↔
      AllocationNearPrimal r X Y := by
  rfl

theorem near_primal_replace_dual_left
    {S : Type*} (r : ℝ) (X Y : Allocation S)
    (dual : FirmType → AdaptedProcess S) :
    AllocationNearPrimal r (replaceCollateralDual X dual) Y ↔
      AllocationNearPrimal r X Y := by
  rfl

theorem agreement_primal_replace_dual_right
    {S : Type*} [Fintype S] [DecidableEq S]
    (P : Primitives S) (X Y : Allocation S)
    (dual : FirmType → AdaptedProcess S) :
    AllocationPrimalAgreementOnSupport P X (replaceCollateralDual Y dual) ↔
      AllocationPrimalAgreementOnSupport P X Y := by
  rfl

/-- The branches are economically different already at the level of the
    reduced collateral slack, without comparing arbitrary multiplier fields. -/
theorem different_prefixes_of_strict_slack_binding
    {S : Type*} [Fintype S]
    (P : Primitives S) (Zs Zb : LocalPrefixCoordinates)
    (hs : 0 < localNormalizedSlackL P Zs)
    (hb : localNormalizedSlackL P Zb = 0) : Zs ≠ Zb := by
  intro h
  subst Zb
  exact (ne_of_gt hs) hb

/-!
The following statement is mechanically derived from PaperInterface's
localMacroMultiplicitySpec. The changes are strictly the four categories
documented above, without deleting or replacing existence assumptions.
-/

def localMacroMultiplicityPrimalSpec : Prop :=
  ∃ (S : Type) (_ : Fintype S) (_ : DecidableEq S)
      (P : Primitives S) (I : InheritedState) (X0 : Allocation S)
      (dateOne recurrent : S) (Z0 : LocalPrefixCoordinates)
      (tail : LocalPrefixContinuationRule)
      (solutionLog : (Fin 5 → ℝ) → (Fin 33 → ℝ)) (hStar r : ℝ),
    BoundaryEquilibriumCandidate P I X0 ∧
    InitialCalendarStateIsTransient P ∧
    DeterministicBridgeCalendar P dateOne recurrent ∧
    LocalMacroStrictBankRegime P I X0 dateOne ∧
    LocalPrefixCoordinatesRealized P X0 dateOne recurrent Z0 ∧
    LocalContinuationControlsRealized P X0 dateOne recurrent tail Z0.stateTwo ∧
    LocalExactContinuationAroundPrimal P recurrent Z0.stateTwo tail ∧
    LocalPrefixEquationsHold LocalPrefixBranch.slack P I X0 dateOne recurrent ∧
    LocalPrefixEquationsHold LocalPrefixBranch.binding P I X0 dateOne recurrent ∧
    LocalReducedPrefixEquationsHold LocalPrefixBranch.slack P I Z0
      dateOne recurrent tail ∧
    LocalReducedPrefixEquationsHold LocalPrefixBranch.binding P I Z0
      dateOne recurrent tail ∧
    LocalReducedPrefixLogJacobianCertifiedAt LocalPrefixBranch.slack P I Z0
      dateOne recurrent tail 54.297 ∧
    LocalReducedPrefixLogJacobianCertifiedAt LocalPrefixBranch.binding P I Z0
      dateOne recurrent tail 75.023 ∧
    LocalScalarImplicitReduction P I Z0 dateOne recurrent tail solutionLog ∧
    LocalScalarComplementarityL P Z0 ∧
    localNormalizedSlackL P Z0 = 0 ∧
    localNormalizedCollateralDualL P Z0 = 0 ∧
    0 < hStar ∧ 0 < r ∧
    CompetitiveEquilibriumWithInitialIntervention P I
      zeroInitialPolicyIntervention X0 ∧
    (∀ h, -hStar < h → h < 0 →
      let Ph := initialIntervenedPrimitives P (pureReserveRateIntervention h)
      ∃ (Xs Xb : Allocation S) (Zs Zb : LocalPrefixCoordinates),
        Zs ≠ Zb ∧
        CompetitiveEquilibriumWithInitialIntervention P I
          (pureReserveRateIntervention h) Xs ∧
        CompetitiveEquilibriumWithInitialIntervention P I
          (pureReserveRateIntervention h) Xb ∧
        LocalMacroStrictBankRegime Ph I Xs dateOne ∧
        LocalMacroStrictBankRegime Ph I Xb dateOne ∧
        LocalPrefixCoordinatesRealized Ph Xs dateOne recurrent Zs ∧
        LocalPrefixCoordinatesRealized Ph Xb dateOne recurrent Zb ∧
        LocalContinuationControlsRealized Ph Xs dateOne recurrent tail Zs.stateTwo ∧
        LocalContinuationControlsRealized Ph Xb dateOne recurrent tail Zb.stateTwo ∧
        LocalPrefixEquationsHold LocalPrefixBranch.slack Ph I Xs
          dateOne recurrent ∧
        LocalPrefixEquationsHold LocalPrefixBranch.binding Ph I Xb
          dateOne recurrent ∧
        LocalReducedPrefixEquationsHold LocalPrefixBranch.slack Ph I Zs
          dateOne recurrent tail ∧
        LocalReducedPrefixEquationsHold LocalPrefixBranch.binding Ph I Zb
          dateOne recurrent tail ∧
        LocalScalarComplementarityL Ph Zs ∧
        LocalScalarComplementarityL Ph Zb ∧
        0 < localNormalizedSlackL Ph Zs ∧
        localNormalizedCollateralDualL Ph Zs = 0 ∧
        localNormalizedSlackL Ph Zb = 0 ∧
        0 < localNormalizedCollateralDualL Ph Zb ∧
        AllocationNearPrimal r X0 Xs ∧ AllocationNearPrimal r X0 Xb ∧
        DateZeroSlackBorrower Ph Xs FirmType.L ∧
        DateZeroBindingBorrower Ph Xb FirmType.L ∧
        DateZeroBindingBorrower Ph Xs FirmType.H ∧
        DateZeroBindingBorrower Ph Xb FirmType.H ∧
        RestrictedFromDate Ph Xs FirmType.H 1 ∧
        RestrictedFromDate Ph Xs FirmType.L 1 ∧
        RestrictedFromDate Ph Xb FirmType.H 1 ∧
        RestrictedFromDate Ph Xb FirmType.L 1 ∧
        (∀ X, CompetitiveEquilibriumWithInitialIntervention P I
            (pureReserveRateIntervention h) X → AllocationNearPrimal r X0 X →
          AllocationPrimalAgreementOnSupport Ph X Xs ∨
            AllocationPrimalAgreementOnSupport Ph X Xb)) ∧
    (∀ h, 0 < h → h < hStar →
      ¬ ∃ X, CompetitiveEquilibriumWithInitialIntervention P I
          (pureReserveRateIntervention h) X ∧ AllocationNearPrimal r X0 X)

end ProposedProposition42PrimalRepair
end Ventura26LiquidityAllocation
