import Ventura26LiquidityAllocation.SourceReduced33FrechetChartTransportCandidate

/-!
# Exact root-set equivalence for the 33-dimensional genuine SOURCE chart

The eliminated loan-rate log coordinate does not add or remove economic
zeros: under the stated stationary positive hypotheses, every reduced
33-row root lifts to a full 34-row SOURCE augmented root and EVERY full
SOURCE augmented root is the lift of a UNIQUE 32-free-log-plus-policy point.

The resulting Equiv is between the actual SOURCE root subtypes, not an
equivalence to a Python float64 solver, and it proves neither existence
nor number of roots. In particular, it cannot by itself prove two
competitive equilibria in the slack/binding regimes.
-/

namespace Ventura26LiquidityAllocation

open ProposedLocalScalarAugmented34Source
open ProposedLocalScalarEconomicSlice

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- At an ORIGINAL SOURCE augmented root, the analytic loan-rate
elimination must reproduce the entire vector, not merely its free logs. -/
theorem sourceFundingDualLift32_recovers_original_root
    (P : Primitives S) (I : InheritedState)
    (Z0 : LocalPrefixCoordinates) (dateOne recurrent : S)
    (tail : LocalPrefixContinuationRule)
    (z : Fin 33 → ℝ) (h : ℝ)
    (hsigma : P.entrepreneurRiskAversion = 1)
    (hc_same : Z0.controlsZero.consumptionL = Z0.controlsOne.consumptionL)
    (hc_positive : 0 < Z0.controlsZero.consumptionL)
    (hpi : Z0.controlsOne.inflation = 1)
    (hr : 0 < Z0.controlsZero.loanRate)
    (hbeta : 0 < P.entrepreneurDiscount)
    (hroot : augmentedBoundaryZeroResidual
      P I Z0 dateOne recurrent tail z h = (0, 0)) :
    sourceFundingDualLift32 P Z0 ((15 : Fin 33).removeNth z) = z := by
  calc
    sourceFundingDualLift32 P Z0 ((15 : Fin 33).removeNth z) =
        sourceDualLoanLogEliminate P Z0 z :=
      sourceFundingDualLift32_removeNth P Z0 z
    _ = z := sourceDualLoanLogEliminate_eq_self_of_source_root
      P I Z0 dateOne recurrent tail z h
      hsigma hc_same hc_positive hpi hr hbeta hroot

#print axioms sourceFundingDualLift32_recovers_original_root

/-- Every full SOURCE augmented root is represented by a reduced SOURCE
economic root with the SAME policy innovation and original data. -/
theorem sourceReduced33_root_from_original
    (P : Primitives S) (I : InheritedState)
    (Z0 : LocalPrefixCoordinates) (dateOne recurrent : S)
    (tail : LocalPrefixContinuationRule)
    (z : Fin 33 → ℝ) (h : ℝ)
    (hsigma : P.entrepreneurRiskAversion = 1)
    (hc_same : Z0.controlsZero.consumptionL = Z0.controlsOne.consumptionL)
    (hc_positive : 0 < Z0.controlsZero.consumptionL)
    (hpi : Z0.controlsOne.inflation = 1)
    (hr : 0 < Z0.controlsZero.loanRate)
    (hbeta : 0 < P.entrepreneurDiscount)
    (hroot : augmentedBoundaryZeroResidual
      P I Z0 dateOne recurrent tail z h = (0, 0)) :
    sourceReduced33EconomicMap P I Z0 dateOne recurrent tail
      ((15 : Fin 33).removeNth z, h) = 0 := by
  apply (sourceReduced33_pointwise_root_iff P I Z0
    dateOne recurrent tail ((15 : Fin 33).removeNth z) h
    hsigma hc_same hc_positive hpi hr hbeta).2
  rw [sourceFundingDualLift32_recovers_original_root
    P I Z0 dateOne recurrent tail z h
    hsigma hc_same hc_positive hpi hr hbeta hroot]
  exact hroot

#print axioms sourceReduced33_root_from_original

/-- Genuine SOURCE zeros are in one-to-one correspondence: the full
34-coordinate root subtype is equivalent to the reduced 33-coordinate
root subtype. This Equiv is a logical representation theorem, NOT
an existence witness. -/
noncomputable def sourceReduced33_root_equiv_original34
    (P : Primitives S) (I : InheritedState)
    (Z0 : LocalPrefixCoordinates) (dateOne recurrent : S)
    (tail : LocalPrefixContinuationRule)
    (hsigma : P.entrepreneurRiskAversion = 1)
    (hc_same : Z0.controlsZero.consumptionL = Z0.controlsOne.consumptionL)
    (hc_positive : 0 < Z0.controlsZero.consumptionL)
    (hpi : Z0.controlsOne.inflation = 1)
    (hr : 0 < Z0.controlsZero.loanRate)
    (hbeta : 0 < P.entrepreneurDiscount) :
    {w : (Fin 32 → ℝ) × ℝ //
      sourceReduced33EconomicMap P I Z0 dateOne recurrent tail w = 0} ≃
    {w : (Fin 33 → ℝ) × ℝ //
      augmentedBoundaryZeroResidual P I Z0 dateOne recurrent tail
        w.1 w.2 = (0, 0)} where
  toFun := fun w =>
    ⟨(sourceFundingDualLift32 P Z0 w.1.1, w.1.2),
      (sourceReduced33_pointwise_root_iff P I Z0
        dateOne recurrent tail w.1.1 w.1.2
        hsigma hc_same hc_positive hpi hr hbeta).mp w.2⟩
  invFun := fun w =>
    ⟨((15 : Fin 33).removeNth w.1.1, w.1.2),
      sourceReduced33_root_from_original P I Z0 dateOne recurrent tail
        w.1.1 w.1.2 hsigma hc_same hc_positive hpi hr hbeta w.2⟩
  left_inv := by
    intro w
    apply Subtype.ext
    apply Prod.ext
    · exact sourceFundingDualLift32_removeNth_leftInverse P Z0 w.1.1
    · rfl
  right_inv := by
    intro w
    apply Subtype.ext
    apply Prod.ext
    · exact sourceFundingDualLift32_recovers_original_root
        P I Z0 dateOne recurrent tail w.1.1 w.1.2
        hsigma hc_same hc_positive hpi hr hbeta w.2
    · rfl

#print axioms sourceReduced33_root_equiv_original34

end Ventura26LiquidityAllocation
