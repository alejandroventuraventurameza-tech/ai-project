import Ventura26LiquidityAllocation.SourceBindingSlackRowFrechetCandidate
import Ventura26LiquidityAllocation.SourceBinding33Row5RankTransportCandidate
import Ventura26LiquidityAllocation.SourceBindingZeroPolicySemanticCandidate
import Ventura26LiquidityAllocation.SourceEulerLogChartRowIndexCandidate

/-!
# Genuine SOURCE 33x33 binding Jacobian transport at a collateral root

Combines the SOURCE zero-intervention primitive identity, exact
modified binding-row semantics, original row index bijectivity and
the nonzero-pledge Fréchet row-5 scaling lemma.

For all original log-coordinate perturbations u, the first-33-row
Jacobian of the augmented remuneration boundary equals a diagonal
row-5 rescaling of the original SOURCE binding branch Jacobian.

At an exact SOURCE binding root with nonzero pledge face, the
modified 33x33 block A is bijective iff the original binding
Jacobian is bijective. This is an *equivalence*, not a proof
that either Jacobian is invertible or that the root exists.
-/

namespace Ventura26LiquidityAllocation

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- All 33 rows of the true SOURCE binding Jacobians differ by
exactly the row-5 scaling at a binding collateral root. Other
32 row identities follow from zero-policy semantic equality. -/
theorem sourceBinding33Jacobian_actual_row_scaling_at_root
    (P : Primitives S) (I : InheritedState)
    (Z0 : LocalPrefixCoordinates)
    (dateOne recurrent : S) (tail : LocalPrefixContinuationRule)
    (zstar : Fin 33 → ℝ)
    (hraw : DifferentiableAt ℝ
      (fun z => localReducedPrefixResidual LocalPrefixBranch.binding P I
        (localPrefixLogChart Z0 z) dateOne recurrent tail
        LocalPrefixEquation.firmRegimeZeroL) zstar)
    (hpledge : DifferentiableAt ℝ
      (fun z => sourceBindingLPledgeFace P (localPrefixLogChart Z0 z))
      zstar)
    (hroot : localReducedPrefixResidual LocalPrefixBranch.binding P I
      (localPrefixLogChart Z0 zstar) dateOne recurrent tail
      LocalPrefixEquation.firmRegimeZeroL = 0)
    (hne : sourceBindingLPledgeFace P (localPrefixLogChart Z0 zstar) ≠ 0)
    (direction : Fin 33 → ℝ) :
    (fun row : Fin 33 =>
      (fderiv ℝ
        (fun z : Fin 33 → ℝ =>
          localBindingResidualWithSlack P I Z0 dateOne recurrent tail
            (ProposedLocalScalarEconomicSlice.reserveRemunerationSlice 0 0)
            z row) zstar) direction) =
    sourceBindingRow5Rescale
      (-(sourceBindingLPledgeFace P (localPrefixLogChart Z0 zstar))⁻¹)
      (fun row : Fin 33 =>
        (fderiv ℝ
          (fun z : Fin 33 → ℝ =>
            localReducedPrefixResidual LocalPrefixBranch.binding P I
              (localPrefixLogChart Z0 z) dateOne recurrent tail
              (localPrefixEquationOfIndex row)) zstar) direction) := by
  funext row
  by_cases hlabel :
      localPrefixEquationOfIndex row = LocalPrefixEquation.firmRegimeZeroL
  · have h5 : row = (5 : Fin 33) := by
      apply sourceLogRowIndex_bijective.1
      simpa [localPrefixEquationOfIndex] using hlabel
    subst row
    have hfun :
        (fun z : Fin 33 → ℝ =>
          localBindingResidualWithSlack P I Z0 dateOne recurrent tail
            (ProposedLocalScalarEconomicSlice.reserveRemunerationSlice 0 0)
            z (5 : Fin 33)) =
        (fun z : Fin 33 → ℝ =>
          localNormalizedSlackL P (localPrefixLogChart Z0 z)) := by
      funext z
      simpa [localPrefixEquationOfIndex] using
        (sourceModifiedBinding33_zeroPolicy_eachRow
          P I Z0 dateOne recurrent tail z (5 : Fin 33))
    rw [hfun]
    have hrow := congrArg
      (fun derivative : (Fin 33 → ℝ) →L[ℝ] ℝ => derivative direction)
      (sourceBindingSlackL_fderiv_eq_scaled_raw_at_root
        P I Z0 dateOne recurrent tail zstar hraw hpledge hroot hne)
    simpa [sourceBindingRow5Rescale, localPrefixEquationOfIndex] using hrow
  · have h5 : row ≠ (5 : Fin 33) := by
      intro he
      subst row
      exact hlabel rfl
    have hfun :
        (fun z : Fin 33 → ℝ =>
          localBindingResidualWithSlack P I Z0 dateOne recurrent tail
            (ProposedLocalScalarEconomicSlice.reserveRemunerationSlice 0 0)
            z row) =
        (fun z : Fin 33 → ℝ =>
          localReducedPrefixResidual LocalPrefixBranch.binding P I
            (localPrefixLogChart Z0 z) dateOne recurrent tail
            (localPrefixEquationOfIndex row)) := by
      funext z
      simpa only [if_neg hlabel] using
        (sourceModifiedBinding33_zeroPolicy_eachRow
          P I Z0 dateOne recurrent tail z row)
    rw [hfun]
    simp [sourceBindingRow5Rescale, h5]

#print axioms sourceBinding33Jacobian_actual_row_scaling_at_root

/-- Under explicit SOURCE binding root, differentiability and
nonzero pledge assumptions, the original 33-row binding Jacobian
is bijective iff the true zero-policy modified binding block is
bijective. No numerical or equilibrium invertibility is assumed. -/
theorem sourceBinding33Jacobian_actual_bijective_iff_at_root
    (P : Primitives S) (I : InheritedState)
    (Z0 : LocalPrefixCoordinates)
    (dateOne recurrent : S) (tail : LocalPrefixContinuationRule)
    (zstar : Fin 33 → ℝ)
    (hraw : DifferentiableAt ℝ
      (fun z => localReducedPrefixResidual LocalPrefixBranch.binding P I
        (localPrefixLogChart Z0 z) dateOne recurrent tail
        LocalPrefixEquation.firmRegimeZeroL) zstar)
    (hpledge : DifferentiableAt ℝ
      (fun z => sourceBindingLPledgeFace P (localPrefixLogChart Z0 z))
      zstar)
    (hroot : localReducedPrefixResidual LocalPrefixBranch.binding P I
      (localPrefixLogChart Z0 zstar) dateOne recurrent tail
      LocalPrefixEquation.firmRegimeZeroL = 0)
    (hne : sourceBindingLPledgeFace P (localPrefixLogChart Z0 zstar) ≠ 0) :
    Function.Bijective
      (fun direction : Fin 33 → ℝ =>
        fun row : Fin 33 =>
          (fderiv ℝ
            (fun z : Fin 33 → ℝ =>
              localBindingResidualWithSlack P I Z0 dateOne recurrent tail
                (ProposedLocalScalarEconomicSlice.reserveRemunerationSlice 0 0)
                z row) zstar) direction) ↔
    Function.Bijective
      (fun direction : Fin 33 → ℝ =>
        fun row : Fin 33 =>
          (fderiv ℝ
            (fun z : Fin 33 → ℝ =>
              localReducedPrefixResidual LocalPrefixBranch.binding P I
                (localPrefixLogChart Z0 z) dateOne recurrent tail
                (localPrefixEquationOfIndex row)) zstar) direction) := by
  apply sourceBinding33Jacobian_bijective_iff_of_exact_row5
    (fun direction : Fin 33 → ℝ =>
      fun row : Fin 33 =>
        (fderiv ℝ
          (fun z : Fin 33 → ℝ =>
            localReducedPrefixResidual LocalPrefixBranch.binding P I
              (localPrefixLogChart Z0 z) dateOne recurrent tail
              (localPrefixEquationOfIndex row)) zstar) direction)
    (fun direction : Fin 33 → ℝ =>
      fun row : Fin 33 =>
        (fderiv ℝ
          (fun z : Fin 33 → ℝ =>
            localBindingResidualWithSlack P I Z0 dateOne recurrent tail
              (ProposedLocalScalarEconomicSlice.reserveRemunerationSlice 0 0)
              z row) zstar) direction)
    (sourceBindingLPledgeFace P (localPrefixLogChart Z0 zstar)) hne
  intro direction
  exact sourceBinding33Jacobian_actual_row_scaling_at_root
    P I Z0 dateOne recurrent tail zstar hraw hpledge hroot hne direction

#print axioms sourceBinding33Jacobian_actual_bijective_iff_at_root

end Ventura26LiquidityAllocation
