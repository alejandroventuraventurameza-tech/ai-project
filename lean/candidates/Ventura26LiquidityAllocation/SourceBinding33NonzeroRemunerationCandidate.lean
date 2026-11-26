import Ventura26LiquidityAllocation.SourceBinding33JacobianActualTransportCandidate
import Ventura26LiquidityAllocation.LocalScalarEconomicSliceCandidate

/-!
# Genuine SOURCE 33-row binding semantics at an ARBITRARY reserve-rate shock

The previous semantic and row-5 Frechet bridges were pinned to h=0.
The economically relevant candidate boundary instead occurs at a nonzero
reserve-remuneration innovation h*. Here the actual SOURCE intervention
is kept inside all 33 economic equations. The original binding residual
uses Pv(h), not the unperturbed primitives P.

No approximate Python Jacobian, numerical h*, or economic root is imported.
All Jacobian conclusions still assume differentiability and a genuine
SOURCE collateral root at the considered nonzero intervention.
-/

namespace Ventura26LiquidityAllocation

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- Literal SOURCE monetary primitives after the policy slice (s=0,h).
Only the innovation to reserve remuneration changes in this slice. -/
noncomputable def sourceReserveSlicePrimitives
    (P : Primitives S) (h : ℝ) : Primitives S :=
  initialIntervenedPrimitives P
    (localScalarParameterIntervention
      (ProposedLocalScalarEconomicSlice.reserveRemunerationSlice 0 h))

/-- Neither the depreciation rate nor the pledgeability parameter is
silently changed by the monetary innovation. -/
theorem sourceReserveSlice_pledgeFace_invariant
    (P : Primitives S) (h : ℝ) (Z : LocalPrefixCoordinates) :
    sourceBindingLPledgeFace (sourceReserveSlicePrimitives P h) Z =
      sourceBindingLPledgeFace P Z := by
  rfl

#print axioms sourceReserveSlice_pledgeFace_invariant

/-- Full exact SOURCE 33-row identity at every log coordinate and every
real reserve-remuneration innovation h (not only at h=0). At fixed h the
modified first 33 equations are the binding-branch equations under Pv(h),
except row 5, which is their normalized L collateral slack. -/
theorem sourceBinding33_nonzeroPolicy_eachRow
    (P : Primitives S) (I : InheritedState)
    (Z0 : LocalPrefixCoordinates)
    (dateOne recurrent : S) (tail : LocalPrefixContinuationRule)
    (z : Fin 33 → ℝ) (h : ℝ) (row : Fin 33) :
    localBindingResidualWithSlack P I Z0 dateOne recurrent tail
      (ProposedLocalScalarEconomicSlice.reserveRemunerationSlice 0 h) z row =
    if localPrefixEquationOfIndex row = LocalPrefixEquation.firmRegimeZeroL then
      localNormalizedSlackL (sourceReserveSlicePrimitives P h)
        (localPrefixLogChart Z0 z)
    else
      localReducedPrefixResidual LocalPrefixBranch.binding
        (sourceReserveSlicePrimitives P h) I
        (localPrefixLogChart Z0 z) dateOne recurrent tail
        (localPrefixEquationOfIndex row) := by
  by_cases hrow :
      localPrefixEquationOfIndex row = LocalPrefixEquation.firmRegimeZeroL
  · simp [localBindingResidualWithSlack, sourceReserveSlicePrimitives,
      hrow]
  · simp [localBindingResidualWithSlack, sourceReserveSlicePrimitives,
      hrow]

#print axioms sourceBinding33_nonzeroPolicy_eachRow

/-- On a positive-pledge point, the changed 33-system has exactly
the same zeros as the raw binding system with the *intervened*
SOURCE primitives Pv(h). -/
theorem sourceBinding33_nonzeroPolicy_row_zero_iff
    (P : Primitives S) (I : InheritedState)
    (Z0 : LocalPrefixCoordinates)
    (dateOne recurrent : S) (tail : LocalPrefixContinuationRule)
    (z : Fin 33 → ℝ) (h : ℝ) (row : Fin 33)
    (hne : sourceBindingLPledgeFace (sourceReserveSlicePrimitives P h)
      (localPrefixLogChart Z0 z) ≠ 0) :
    (localBindingResidualWithSlack P I Z0 dateOne recurrent tail
      (ProposedLocalScalarEconomicSlice.reserveRemunerationSlice 0 h)
      z row = 0) ↔
    (localReducedPrefixResidual LocalPrefixBranch.binding
      (sourceReserveSlicePrimitives P h) I
      (localPrefixLogChart Z0 z) dateOne recurrent tail
      (localPrefixEquationOfIndex row) = 0) := by
  rw [sourceBinding33_nonzeroPolicy_eachRow
    P I Z0 dateOne recurrent tail z h row]
  by_cases hrow :
      localPrefixEquationOfIndex row = LocalPrefixEquation.firmRegimeZeroL
  · simp only [if_pos hrow]
    rw [hrow]
    exact sourceBindingNormalizedSlackL_zero_iff_rawL_zero
      (sourceReserveSlicePrimitives P h) I
      (localPrefixLogChart Z0 z) dateOne recurrent tail hne
  · simp only [if_neg hrow]

#print axioms sourceBinding33_nonzeroPolicy_row_zero_iff

/-- Whole genuine SOURCE 33-row solution-set equivalence holds for
arbitrary h (including the nonzero h*), with the inherited I unchanged. -/
theorem sourceBinding33_nonzeroPolicy_all_zero_iff
    (P : Primitives S) (I : InheritedState)
    (Z0 : LocalPrefixCoordinates)
    (dateOne recurrent : S) (tail : LocalPrefixContinuationRule)
    (z : Fin 33 → ℝ) (h : ℝ)
    (hne : sourceBindingLPledgeFace (sourceReserveSlicePrimitives P h)
      (localPrefixLogChart Z0 z) ≠ 0) :
    (∀ row : Fin 33,
      localBindingResidualWithSlack P I Z0 dateOne recurrent tail
        (ProposedLocalScalarEconomicSlice.reserveRemunerationSlice 0 h)
        z row = 0) ↔
    (∀ row : Fin 33,
      localReducedPrefixResidual LocalPrefixBranch.binding
        (sourceReserveSlicePrimitives P h) I
        (localPrefixLogChart Z0 z) dateOne recurrent tail
        (localPrefixEquationOfIndex row) = 0) := by
  constructor
  · intro hz row
    exact (sourceBinding33_nonzeroPolicy_row_zero_iff
      P I Z0 dateOne recurrent tail z h row hne).mp (hz row)
  · intro hz row
    exact (sourceBinding33_nonzeroPolicy_row_zero_iff
      P I Z0 dateOne recurrent tail z h row hne).mpr (hz row)

#print axioms sourceBinding33_nonzeroPolicy_all_zero_iff

/-- The genuine SOURCE Frechet Jacobian of the modified 33-row block
at h differs from the raw Pv(h) binding Jacobian ONLY by the row-5
factor -1 / Gamma_L, at a genuine Pv(h) collateral root. -/
theorem sourceBinding33_nonzeroPolicy_actual_row_scaling_at_root
    (P : Primitives S) (I : InheritedState)
    (Z0 : LocalPrefixCoordinates)
    (dateOne recurrent : S) (tail : LocalPrefixContinuationRule)
    (zstar : Fin 33 → ℝ) (h : ℝ)
    (hraw : DifferentiableAt ℝ
      (fun z => localReducedPrefixResidual LocalPrefixBranch.binding
        (sourceReserveSlicePrimitives P h) I
        (localPrefixLogChart Z0 z) dateOne recurrent tail
        LocalPrefixEquation.firmRegimeZeroL) zstar)
    (hpledge : DifferentiableAt ℝ
      (fun z => sourceBindingLPledgeFace
        (sourceReserveSlicePrimitives P h) (localPrefixLogChart Z0 z))
      zstar)
    (hroot : localReducedPrefixResidual LocalPrefixBranch.binding
      (sourceReserveSlicePrimitives P h) I
      (localPrefixLogChart Z0 zstar) dateOne recurrent tail
      LocalPrefixEquation.firmRegimeZeroL = 0)
    (hne : sourceBindingLPledgeFace (sourceReserveSlicePrimitives P h)
      (localPrefixLogChart Z0 zstar) ≠ 0)
    (direction : Fin 33 → ℝ) :
    (fun row : Fin 33 =>
      (fderiv ℝ
        (fun z : Fin 33 → ℝ =>
          localBindingResidualWithSlack P I Z0 dateOne recurrent tail
            (ProposedLocalScalarEconomicSlice.reserveRemunerationSlice 0 h)
            z row) zstar) direction) =
    sourceBindingRow5Rescale
      (-(sourceBindingLPledgeFace (sourceReserveSlicePrimitives P h)
        (localPrefixLogChart Z0 zstar))⁻¹)
      (fun row : Fin 33 =>
        (fderiv ℝ
          (fun z : Fin 33 → ℝ =>
            localReducedPrefixResidual LocalPrefixBranch.binding
              (sourceReserveSlicePrimitives P h) I
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
            (ProposedLocalScalarEconomicSlice.reserveRemunerationSlice 0 h)
            z (5 : Fin 33)) =
        (fun z : Fin 33 → ℝ =>
          localNormalizedSlackL (sourceReserveSlicePrimitives P h)
            (localPrefixLogChart Z0 z)) := by
      funext z
      simpa [localPrefixEquationOfIndex] using
        (sourceBinding33_nonzeroPolicy_eachRow
          P I Z0 dateOne recurrent tail z h (5 : Fin 33))
    rw [hfun]
    have hderiv := congrArg
      (fun derivative : (Fin 33 → ℝ) →L[ℝ] ℝ => derivative direction)
      (sourceBindingSlackL_fderiv_eq_scaled_raw_at_root
        (sourceReserveSlicePrimitives P h) I
        Z0 dateOne recurrent tail zstar hraw hpledge hroot hne)
    simpa [sourceBindingRow5Rescale, localPrefixEquationOfIndex] using hderiv
  · have h5 : row ≠ (5 : Fin 33) := by
      intro he
      subst row
      exact hlabel rfl
    have hfun :
        (fun z : Fin 33 → ℝ =>
          localBindingResidualWithSlack P I Z0 dateOne recurrent tail
            (ProposedLocalScalarEconomicSlice.reserveRemunerationSlice 0 h)
            z row) =
        (fun z : Fin 33 → ℝ =>
          localReducedPrefixResidual LocalPrefixBranch.binding
            (sourceReserveSlicePrimitives P h) I
            (localPrefixLogChart Z0 z) dateOne recurrent tail
            (localPrefixEquationOfIndex row)) := by
      funext z
      simpa only [if_neg hlabel] using
        (sourceBinding33_nonzeroPolicy_eachRow
          P I Z0 dateOne recurrent tail z h row)
    rw [hfun]
    simp [sourceBindingRow5Rescale, h5]

#print axioms sourceBinding33_nonzeroPolicy_actual_row_scaling_at_root

/-- The 33x33 SOURCE Jacobian rank is preserved at any h, including a
nonzero boundary h*, assuming the actual SOURCE collateral root,
differentiability and nonzero pledge face. This is a rank EQUIVALENCE,
not a certificate that either economic Jacobian is invertible. -/
theorem sourceBinding33_nonzeroPolicy_Jacobian_bijective_iff_at_root
    (P : Primitives S) (I : InheritedState)
    (Z0 : LocalPrefixCoordinates)
    (dateOne recurrent : S) (tail : LocalPrefixContinuationRule)
    (zstar : Fin 33 → ℝ) (h : ℝ)
    (hraw : DifferentiableAt ℝ
      (fun z => localReducedPrefixResidual LocalPrefixBranch.binding
        (sourceReserveSlicePrimitives P h) I
        (localPrefixLogChart Z0 z) dateOne recurrent tail
        LocalPrefixEquation.firmRegimeZeroL) zstar)
    (hpledge : DifferentiableAt ℝ
      (fun z => sourceBindingLPledgeFace
        (sourceReserveSlicePrimitives P h) (localPrefixLogChart Z0 z))
      zstar)
    (hroot : localReducedPrefixResidual LocalPrefixBranch.binding
      (sourceReserveSlicePrimitives P h) I
      (localPrefixLogChart Z0 zstar) dateOne recurrent tail
      LocalPrefixEquation.firmRegimeZeroL = 0)
    (hne : sourceBindingLPledgeFace (sourceReserveSlicePrimitives P h)
      (localPrefixLogChart Z0 zstar) ≠ 0) :
    Function.Bijective
      (fun direction : Fin 33 → ℝ =>
        fun row : Fin 33 =>
          (fderiv ℝ
            (fun z : Fin 33 → ℝ =>
              localBindingResidualWithSlack P I Z0 dateOne recurrent tail
                (ProposedLocalScalarEconomicSlice.reserveRemunerationSlice 0 h)
                z row) zstar) direction) ↔
    Function.Bijective
      (fun direction : Fin 33 → ℝ =>
        fun row : Fin 33 =>
          (fderiv ℝ
            (fun z : Fin 33 → ℝ =>
              localReducedPrefixResidual LocalPrefixBranch.binding
                (sourceReserveSlicePrimitives P h) I
                (localPrefixLogChart Z0 z) dateOne recurrent tail
                (localPrefixEquationOfIndex row)) zstar) direction) := by
  apply sourceBinding33Jacobian_bijective_iff_of_exact_row5
    (fun direction : Fin 33 → ℝ =>
      fun row : Fin 33 =>
        (fderiv ℝ
          (fun z : Fin 33 → ℝ =>
            localReducedPrefixResidual LocalPrefixBranch.binding
              (sourceReserveSlicePrimitives P h) I
              (localPrefixLogChart Z0 z) dateOne recurrent tail
              (localPrefixEquationOfIndex row)) zstar) direction)
    (fun direction : Fin 33 → ℝ =>
      fun row : Fin 33 =>
        (fderiv ℝ
          (fun z : Fin 33 → ℝ =>
            localBindingResidualWithSlack P I Z0 dateOne recurrent tail
              (ProposedLocalScalarEconomicSlice.reserveRemunerationSlice 0 h)
              z row) zstar) direction)
    (sourceBindingLPledgeFace (sourceReserveSlicePrimitives P h)
      (localPrefixLogChart Z0 zstar)) hne
  intro direction
  exact sourceBinding33_nonzeroPolicy_actual_row_scaling_at_root
    P I Z0 dateOne recurrent tail zstar h hraw hpledge hroot hne direction

#print axioms sourceBinding33_nonzeroPolicy_Jacobian_bijective_iff_at_root

end Ventura26LiquidityAllocation
