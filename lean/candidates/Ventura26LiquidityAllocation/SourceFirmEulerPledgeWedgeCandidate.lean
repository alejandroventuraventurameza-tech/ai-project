import Ventura26LiquidityAllocation.SourceCollateralRegimeLogBridgeCandidate

/-!
# Actual SOURCE firm Euler: exact unconstrained and binding wedge decomposition

The binding branch's capital Euler residual equals the unconstrained
Euler residual plus the pledge-unit wedge:
  pledge * (entrepreneurSDF / future inflation - 1 / current loan rate).
No Python SOURCE-shaped transcription is used.

This is a definitional/algebraic statement of the SOURCE function, not
an equilibrium, KKT sufficiency, positive-value, or growth theorem.
-/

namespace Ventura26LiquidityAllocation

noncomputable def sourceFirmEulerUnconstrained
    (P : Primitives LocalBridgePhase) (d : LocalPrefixDateData)
    (i : FirmType) : ℝ :=
  d.controls.capitalPrice -
    localPrefixEntrepreneurSDF P d i *
      (localPrefixNextMarginalProduct P d i +
        (1 - P.depreciation) * d.nextControls.capitalPrice)

noncomputable def sourceFirmEulerPledgeWedge
    (P : Primitives LocalBridgePhase) (d : LocalPrefixDateData)
    (i : FirmType) : ℝ :=
  localPrefixPledgeUnit P d i *
    (localPrefixEntrepreneurSDF P d i / d.nextControls.inflation -
      1 / d.controls.loanRate)

/-- Exact SOURCE binding capital Euler wedge at any date-local data,
without imposing the Euler row equals zero. -/
theorem sourceFirmEuler_binding_decomposition
    (P : Primitives LocalBridgePhase) (d : LocalPrefixDateData)
    (i : FirmType) :
    localReducedFirmCapitalEulerResidual .binding P d i =
      sourceFirmEulerUnconstrained P d i +
        sourceFirmEulerPledgeWedge P d i := by
  simp only [localReducedFirmCapitalEulerResidual,
    sourceFirmEulerUnconstrained, sourceFirmEulerPledgeWedge]
  ring

#print axioms sourceFirmEuler_binding_decomposition

/-- On the slack L branch the SOURCE Euler is the unconstrained Euler,
whereas the binding row retains its collateral-dependent wedge. -/
theorem sourceFirmEuler_slack_L_unconstrained
    (P : Primitives LocalBridgePhase) (d : LocalPrefixDateData) :
    localReducedFirmCapitalEulerResidual .slack P d FirmType.L =
      sourceFirmEulerUnconstrained P d FirmType.L := by
  rfl

#print axioms sourceFirmEuler_slack_L_unconstrained

/-- SOURCE date-one Euler is always evaluated on the binding branch,
regardless of the date-zero branch. -/
theorem sourceFirmEuler_dateOne_H_binding
    (branch : LocalPrefixBranch)
    (P : Primitives LocalBridgePhase) (I : InheritedState)
    (Z : LocalPrefixCoordinates) (dateOne recurrent : LocalBridgePhase)
    (tail : LocalPrefixContinuationRule) :
    localReducedPrefixResidual branch P I Z dateOne recurrent tail
      .firmCapitalEulerOneH =
    localReducedFirmCapitalEulerResidual .binding P
      (localPrefixDateOneData P Z dateOne recurrent tail) FirmType.H := by
  rfl

#print axioms sourceFirmEuler_dateOne_H_binding

theorem sourceFirmEuler_dateOne_L_binding
    (branch : LocalPrefixBranch)
    (P : Primitives LocalBridgePhase) (I : InheritedState)
    (Z : LocalPrefixCoordinates) (dateOne recurrent : LocalBridgePhase)
    (tail : LocalPrefixContinuationRule) :
    localReducedPrefixResidual branch P I Z dateOne recurrent tail
      .firmCapitalEulerOneL =
    localReducedFirmCapitalEulerResidual .binding P
      (localPrefixDateOneData P Z dateOne recurrent tail) FirmType.L := by
  rfl

#print axioms sourceFirmEuler_dateOne_L_binding

/-- SOURCE binding date-zero H-row is the binding Euler; the L-row
branches between collateral wedge and unconstrained Euler. -/
theorem sourceFirmEuler_dateZero_H_binding
    (P : Primitives LocalBridgePhase) (I : InheritedState)
    (Z : LocalPrefixCoordinates) (dateOne recurrent : LocalBridgePhase)
    (tail : LocalPrefixContinuationRule) :
    localReducedPrefixResidual .binding P I Z dateOne recurrent tail
      .firmCapitalEulerZeroH =
    localReducedFirmCapitalEulerResidual .binding P
      (localPrefixDateZeroData P I Z dateOne) FirmType.H := by
  rfl

#print axioms sourceFirmEuler_dateZero_H_binding

theorem sourceFirmEuler_dateZero_L_slack
    (P : Primitives LocalBridgePhase) (I : InheritedState)
    (Z : LocalPrefixCoordinates) (dateOne recurrent : LocalBridgePhase)
    (tail : LocalPrefixContinuationRule) :
    localReducedPrefixResidual .slack P I Z dateOne recurrent tail
      .firmCapitalEulerZeroL =
    localReducedFirmCapitalEulerResidual .slack P
      (localPrefixDateZeroData P I Z dateOne) FirmType.L := by
  rfl

#print axioms sourceFirmEuler_dateZero_L_slack

end Ventura26LiquidityAllocation
