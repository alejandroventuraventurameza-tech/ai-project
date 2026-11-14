import Ventura26LiquidityAllocation.EconomicModel

/-!
# A literal SOURCE extensionality lemma for inherited reduced-prefix data

This proposition concerns ONLY the 33-row reduced local prefix in EconomicModel.
It does not claim equivalence of the underlying complete equilibrium, fiscal
closure, bank plans, or Python implementation.
-/

namespace Ventura26LiquidityAllocation

variable {S : Type*} [Fintype S] [DecidableEq S]

theorem localReducedPrefixResidual_inherited_extensionality
    (branch : LocalPrefixBranch) (P : Primitives S)
    (I J : InheritedState) (Z : LocalPrefixCoordinates)
    (dateOne recurrent : S) (tail : LocalPrefixContinuationRule)
    (hcapital : I.capital = J.capital)
    (hface : I.firmFace = J.firmFace)
    (hbank : I.bankFace = J.bankFace)
    (hrate : I.reserveRateLag = J.reserveRateLag)
    (hreserves : I.reservesPreLag = J.reservesPreLag)
    (equation : LocalPrefixEquation) :
    localReducedPrefixResidual branch P I Z dateOne recurrent tail equation =
      localReducedPrefixResidual branch P J Z dateOne recurrent tail equation := by
  have hdate :
      localPrefixDateZeroData P I Z dateOne =
        localPrefixDateZeroData P J Z dateOne := by
    simp [localPrefixDateZeroData, hcapital, hface, hbank, hrate, hreserves]
  simp [localReducedPrefixResidual, hdate]

#print axioms localReducedPrefixResidual_inherited_extensionality

theorem localReducedPrefixLogResidualVector_inherited_extensionality
    (branch : LocalPrefixBranch) (P : Primitives S)
    (I J : InheritedState) (Z0 : LocalPrefixCoordinates)
    (dateOne recurrent : S) (tail : LocalPrefixContinuationRule)
    (hcapital : I.capital = J.capital)
    (hface : I.firmFace = J.firmFace)
    (hbank : I.bankFace = J.bankFace)
    (hrate : I.reserveRateLag = J.reserveRateLag)
    (hreserves : I.reservesPreLag = J.reservesPreLag) :
    localReducedPrefixLogResidualVector branch P I Z0 dateOne recurrent tail =
      localReducedPrefixLogResidualVector branch P J Z0 dateOne recurrent tail := by
  funext z row
  exact localReducedPrefixResidual_inherited_extensionality
    branch P I J (localPrefixLogChart Z0 z) dateOne recurrent tail
    hcapital hface hbank hrate hreserves (localPrefixEquationOfIndex row)

#print axioms localReducedPrefixLogResidualVector_inherited_extensionality



/-- Equality of the actual SOURCE Fréchet derivatives follows from equality
of the full log residual functions; no rank, inverse or smoothness is assumed. -/
theorem localReducedPrefixLogJacobian_inherited_extensionality
    (branch : LocalPrefixBranch) (P : Primitives S)
    (I J : InheritedState) (Z0 : LocalPrefixCoordinates)
    (dateOne recurrent : S) (tail : LocalPrefixContinuationRule)
    (hcapital : I.capital = J.capital)
    (hface : I.firmFace = J.firmFace)
    (hbank : I.bankFace = J.bankFace)
    (hrate : I.reserveRateLag = J.reserveRateLag)
    (hreserves : I.reservesPreLag = J.reservesPreLag) :
    fderiv ℝ (localReducedPrefixLogResidualVector branch P I Z0 dateOne recurrent tail)
        (0 : Fin 33 → ℝ) =
      fderiv ℝ (localReducedPrefixLogResidualVector branch P J Z0 dateOne recurrent tail)
        (0 : Fin 33 → ℝ) := by
  rw [localReducedPrefixLogResidualVector_inherited_extensionality
    branch P I J Z0 dateOne recurrent tail hcapital hface hbank hrate hreserves]

#print axioms localReducedPrefixLogJacobian_inherited_extensionality

/-- The *property* of possessing a certified inverse for the original SOURCE
log-residual Jacobian is constant on each inherited-state fiber.  Neither
the certificate's existence nor positivity is proved here. -/
theorem localReducedPrefixLogJacobianCertifiedAt_inherited_iff
    (branch : LocalPrefixBranch) (P : Primitives S)
    (I J : InheritedState) (Z0 : LocalPrefixCoordinates)
    (dateOne recurrent : S) (tail : LocalPrefixContinuationRule)
    (inverseNormBound : ℝ)
    (hcapital : I.capital = J.capital)
    (hface : I.firmFace = J.firmFace)
    (hbank : I.bankFace = J.bankFace)
    (hrate : I.reserveRateLag = J.reserveRateLag)
    (hreserves : I.reservesPreLag = J.reservesPreLag) :
    LocalReducedPrefixLogJacobianCertifiedAt
      branch P I Z0 dateOne recurrent tail inverseNormBound ↔
    LocalReducedPrefixLogJacobianCertifiedAt
      branch P J Z0 dateOne recurrent tail inverseNormBound := by
  have hfun := localReducedPrefixLogResidualVector_inherited_extensionality
    branch P I J Z0 dateOne recurrent tail
    hcapital hface hbank hrate hreserves
  simp only [LocalReducedPrefixLogJacobianCertifiedAt, hfun]

#print axioms localReducedPrefixLogJacobianCertifiedAt_inherited_iff


end Ventura26LiquidityAllocation
