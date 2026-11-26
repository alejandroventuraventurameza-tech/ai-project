import Ventura26LiquidityAllocation.CurrentSourceTwoDateFDerivTransport

/-!
# Injectivity transport for the genuine two-date SOURCE Jacobian

The SOURCE bank targetization is a six-row triangular operation on the
actual 33-dimensional economic residual. At a common root, the preceding
Fréchet theorem shows that its Jacobian is E(z0) composed with J_source.

This module proves that the linear operator E(z0) is injective for all
real coefficients and transports Jacobian injectivity *conditional on*
a SOURCE root, economic admissibility on a neighborhood and the assumed
Fréchet derivatives. No numerical bound for J_source is provided.
-/

namespace Ventura26LiquidityAllocation
namespace CurrentSourceFullFDeriv

open CurrentSourceTwoDateBank
open scoped Topology

/-- The linear realization of the six SOURCE bank-row operations has
trivial kernel and is injective, for arbitrary eight real coefficients. -/
theorem sourceShearCLM_injective
    (loan0 deposit0 loan1 deposit1
      rate0 quantity0 rate1 quantity1 : ℝ) :
    Function.Injective
      (sourceShearCLM loan0 deposit0 loan1 deposit1
        rate0 quantity0 rate1 quantity1) := by
  intro v w hvw
  have hz :
      sourceShearCLM loan0 deposit0 loan1 deposit1
        rate0 quantity0 rate1 quantity1 (v - w) = 0 := by
    simpa only [map_sub, sub_eq_zero] using hvw
  have hzero : v - w = 0 :=
    (sourceShearCLM_zero_iff
      loan0 deposit0 loan1 deposit1
      rate0 quantity0 rate1 quantity1 (v - w)).mp hz
  exact sub_eq_zero.mp hzero

#print axioms sourceShearCLM_injective

/-- The eight state-dependent actual SOURCE coefficients define an
injective 33-dimensional row operation at each economic state. -/
theorem economicLogShearCLM_injective
    {S : Type*} [Fintype S] [DecidableEq S]
    (P : Primitives S) (I : InheritedState)
    (Z0 : LocalPrefixCoordinates) (dateOneState recurrent : S)
    (tail : LocalPrefixContinuationRule) (z : Row33) :
    Function.Injective
      (economicLogShearCLM P I Z0 dateOneState recurrent tail z) := by
  unfold economicLogShearCLM
  exact sourceShearCLM_injective _ _ _ _ _ _ _ _

#print axioms economicLogShearCLM_injective

/-- Composition with an injective output row operation preserves
injectivity of an arbitrary 33-dimensional linear derivative. -/
theorem clm_comp_injective_iff
    (E J : Row33 →L[ℝ] Row33)
    (hE : Function.Injective E) :
    Function.Injective (E.comp J) ↔ Function.Injective J := by
  constructor
  · intro h x y hxy
    exact h (congrArg E hxy)
  · intro h x y hxy
    exact h (hE hxy)

#print axioms clm_comp_injective_iff

/-- CONDITIONAL actual SOURCE full-column-rank transport at a root.
This is the real logarithmic SOURCE residual, not a Python substitute.
The equality between the two actual Jacobians is supplied by the
kernel-verified Fréchet transport theorem; the economic root and
differentiability hypotheses remain explicit premises. -/
theorem targetizedLogPrefix33_jacobian_injective_iff
    {S : Type*} [Fintype S] [DecidableEq S]
    (branch : LocalPrefixBranch) (P : Primitives S)
    (I : InheritedState) (Z0 : LocalPrefixCoordinates)
    (dateOneState recurrent : S)
    (tail : LocalPrefixContinuationRule) (z0 : Row33)
    (J : Row33 →L[ℝ] Row33)
    (dA : Row33 →L[ℝ] (Row33 →L[ℝ] Row33))
    (hmatch : P.matchingIntensity = Real.log 2)
    (hadm : ∀ᶠ z in 𝓝 z0,
      TargetBankAdmissible P
        (dateZero P I (localPrefixLogChart Z0 z) dateOneState) ∧
      TargetBankAdmissible P
        (dateOne P (localPrefixLogChart Z0 z)
          dateOneState recurrent tail))
    (hA : HasFDerivAt
      (economicLogShearCLM P I Z0 dateOneState recurrent tail) dA z0)
    (hF : HasFDerivAt
      (localReducedPrefixLogResidualVector branch P I Z0
        dateOneState recurrent tail) J z0)
    (hroot :
      localReducedPrefixLogResidualVector branch P I Z0
        dateOneState recurrent tail z0 = 0) :
    Function.Injective
      (fderiv ℝ
        (targetizedLogPrefix33 branch P I Z0
          dateOneState recurrent tail) z0) ↔
    Function.Injective J := by
  have hd := targetizedLogPrefix33_hasFDerivAt_at_source_root
    branch P I Z0 dateOneState recurrent tail z0 J dA
    hmatch hadm hA hF hroot
  rw [hd.fderiv]
  exact clm_comp_injective_iff
    (economicLogShearCLM P I Z0 dateOneState recurrent tail z0) J
    (economicLogShearCLM_injective
      P I Z0 dateOneState recurrent tail z0)

#print axioms targetizedLogPrefix33_jacobian_injective_iff

end CurrentSourceFullFDeriv
end Ventura26LiquidityAllocation
