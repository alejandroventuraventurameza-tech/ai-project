import Ventura26LiquidityAllocation.CurrentSourceTwoDateFDerivRank

/-!
# Exact inverse and conditional inverse-Jacobian transport for actual SOURCE

The six banking rows of the 33-equation two-date SOURCE prefix are
targetized by a triangular linear shear E with eight REAL economic
coefficients. Since all donor monetary-rule rows are unchanged,
the inverse is exactly the shear with negated coefficients.

The proof here is algebraic and valid for all finite real coefficients,
without a claim that any SOURCE equilibrium root exists. Under the
SAME explicit differentiability, banking-domain and root premises as
the prior SOURCE Frechet transport, an available two-sided SOURCE
Jacobian inverse induces a two-sided targetized Jacobian inverse.
The norm inequality is symbolic; it is NOT a SOURCE numerical bound.
-/

namespace Ventura26LiquidityAllocation
namespace CurrentSourceFullFDeriv

open CurrentSourceTwoDateBank
open CurrentSourceFiveBankBridge
open scoped Topology

/-- A continuous linear inverse candidate: negate precisely the eight
SOURCE cross-row coefficients, retaining the true 33-row index order. -/
noncomputable def sourceShearInvCLM
    (loan0 deposit0 loan1 deposit1
      rate0 quantity0 rate1 quantity1 : ℝ) :
    Row33 →L[ℝ] Row33 :=
  sourceShearCLM
    (-loan0) (-deposit0) (-loan1) (-deposit1)
    (-rate0) (-quantity0) (-rate1) (-quantity1)

/-- For every real coefficient vector, the negative shear is a left
inverse of the original SOURCE six-row operation. -/
theorem sourceShearInvCLM_left
    (loan0 deposit0 loan1 deposit1
      rate0 quantity0 rate1 quantity1 : ℝ)
    (v : Row33) :
    sourceShearInvCLM
      loan0 deposit0 loan1 deposit1
      rate0 quantity0 rate1 quantity1
      (sourceShearCLM
        loan0 deposit0 loan1 deposit1
        rate0 quantity0 rate1 quantity1 v) = v := by
  funext i
  fin_cases i <;>
    simp [sourceShearInvCLM, sourceShearCLM, rowCoord] <;> ring

#print axioms sourceShearInvCLM_left

/-- The inverse also works on the other side, establishing bijectivity
of the exact state-dependent banking row operation. -/
theorem sourceShearInvCLM_right
    (loan0 deposit0 loan1 deposit1
      rate0 quantity0 rate1 quantity1 : ℝ)
    (v : Row33) :
    sourceShearCLM
      loan0 deposit0 loan1 deposit1
      rate0 quantity0 rate1 quantity1
      (sourceShearInvCLM
        loan0 deposit0 loan1 deposit1
        rate0 quantity0 rate1 quantity1 v) = v := by
  simpa only [sourceShearInvCLM, neg_neg] using
    (sourceShearInvCLM_left
      (-loan0) (-deposit0) (-loan1) (-deposit1)
      (-rate0) (-quantity0) (-rate1) (-quantity1) v)

#print axioms sourceShearInvCLM_right

/-- Apply the inverse to SOURCE economic coefficients at the actual
logarithmic state; no Python surrogate coefficients are introduced. -/
noncomputable def economicLogShearInvCLM
    {S : Type*} [Fintype S] [DecidableEq S]
    (P : Primitives S) (I : InheritedState)
    (Z0 : LocalPrefixCoordinates) (dateOneState recurrent : S)
    (tail : LocalPrefixContinuationRule) (z : Row33) :
    Row33 →L[ℝ] Row33 :=
  let Z := localPrefixLogChart Z0 z
  let d0 := dateZero P I Z dateOneState
  let d1 := dateOne P Z dateOneState recurrent tail
  sourceShearInvCLM
    (sourceLoanCross P d0) (sourceDepositCross P d0)
    (sourceLoanCross P d1) (sourceDepositCross P d1)
    (sourceBalanceRateCross P d0) (sourceBalanceQuantityCross P d0)
    (sourceBalanceRateCross P d1) (sourceBalanceQuantityCross P d1)

theorem economicLogShearInvCLM_left
    {S : Type*} [Fintype S] [DecidableEq S]
    (P : Primitives S) (I : InheritedState)
    (Z0 : LocalPrefixCoordinates) (dateOneState recurrent : S)
    (tail : LocalPrefixContinuationRule) (z v : Row33) :
    economicLogShearInvCLM P I Z0 dateOneState recurrent tail z
      (economicLogShearCLM P I Z0 dateOneState recurrent tail z v) = v := by
  unfold economicLogShearInvCLM economicLogShearCLM
  exact sourceShearInvCLM_left _ _ _ _ _ _ _ _ v

#print axioms economicLogShearInvCLM_left

theorem economicLogShearInvCLM_right
    {S : Type*} [Fintype S] [DecidableEq S]
    (P : Primitives S) (I : InheritedState)
    (Z0 : LocalPrefixCoordinates) (dateOneState recurrent : S)
    (tail : LocalPrefixContinuationRule) (z v : Row33) :
    economicLogShearCLM P I Z0 dateOneState recurrent tail z
      (economicLogShearInvCLM P I Z0 dateOneState recurrent tail z v) = v := by
  unfold economicLogShearInvCLM economicLogShearCLM
  exact sourceShearInvCLM_right _ _ _ _ _ _ _ _ v

#print axioms economicLogShearInvCLM_right

/-- If E and J have two-sided continuous-linear inverses, J^-1 E^-1
inverts E J on both sides. This is strictly conditional algebra. -/
theorem twoSidedInverse_of_shear_comp
    (E J Einv Jinv : Row33 →L[ℝ] Row33)
    (hEl : Function.LeftInverse Einv E)
    (hEr : Function.RightInverse Einv E)
    (hJl : Function.LeftInverse Jinv J)
    (hJr : Function.RightInverse Jinv J) :
    Function.LeftInverse (Jinv.comp Einv) (E.comp J) ∧
    Function.RightInverse (Jinv.comp Einv) (E.comp J) := by
  constructor
  · intro x
    change Jinv (Einv (E (J x))) = x
    rw [hEl (J x)]
    exact hJl x
  · intro x
    change E (J (Jinv (Einv x))) = x
    rw [hJr (Einv x)]
    exact hEr x

#print axioms twoSidedInverse_of_shear_comp

/-- Conditional SOURCE inverse transport at a COMMON exact root.
The inequality involves the norm of the actual economic E^-1,
not a numerical certificate for that norm or the SOURCE Jacobian. -/
theorem targetizedLogPrefix33_inverse_from_source
    {S : Type*} [Fintype S] [DecidableEq S]
    (branch : LocalPrefixBranch) (P : Primitives S)
    (I : InheritedState) (Z0 : LocalPrefixCoordinates)
    (dateOneState recurrent : S)
    (tail : LocalPrefixContinuationRule) (z0 : Row33)
    (J Jinv : Row33 →L[ℝ] Row33)
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
        dateOneState recurrent tail z0 = 0)
    (hJl : Function.LeftInverse Jinv J)
    (hJr : Function.RightInverse Jinv J) :
    ∃ K : Row33 →L[ℝ] Row33,
      Function.LeftInverse K
        (fderiv ℝ
          (targetizedLogPrefix33 branch P I Z0
            dateOneState recurrent tail) z0) ∧
      Function.RightInverse K
        (fderiv ℝ
          (targetizedLogPrefix33 branch P I Z0
            dateOneState recurrent tail) z0) ∧
      ‖K‖ ≤ ‖Jinv‖ *
        ‖economicLogShearInvCLM P I Z0
          dateOneState recurrent tail z0‖ := by
  let E := economicLogShearCLM P I Z0 dateOneState recurrent tail z0
  let Einv := economicLogShearInvCLM P I Z0 dateOneState recurrent tail z0
  have hderiv := (targetizedLogPrefix33_hasFDerivAt_at_source_root
    branch P I Z0 dateOneState recurrent tail z0 J dA
    hmatch hadm hA hF hroot).fderiv
  have hEl : Function.LeftInverse Einv E :=
    fun v => economicLogShearInvCLM_left
      P I Z0 dateOneState recurrent tail z0 v
  have hEr : Function.RightInverse Einv E :=
    fun v => economicLogShearInvCLM_right
      P I Z0 dateOneState recurrent tail z0 v
  obtain ⟨hl, hr⟩ :=
    twoSidedInverse_of_shear_comp E J Einv Jinv hEl hEr hJl hJr
  refine ⟨Jinv.comp Einv, ?_, ?_, ?_⟩
  · rw [hderiv]
    exact hl
  · rw [hderiv]
    exact hr
  · exact ContinuousLinearMap.opNorm_comp_le Jinv Einv

#print axioms targetizedLogPrefix33_inverse_from_source

end CurrentSourceFullFDeriv
end Ventura26LiquidityAllocation
