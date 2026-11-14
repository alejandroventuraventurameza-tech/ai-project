import Ventura26LiquidityAllocation.SourceReduced33PointwiseChartCandidate
import Mathlib.Analysis.Calculus.FDeriv.Prod

/-!
# Exact Frechet transport on the SOURCE reduced 33-dimensional chart

Let F(z,h) be the ORIGINAL 34-output SOURCE augmented residual and G(u,h)
its 33-output economic reduction after exact elimination of the stationary
L funding-dual condition. The previously proved SOURCE chart identity is

  F(L(u),h) = (G(u,h), 0)

at EVERY reduced coordinate, under the explicit stationary positive hypotheses.

This module transfers that literal equality to differentiability and Frechet
derivatives: D(F o L)(w) . d = (DG(w) . d, 0). In particular the eliminated
dual row has exactly zero derivative in every reduced tangent direction,
and injectivity (full column rank) of the embedded 34x33 derivative is
equivalent to injectivity of the genuine SOURCE reduced 33x33 derivative.

None of this asserts that DG is invertible, bounds the SOURCE derivatives
over a box, identifies the float Python implementation, constructs a root,
or certifies dynamic competitive equilibrium.
-/

namespace Ventura26LiquidityAllocation

open ProposedLocalScalarAugmented34Source
open ProposedLocalScalarEconomicSlice

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- Differentiability of the 34-output SOURCE residual restricted to the
exact funding-dual chart is equivalent to differentiability of G. -/
theorem sourceReduced33_chart_differentiableAt_iff
    (P : Primitives S) (I : InheritedState)
    (Z0 : LocalPrefixCoordinates) (dateOne recurrent : S)
    (tail : LocalPrefixContinuationRule)
    (wstar : (Fin 32 → ℝ) × ℝ)
    (hsigma : P.entrepreneurRiskAversion = 1)
    (hc_same : Z0.controlsZero.consumptionL = Z0.controlsOne.consumptionL)
    (hc_positive : 0 < Z0.controlsZero.consumptionL)
    (hpi : Z0.controlsOne.inflation = 1)
    (hr : 0 < Z0.controlsZero.loanRate)
    (hbeta : 0 < P.entrepreneurDiscount) :
    DifferentiableAt ℝ
      (fun w : (Fin 32 → ℝ) × ℝ =>
        augmentedBoundaryZeroResidual P I Z0 dateOne recurrent tail
          (sourceFundingDualLift32 P Z0 w.1) w.2) wstar ↔
    DifferentiableAt ℝ
      (sourceReduced33EconomicMap P I Z0 dateOne recurrent tail) wstar := by
  let F : ((Fin 32 → ℝ) × ℝ) → (Fin 33 → ℝ) × ℝ :=
    fun w => augmentedBoundaryZeroResidual P I Z0 dateOne recurrent tail
      (sourceFundingDualLift32 P Z0 w.1) w.2
  let G : ((Fin 32 → ℝ) × ℝ) → (Fin 33 → ℝ) :=
    sourceReduced33EconomicMap P I Z0 dateOne recurrent tail
  have hfun : F = (fun w => (G w, (0 : ℝ))) := by
    funext w
    exact sourceReduced33_pointwise_reconstruction
      P I Z0 dateOne recurrent tail w.1 w.2
      hsigma hc_same hc_positive hpi hr hbeta
  change DifferentiableAt ℝ F wstar ↔ DifferentiableAt ℝ G wstar
  rw [hfun]
  constructor
  · intro h
    exact h.fst
  · intro h
    exact h.prodMk (differentiableAt_const (0 : ℝ))

#print axioms sourceReduced33_chart_differentiableAt_iff

/-- The first 33 derivative coordinates of the embedded ORIGINAL SOURCE
residual equal the genuine SOURCE reduced economic Frechet derivative. -/
theorem sourceReduced33_chart_fderiv_first
    (P : Primitives S) (I : InheritedState)
    (Z0 : LocalPrefixCoordinates) (dateOne recurrent : S)
    (tail : LocalPrefixContinuationRule)
    (wstar d : (Fin 32 → ℝ) × ℝ)
    (hsigma : P.entrepreneurRiskAversion = 1)
    (hc_same : Z0.controlsZero.consumptionL = Z0.controlsOne.consumptionL)
    (hc_positive : 0 < Z0.controlsZero.consumptionL)
    (hpi : Z0.controlsOne.inflation = 1)
    (hr : 0 < Z0.controlsZero.loanRate)
    (hbeta : 0 < P.entrepreneurDiscount)
    (hG : DifferentiableAt ℝ
      (sourceReduced33EconomicMap P I Z0 dateOne recurrent tail) wstar) :
    ((fderiv ℝ
      (fun w : (Fin 32 → ℝ) × ℝ =>
        augmentedBoundaryZeroResidual P I Z0 dateOne recurrent tail
          (sourceFundingDualLift32 P Z0 w.1) w.2)
      wstar) d).1 =
    (fderiv ℝ (sourceReduced33EconomicMap
      P I Z0 dateOne recurrent tail) wstar) d := by
  let F : ((Fin 32 → ℝ) × ℝ) → (Fin 33 → ℝ) × ℝ :=
    fun w => augmentedBoundaryZeroResidual P I Z0 dateOne recurrent tail
      (sourceFundingDualLift32 P Z0 w.1) w.2
  let G : ((Fin 32 → ℝ) × ℝ) → (Fin 33 → ℝ) :=
    sourceReduced33EconomicMap P I Z0 dateOne recurrent tail
  have hF : DifferentiableAt ℝ F wstar :=
    (sourceReduced33_chart_differentiableAt_iff
      P I Z0 dateOne recurrent tail wstar
      hsigma hc_same hc_positive hpi hr hbeta).2 hG
  have hfirst : (fun w => (F w).1) = G := rfl
  change ((fderiv ℝ F wstar) d).1 = (fderiv ℝ G wstar) d
  calc
    ((fderiv ℝ F wstar) d).1 =
        (fderiv ℝ (fun w => (F w).1) wstar) d := by
          rw [fderiv.fst hF]
          rfl
    _ = (fderiv ℝ G wstar) d := by rw [hfirst]

#print axioms sourceReduced33_chart_fderiv_first

/-- The ORIGINAL SOURCE L funding-dual derivative is zero in EVERY
tangent direction of the exact 33-dimensional reduced chart. -/
theorem sourceReduced33_chart_fderiv_dual_zero
    (P : Primitives S) (I : InheritedState)
    (Z0 : LocalPrefixCoordinates) (dateOne recurrent : S)
    (tail : LocalPrefixContinuationRule)
    (wstar d : (Fin 32 → ℝ) × ℝ)
    (hsigma : P.entrepreneurRiskAversion = 1)
    (hc_same : Z0.controlsZero.consumptionL = Z0.controlsOne.consumptionL)
    (hc_positive : 0 < Z0.controlsZero.consumptionL)
    (hpi : Z0.controlsOne.inflation = 1)
    (hr : 0 < Z0.controlsZero.loanRate)
    (hbeta : 0 < P.entrepreneurDiscount)
    (hG : DifferentiableAt ℝ
      (sourceReduced33EconomicMap P I Z0 dateOne recurrent tail) wstar) :
    ((fderiv ℝ
      (fun w : (Fin 32 → ℝ) × ℝ =>
        augmentedBoundaryZeroResidual P I Z0 dateOne recurrent tail
          (sourceFundingDualLift32 P Z0 w.1) w.2)
      wstar) d).2 = 0 := by
  let F : ((Fin 32 → ℝ) × ℝ) → (Fin 33 → ℝ) × ℝ :=
    fun w => augmentedBoundaryZeroResidual P I Z0 dateOne recurrent tail
      (sourceFundingDualLift32 P Z0 w.1) w.2
  have hF : DifferentiableAt ℝ F wstar :=
    (sourceReduced33_chart_differentiableAt_iff
      P I Z0 dateOne recurrent tail wstar
      hsigma hc_same hc_positive hpi hr hbeta).2 hG
  have hdual : (fun w => (F w).2) =
      (fun _ : (Fin 32 → ℝ) × ℝ => (0 : ℝ)) := by
    funext w
    exact sourceFundingDualLift32_dual_zero P Z0 w.1
      hsigma hc_same hc_positive hpi hr hbeta
  change ((fderiv ℝ F wstar) d).2 = 0
  calc
    ((fderiv ℝ F wstar) d).2 =
      (fderiv ℝ (fun w => (F w).2) wstar) d := by
        rw [fderiv.snd hF]
        rfl
    _ = 0 := by rw [hdual]; simp

#print axioms sourceReduced33_chart_fderiv_dual_zero

/-- Exact reduced SOURCE Frechet factorization with NO postulated
Jacobian identity, only stated regularity of the reduced economic map. -/
theorem sourceReduced33_chart_fderiv_factorization
    (P : Primitives S) (I : InheritedState)
    (Z0 : LocalPrefixCoordinates) (dateOne recurrent : S)
    (tail : LocalPrefixContinuationRule)
    (wstar d : (Fin 32 → ℝ) × ℝ)
    (hsigma : P.entrepreneurRiskAversion = 1)
    (hc_same : Z0.controlsZero.consumptionL = Z0.controlsOne.consumptionL)
    (hc_positive : 0 < Z0.controlsZero.consumptionL)
    (hpi : Z0.controlsOne.inflation = 1)
    (hr : 0 < Z0.controlsZero.loanRate)
    (hbeta : 0 < P.entrepreneurDiscount)
    (hG : DifferentiableAt ℝ
      (sourceReduced33EconomicMap P I Z0 dateOne recurrent tail) wstar) :
    (fderiv ℝ
      (fun w : (Fin 32 → ℝ) × ℝ =>
        augmentedBoundaryZeroResidual P I Z0 dateOne recurrent tail
          (sourceFundingDualLift32 P Z0 w.1) w.2)
      wstar) d =
    ((fderiv ℝ (sourceReduced33EconomicMap
      P I Z0 dateOne recurrent tail) wstar) d, (0 : ℝ)) := by
  apply Prod.ext
  · exact sourceReduced33_chart_fderiv_first
      P I Z0 dateOne recurrent tail wstar d
      hsigma hc_same hc_positive hpi hr hbeta hG
  · exact sourceReduced33_chart_fderiv_dual_zero
      P I Z0 dateOne recurrent tail wstar d
      hsigma hc_same hc_positive hpi hr hbeta hG

#print axioms sourceReduced33_chart_fderiv_factorization

/-- The embedded 34x33 SOURCE derivative has full column rank exactly
when the true reduced 33x33 SOURCE derivative is injective.
Neither condition is claimed to hold at the numerical Python root. -/
theorem sourceReduced33_chart_fderiv_injective_iff
    (P : Primitives S) (I : InheritedState)
    (Z0 : LocalPrefixCoordinates) (dateOne recurrent : S)
    (tail : LocalPrefixContinuationRule)
    (wstar : (Fin 32 → ℝ) × ℝ)
    (hsigma : P.entrepreneurRiskAversion = 1)
    (hc_same : Z0.controlsZero.consumptionL = Z0.controlsOne.consumptionL)
    (hc_positive : 0 < Z0.controlsZero.consumptionL)
    (hpi : Z0.controlsOne.inflation = 1)
    (hr : 0 < Z0.controlsZero.loanRate)
    (hbeta : 0 < P.entrepreneurDiscount)
    (hG : DifferentiableAt ℝ
      (sourceReduced33EconomicMap P I Z0 dateOne recurrent tail) wstar) :
    Function.Injective
      (fderiv ℝ
        (fun w : (Fin 32 → ℝ) × ℝ =>
          augmentedBoundaryZeroResidual P I Z0 dateOne recurrent tail
            (sourceFundingDualLift32 P Z0 w.1) w.2)
        wstar) ↔
    Function.Injective
      (fderiv ℝ (sourceReduced33EconomicMap
        P I Z0 dateOne recurrent tail) wstar) := by
  let F : ((Fin 32 → ℝ) × ℝ) → (Fin 33 → ℝ) × ℝ :=
    fun w => augmentedBoundaryZeroResidual P I Z0 dateOne recurrent tail
      (sourceFundingDualLift32 P Z0 w.1) w.2
  let G : ((Fin 32 → ℝ) × ℝ) → (Fin 33 → ℝ) :=
    sourceReduced33EconomicMap P I Z0 dateOne recurrent tail
  have hfactor : ∀ d : (Fin 32 → ℝ) × ℝ,
      (fderiv ℝ F wstar) d = ((fderiv ℝ G wstar) d, (0 : ℝ)) :=
    fun d => sourceReduced33_chart_fderiv_factorization
      P I Z0 dateOne recurrent tail wstar d
      hsigma hc_same hc_positive hpi hr hbeta hG
  change Function.Injective (fderiv ℝ F wstar) ↔
    Function.Injective (fderiv ℝ G wstar)
  constructor
  · intro hf d1 d2 hEq
    apply hf
    rw [hfactor d1, hfactor d2, hEq]
  · intro hg d1 d2 hEq
    have hfirst := congrArg Prod.fst hEq
    rw [hfactor d1, hfactor d2] at hfirst
    exact hg hfirst

#print axioms sourceReduced33_chart_fderiv_injective_iff

end Ventura26LiquidityAllocation
