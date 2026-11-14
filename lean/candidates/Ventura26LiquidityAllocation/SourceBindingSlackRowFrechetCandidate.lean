import Ventura26LiquidityAllocation.SourceBindingSlackRowScalingCandidate
import Mathlib.Analysis.Calculus.FDeriv.Congr

/-!
# Fréchet derivative of normalized firm-L collateral row at a SOURCE binding root

On the genuine SOURCE positive-log chart, the modified 33-row binding
system replaces the original nominal face residual R_L with normalized
slack S_L. At R_L(z*)=0 and nonzero pledge face Gamma_L(z*),
the differentials satisfy D S_L(z*)=-(1/Gamma_L(z*)) D R_L(z*).

We do not assume pointwise equality between S_L and -R_L/Gamma_L
outside the nonzero-pledge domain. Differentiability of Gamma_L
establishes a genuine open neighborhood of that domain; then
eventual equality transports the actual Fréchet derivative.

This proves a local SOURCE row identity, not full-Jacobian
invertibility, a numerical certificate, or economic existence.
-/

namespace Ventura26LiquidityAllocation

open Filter

/-- General real-valued Fréchet quotient identity at a zero numerator,
on any real normed vector space. -/
theorem sourceNegDiv_fderiv_at_numerator_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f g : E → ℝ) (x : E)
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x)
    (hf0 : f x = 0) (hg0 : g x ≠ 0) :
    fderiv ℝ (fun y => -(f y) / g y) x =
      (-(g x)⁻¹) • fderiv ℝ f x := by
  have hginv : DifferentiableAt ℝ (fun y => (g y)⁻¹) x :=
    hg.inv hg0
  have hmul :
      fderiv ℝ (fun y => f y * (g y)⁻¹) x =
        (g x)⁻¹ • fderiv ℝ f x := by
    rw [fderiv_fun_mul hf hginv, hf0]
    simp
  calc
    fderiv ℝ (fun y => -(f y) / g y) x =
        fderiv ℝ (fun y => -(f y * (g y)⁻¹)) x := by
          congr 1
          funext y
          simp only [div_eq_mul_inv, neg_mul]
    _ = -fderiv ℝ (fun y => f y * (g y)⁻¹) x := by
          rw [fderiv_fun_neg]
    _ = -((g x)⁻¹ • fderiv ℝ f x) := by rw [hmul]
    _ = (-(g x)⁻¹) • fderiv ℝ f x := by simp

#print axioms sourceNegDiv_fderiv_at_numerator_zero

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- Exact SOURCE row-5 Fréchet identity at a *genuine* binding
collateral root. The only assumptions are differentiability of the
raw residual and pledge face in the original log coordinates,
the zero binding residual and a nonzero pledge denominator.

At the root this is an invertible scalar row transformation.
It does not yet establish the equality of all other 32 rows. -/
theorem sourceBindingSlackL_fderiv_eq_scaled_raw_at_root
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
    fderiv ℝ
      (fun z : Fin 33 → ℝ =>
        localNormalizedSlackL P (localPrefixLogChart Z0 z)) zstar =
      (-(sourceBindingLPledgeFace P (localPrefixLogChart Z0 zstar))⁻¹) •
        fderiv ℝ
          (fun z : Fin 33 → ℝ =>
            localReducedPrefixResidual LocalPrefixBranch.binding P I
              (localPrefixLogChart Z0 z) dateOne recurrent tail
              LocalPrefixEquation.firmRegimeZeroL) zstar := by
  let f : (Fin 33 → ℝ) → ℝ :=
    fun z => localReducedPrefixResidual LocalPrefixBranch.binding P I
      (localPrefixLogChart Z0 z) dateOne recurrent tail
      LocalPrefixEquation.firmRegimeZeroL
  let g : (Fin 33 → ℝ) → ℝ :=
    fun z => sourceBindingLPledgeFace P (localPrefixLogChart Z0 z)
  have hf : DifferentiableAt ℝ f zstar := hraw
  have hg : DifferentiableAt ℝ g zstar := hpledge
  have hf0 : f zstar = 0 := hroot
  have hg0 : g zstar ≠ 0 := hne
  have hlocal :
      (fun z : Fin 33 → ℝ =>
        localNormalizedSlackL P (localPrefixLogChart Z0 z)) =ᶠ[𝓝 zstar]
      (fun z => -(f z) / g z) := by
    filter_upwards [hg.continuousAt.eventually_ne hg0] with z hz
    exact sourceBindingNormalizedSlackL_eq_neg_raw_div_pledge
      P I (localPrefixLogChart Z0 z) dateOne recurrent tail hz
  have hquot : DifferentiableAt ℝ (fun z => -(f z) / g z) zstar := by
    simpa only [div_eq_mul_inv] using
      hf.neg.mul (hg.inv hg0)
  have htrans :
      fderiv ℝ
        (fun z : Fin 33 → ℝ =>
          localNormalizedSlackL P (localPrefixLogChart Z0 z)) zstar =
      fderiv ℝ (fun z => -(f z) / g z) zstar :=
    (hquot.hasFDerivAt.congr_of_eventuallyEq hlocal).fderiv
  calc
    fderiv ℝ
        (fun z : Fin 33 → ℝ =>
          localNormalizedSlackL P (localPrefixLogChart Z0 z)) zstar =
        fderiv ℝ (fun z => -(f z) / g z) zstar := htrans
    _ = (-(g zstar)⁻¹) • fderiv ℝ f zstar :=
      sourceNegDiv_fderiv_at_numerator_zero f g zstar hf hg hf0 hg0

#print axioms sourceBindingSlackL_fderiv_eq_scaled_raw_at_root

end Ventura26LiquidityAllocation
