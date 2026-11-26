import Ventura26LiquidityAllocation.PaperLemma43CompactPathDerivativeCandidate

/-!
# Appendix Lemma A.1.4: pathwise derivative with PHYSICAL two-firm output

This strengthens compactLossRatioAggregate_hasDerivAt by replacing
the denominator L^b*G^(1-b) by the sum of the two original Cobb-Douglas
firm productions Y_i=A_i*k_i^a*ell_i^b, where the optimal labor
ell_i(s)=L*g_i(s)/(vH*gH(s)+vL*gL(s)) is constructed at every
nearby capital path position s. The historical physical aggregation
theorem is applied locally, without assuming this equality as a premise.

The path parameter s is a continuous local reallocation parameter,
not automatically the discrete calendar date of a DSGE.
-/

namespace Ventura26LiquidityAllocation
namespace CurrentCompact

open Filter

/-- Direct derivative of log(EFFICIENT physical output / ACTUAL physical
output) along differentiable positive capital paths. Same assumptions
as the compact Appendix A.1.4; no global positivity of either path
is required, because positivity at t gives a neighborhood. -/
theorem compactLossRatioPhysical_hasDerivAt
    (vH vL AH AL L a b d : ℝ)
    (kH kL : ℝ → ℝ) (t dkH dkL : ℝ)
    (hvH : 0 < vH) (hvL : 0 < vL)
    (hAH : 0 < AH) (hAL : 0 < AL)
    (hL : 0 < L)
    (ha : 0 < a) (hb : 0 < b) (hd : 0 < d)
    (hsum : a + b + d = 1)
    (hkH : 0 < kH t) (hkL : 0 < kL t)
    (hH : HasDerivAt kH dkH t)
    (hLL : HasDerivAt kL dkL t) :
    let gamma := a / (1 - b)
    let gH := fun s : ℝ => AH ^ (1 / (1 - b)) * (kH s) ^ gamma
    let gL := fun s : ℝ => AL ^ (1 / (1 - b)) * (kL s) ^ gamma
    let cH := vH * AH ^ (1 / (1 - b))
    let cL := vL * AL ^ (1 / (1 - b))
    let ZA := vH * AH ^ (1 / d) + vL * AL ^ (1 / d)
    let K := vH * kH t + vL * kL t
    let G := cH * (kH t) ^ gamma + cL * (kL t) ^ gamma
    let kappaH := vH * kH t / K
    let omegaH := cH * (kH t) ^ gamma / G
    HasDerivAt
      (fun s : ℝ =>
        Real.log
          (((vH * kH s + vL * kL s) ^ a * L ^ b * ZA ^ d) /
            (vH * (AH * (kH s) ^ a *
                (L * gH s / (vH * gH s + vL * gL s)) ^ b) +
              vL * (AL * (kL s) ^ a *
                (L * gL s / (vH * gH s + vL * gL s)) ^ b))))
      (a * (kappaH - omegaH) * (dkH / kH t - dkL / kL t)) t := by
  let gamma : ℝ := a / (1 - b)
  let gH : ℝ → ℝ := fun s => AH ^ (1 / (1 - b)) * (kH s) ^ gamma
  let gL : ℝ → ℝ := fun s => AL ^ (1 / (1 - b)) * (kL s) ^ gamma
  let cH : ℝ := vH * AH ^ (1 / (1 - b))
  let cL : ℝ := vL * AL ^ (1 / (1 - b))
  let ZA : ℝ := vH * AH ^ (1 / d) + vL * AL ^ (1 / d)
  let K : ℝ := vH * kH t + vL * kL t
  let G : ℝ := cH * (kH t) ^ gamma + cL * (kL t) ^ gamma
  let kappaH : ℝ := vH * kH t / K
  let omegaH : ℝ := cH * (kH t) ^ gamma / G
  change HasDerivAt
      (fun s : ℝ =>
        Real.log
          (((vH * kH s + vL * kL s) ^ a * L ^ b * ZA ^ d) /
            (vH * (AH * (kH s) ^ a *
                (L * gH s / (vH * gH s + vL * gL s)) ^ b) +
              vL * (AL * (kL s) ^ a *
                (L * gL s / (vH * gH s + vL * gL s)) ^ b))))
      (a * (kappaH - omegaH) * (dkH / kH t - dkL / kL t)) t
  have hAggregated :
      HasDerivAt
        (fun s : ℝ =>
          Real.log
            (((vH * kH s + vL * kL s) ^ a * L ^ b * ZA ^ d) /
              (L ^ b * (cH * (kH s) ^ gamma +
                cL * (kL s) ^ gamma) ^ (1 - b))))
        (a * (kappaH - omegaH) * (dkH / kH t - dkL / kL t)) t :=
    compactLossRatioAggregate_hasDerivAt
      vH vL AH AL L a b d kH kL t dkH dkL
      hvH hvL hAH hAL hL ha hb hd hsum hkH hkL hH hLL
  have hb1 : b < 1 := by linarith [hsum, ha, hd]
  have hPositiveH : ∀ᶠ s in 𝓝 t, 0 < kH s :=
    ContinuousAt.eventually_lt continuousAt_const hH.continuousAt hkH
  have hPositiveL : ∀ᶠ s in 𝓝 t, 0 < kL s :=
    ContinuousAt.eventually_lt continuousAt_const hLL.continuousAt hkL
  have hPhysicalEventual :
      (fun s : ℝ =>
        Real.log
          (((vH * kH s + vL * kL s) ^ a * L ^ b * ZA ^ d) /
            (vH * (AH * (kH s) ^ a *
                (L * gH s / (vH * gH s + vL * gL s)) ^ b) +
              vL * (AL * (kL s) ^ a *
                (L * gL s / (vH * gH s + vL * gL s)) ^ b)))) =ᶠ[𝓝 t]
        (fun s : ℝ =>
          Real.log
            (((vH * kH s + vL * kL s) ^ a * L ^ b * ZA ^ d) /
              (L ^ b * (cH * (kH s) ^ gamma +
                cL * (kL s) ^ gamma) ^ (1 - b)))) := by
    filter_upwards [hPositiveH, hPositiveL] with s hHs hLs
    have hPhysics :
        vH * (AH * (kH s) ^ a *
            (L * gH s / (vH * gH s + vL * gL s)) ^ b) +
          vL * (AL * (kL s) ^ a *
            (L * gL s / (vH * gH s + vL * gL s)) ^ b) =
          L ^ b * (vH * gH s + vL * gL s) ^ (1 - b) :=
      ProposedPaperAllocationSourceAlgebraBridge.source_two_type_output_at_optimal_labor
        vH vL AH AL (kH s) (kL s) L a b
        hvH hvL hAH hAL hHs hLs hL hb1
    have hGmatch : vH * gH s + vL * gL s =
        cH * (kH s) ^ gamma + cL * (kL s) ^ gamma := by
      dsimp [gH, gL, cH, cL]
      ring
    rw [hPhysics, hGmatch]
  exact hAggregated.congr_of_eventuallyEq hPhysicalEventual

#print axioms compactLossRatioPhysical_hasDerivAt

end CurrentCompact
end Ventura26LiquidityAllocation
