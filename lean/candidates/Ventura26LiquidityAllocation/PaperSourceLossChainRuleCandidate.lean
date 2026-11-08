import Ventura26LiquidityAllocation.PaperSourceDifferentialSharesCandidate
import Ventura26LiquidityAllocation.PaperAllocationLossElasticityCandidate

/-!
# Lemma 4.3: exact source chain rule for the allocative-loss differential

This theorem is for ANY differentiable positive paths of the two firms'
physical capital stocks. It uses:
 * derivative of source K(t) = vH*kH(t)+vL*kL(t);
 * derivative of source G(t) = sum_i v_i*A_i^(1/(1-b))*k_i(t)^(a/(1-b));
 * exact original source shares kappaH and omegaH;
 * the previously kernel-verified coefficient cancellation.

No equilibrium comparative statics, policy perturbation, or endogenous
capital-law equations are assumed or established here.
-/

namespace Ventura26LiquidityAllocation
namespace ProposedPaperSourceLossChainRule

/-- At any time t with strictly positive firm capital, positive
population masses/productivity, common technology elasticities and
a < 1-b, the exact log-loss expression has derivative
a*(kappaH-omegaH)*d log(kH/kL).
The constant efficient-productivity normalization ZA is constructed
directly from the original A_i, not treated as a free number.
The d term does not affect the derivative because A_i and masses
are fixed along the capital path. -/
theorem original_source_loss_hasDerivAt_relative_capital
    (vH vL AH AL a b d : ℝ)
    (kH kL : ℝ → ℝ) (t dkH dkL : ℝ)
    (hvH : 0 < vH) (hvL : 0 < vL)
    (hAH : 0 < AH) (hAL : 0 < AL)
    (hkH : 0 < kH t) (hkL : 0 < kL t)
    (hb : b < 1)
    (hH : HasDerivAt kH dkH t)
    (hL : HasDerivAt kL dkL t) :
    let gamma := a / (1 - b)
    let cH := vH * AH ^ (1 / (1 - b))
    let cL := vL * AL ^ (1 / (1 - b))
    let ZA := vH * AH ^ (1 / d) + vL * AL ^ (1 / d)
    let K := vH * kH t + vL * kL t
    let G := cH * (kH t) ^ gamma + cL * (kL t) ^ gamma
    let kappaH := vH * kH t / K
    let omegaH := cH * (kH t) ^ gamma / G
    HasDerivAt
      (fun s => a * Real.log (vH * kH s + vL * kL s) +
        d * Real.log ZA -
        (1 - b) * Real.log (cH * (kH s) ^ gamma + cL * (kL s) ^ gamma))
      (a * (kappaH - omegaH) *
        (dkH / kH t - dkL / kL t)) t := by
  let gamma : ℝ := a / (1 - b)
  let cH : ℝ := vH * AH ^ (1 / (1 - b))
  let cL : ℝ := vL * AL ^ (1 / (1 - b))
  let ZA : ℝ := vH * AH ^ (1 / d) + vL * AL ^ (1 / d)
  let K : ℝ := vH * kH t + vL * kL t
  let G : ℝ := cH * (kH t) ^ gamma + cL * (kL t) ^ gamma
  let kappaH : ℝ := vH * kH t / K
  let omegaH : ℝ := cH * (kH t) ^ gamma / G
  change HasDerivAt
    (fun s => a * Real.log (vH * kH s + vL * kL s) +
        d * Real.log ZA -
        (1 - b) * Real.log (cH * (kH s) ^ gamma + cL * (kL s) ^ gamma))
    (a * (kappaH - omegaH) * (dkH / kH t - dkL / kL t)) t
  have hcH : 0 < cH := by
    dsimp [cH]
    exact mul_pos hvH (Real.rpow_pos_of_pos hAH _)
  have hcL : 0 < cL := by
    dsimp [cL]
    exact mul_pos hvL (Real.rpow_pos_of_pos hAL _)
  have hK : 0 < K := by dsimp [K]; positivity
  have hG : 0 < G := by dsimp [G]; positivity
  have hlogK : HasDerivAt
      (fun s => Real.log (vH * kH s + vL * kL s))
      (K⁻¹ * (vH * dkH + vL * dkL)) t :=
    ProposedPaperSourceDifferentiation.source_log_total_capital_hasDerivAt
      vH vL kH kL t dkH dkL hK hH hL
  have hlogG : HasDerivAt
      (fun s => Real.log (cH * (kH s) ^ gamma + cL * (kL s) ^ gamma))
      (G⁻¹ *
        (cH * (gamma * (kH t) ^ (gamma - 1) * dkH) +
          cL * (gamma * (kL t) ^ (gamma - 1) * dkL))) t :=
    ProposedPaperSourceDifferentiation.source_log_productivity_aggregate_hasDerivAt
      vH vL AH AL a b kH kL t dkH dkL hkH hkL hG hH hL
  have hshareK :
      K⁻¹ * (vH * dkH + vL * dkL) =
        kappaH * (dkH / kH t) + (1 - kappaH) * (dkL / kL t) :=
    ProposedPaperSourceDifferentialShares.original_capital_log_share_identity
      vH vL (kH t) (kL t) dkH dkL hkH hkL hvH hvL
  have hshareG :
      G⁻¹ * (cH * (gamma * (kH t) ^ (gamma - 1) * dkH) +
        cL * (gamma * (kL t) ^ (gamma - 1) * dkL)) =
        gamma * (omegaH * (dkH / kH t) +
          (1 - omegaH) * (dkL / kL t)) :=
    ProposedPaperSourceDifferentialShares.original_productivity_log_share_identity
      cH cL (kH t) (kL t) gamma dkH dkL hcH hcL hkH hkL
  have hcoeff :
      a * (K⁻¹ * (vH * dkH + vL * dkL)) -
        (1 - b) * (G⁻¹ *
          (cH * (gamma * (kH t) ^ (gamma - 1) * dkH) +
            cL * (gamma * (kL t) ^ (gamma - 1) * dkL))) =
        a * (kappaH - omegaH) * (dkH / kH t - dkL / kL t) := by
    rw [hshareK, hshareG]
    exact ProposedPaperAllocationLossElasticity.allocation_loss_log_differential_algebra
      a b kappaH omegaH (dkH / kH t) (dkL / kL t) hb
  have hconst :
      HasDerivAt (fun _ : ℝ => d * Real.log ZA) 0 t :=
    hasDerivAt_const t (d * Real.log ZA)
  have hsource : HasDerivAt
      (fun s => a * Real.log (vH * kH s + vL * kL s) +
        d * Real.log ZA -
        (1 - b) * Real.log (cH * (kH s) ^ gamma + cL * (kL s) ^ gamma))
      (a * (K⁻¹ * (vH * dkH + vL * dkL)) -
        (1 - b) * (G⁻¹ *
          (cH * (gamma * (kH t) ^ (gamma - 1) * dkH) +
            cL * (gamma * (kL t) ^ (gamma - 1) * dkL)))) t := by
    simpa only [add_zero] using
      ((hlogK.const_mul a).add hconst).sub (hlogG.const_mul (1 - b))
  rw [hcoeff] at hsource
  exact hsource

#print axioms original_source_loss_hasDerivAt_relative_capital

end ProposedPaperSourceLossChainRule
end Ventura26LiquidityAllocation
