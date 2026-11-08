import Ventura26LiquidityAllocation.PaperSourceDifferentiationCandidate

/-!
# Lemma 4.3: derive logarithmic capital/share coefficients from K and G

These are SOURCE algebra lemmas. The shares are not arbitrary reals:
kappa_H = vH*kH/(vH*kH+vL*kL) and
omega_H = cH*kH^gamma/(cH*kH^gamma+cL*kL^gamma).
No derivative is postulated in this module; the HasDerivAt proofs of the
underlying source K and G functions are imported from the previous module.
-/

namespace Ventura26LiquidityAllocation
namespace ProposedPaperSourceDifferentialShares

/-- Log K(t) derivative expressed using the capital shares of both types.
The identity derives the second share from the original budget exactly. -/
theorem original_capital_log_share_identity
    (vH vL kH kL dkH dkL : ℝ)
    (hkH : 0 < kH) (hkL : 0 < kL)
    (hvH : 0 < vH) (hvL : 0 < vL) :
    let K := vH * kH + vL * kL
    let kappaH := vH * kH / K
    K⁻¹ * (vH * dkH + vL * dkL) =
      kappaH * (dkH / kH) + (1 - kappaH) * (dkL / kL) := by
  let K : ℝ := vH * kH + vL * kL
  let kappaH : ℝ := vH * kH / K
  change K⁻¹ * (vH * dkH + vL * dkL) =
    kappaH * (dkH / kH) + (1 - kappaH) * (dkL / kL)
  have hK : 0 < K := by
    dsimp [K]
    positivity
  have hother : 1 - kappaH = vL * kL / K := by
    dsimp [kappaH]
    field_simp [ne_of_gt hK] <;> dsimp [K] <;> ring
  rw [hother]
  dsimp [kappaH]
  field_simp [ne_of_gt hK, ne_of_gt hkH, ne_of_gt hkL] <;> ring

/-- Log G(t) derivative expressed using SOURCE adjusted productivity
weights. The crucial exponent identity k^(gamma-1) = k^gamma/k
holds only when each source capital is strictly positive. -/
theorem original_productivity_log_share_identity
    (cH cL kH kL gamma dkH dkL : ℝ)
    (hcH : 0 < cH) (hcL : 0 < cL)
    (hkH : 0 < kH) (hkL : 0 < kL) :
    let G := cH * kH ^ gamma + cL * kL ^ gamma
    let omegaH := cH * kH ^ gamma / G
    G⁻¹ * (cH * (gamma * kH ^ (gamma - 1) * dkH) +
      cL * (gamma * kL ^ (gamma - 1) * dkL)) =
      gamma * (omegaH * (dkH / kH) +
        (1 - omegaH) * (dkL / kL)) := by
  let G : ℝ := cH * kH ^ gamma + cL * kL ^ gamma
  let omegaH : ℝ := cH * kH ^ gamma / G
  change G⁻¹ *
    (cH * (gamma * kH ^ (gamma - 1) * dkH) +
      cL * (gamma * kL ^ (gamma - 1) * dkL)) =
    gamma * (omegaH * (dkH / kH) +
      (1 - omegaH) * (dkL / kL))
  have hG : 0 < G := by
    dsimp [G]
    positivity
  have hother : 1 - omegaH = cL * kL ^ gamma / G := by
    dsimp [omegaH]
    field_simp [ne_of_gt hG] <;> dsimp [G] <;> ring
  have hpowH : kH ^ (gamma - 1) = kH ^ gamma / kH := by
    rw [Real.rpow_sub hkH gamma 1]
    simp
  have hpowL : kL ^ (gamma - 1) = kL ^ gamma / kL := by
    rw [Real.rpow_sub hkL gamma 1]
    simp
  rw [hother, hpowH, hpowL]
  dsimp [omegaH]
  field_simp [ne_of_gt hG, ne_of_gt hkH, ne_of_gt hkL] <;> ring

#print axioms original_capital_log_share_identity
#print axioms original_productivity_log_share_identity

end ProposedPaperSourceDifferentialShares
end Ventura26LiquidityAllocation
