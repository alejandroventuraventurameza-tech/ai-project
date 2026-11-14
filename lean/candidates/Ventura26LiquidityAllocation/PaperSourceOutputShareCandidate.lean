import Ventura26LiquidityAllocation.PaperSourceLossChainRuleCandidate

/-!
# Lemma 4.3: identify the share in d log G with source physical output

The differential of log G uses omegaH = vH*gH/G. This file proves
that, under the paper's optimal labor allocation, omegaH is EXACTLY
the source physical output share vH*yH/(vH*yH+vL*yL).
It prevents substituting a mathematically convenient weight for an
economic object without demonstrating their equality.
-/

namespace Ventura26LiquidityAllocation
namespace ProposedPaperSourceOutputShare

theorem original_output_share_equals_adjusted_weight
    (vH vL AH AL kH kL L a b : ℝ)
    (hvH : 0 < vH) (hvL : 0 < vL)
    (hAH : 0 < AH) (hAL : 0 < AL)
    (hkH : 0 < kH) (hkL : 0 < kL)
    (hL : 0 < L) (hb : b < 1) :
    let gH := AH ^ (1 / (1 - b)) * kH ^ (a / (1 - b))
    let gL := AL ^ (1 / (1 - b)) * kL ^ (a / (1 - b))
    let G := vH * gH + vL * gL
    let yH := AH * kH ^ a * (L * gH / G) ^ b
    let yL := AL * kL ^ a * (L * gL / G) ^ b
    ProposedPaperAllocationLossElasticity.outputShareH vH vL yH yL =
      vH * gH / G := by
  let gH : ℝ := AH ^ (1 / (1 - b)) * kH ^ (a / (1 - b))
  let gL : ℝ := AL ^ (1 / (1 - b)) * kL ^ (a / (1 - b))
  let G : ℝ := vH * gH + vL * gL
  let yH : ℝ := AH * kH ^ a * (L * gH / G) ^ b
  let yL : ℝ := AL * kL ^ a * (L * gL / G) ^ b
  change ProposedPaperAllocationLossElasticity.outputShareH vH vL yH yL =
    vH * gH / G
  have hgH : 0 < gH := by
    dsimp [gH]
    positivity
  have hgL : 0 < gL := by
    dsimp [gL]
    positivity
  have hG : 0 < G := by
    dsimp [G]
    exact add_pos (mul_pos hvH hgH) (mul_pos hvL hgL)
  let scale : ℝ := (L / G) ^ b
  have hscale : 0 < scale := by
    dsimp [scale]
    exact Real.rpow_pos_of_pos (div_pos hL hG) b
  have hyH : yH = scale * gH :=
    ProposedPaperAllocationSourceAlgebraBridge.source_output_at_weighted_labor
      AH kH L G a b hAH hkH hL hG hb
  have hyL : yL = scale * gL :=
    ProposedPaperAllocationSourceAlgebraBridge.source_output_at_weighted_labor
      AL kL L G a b hAL hkL hL hG hb
  have hsum : vH * (scale * gH) + vL * (scale * gL) =
      scale * G := by
    dsimp [G]
    ring
  unfold ProposedPaperAllocationLossElasticity.outputShareH
  rw [hyH, hyL, hsum]
  field_simp [ne_of_gt hscale, ne_of_gt hG] <;> ring

#print axioms original_output_share_equals_adjusted_weight

end ProposedPaperSourceOutputShare
end Ventura26LiquidityAllocation
