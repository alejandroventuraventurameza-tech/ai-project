import Ventura26LiquidityAllocation.PaperSourceLogCapitalRatioCandidate

/-!
# Lemma 4.3 — single pathwise derivative and physical-product-share bundle

This proof starts with differentiable original firm capital paths and fixed
positive masses/productivities. The physical output Y_i uses the proven
optimal labor allocation. The conclusion combines:
 (1) full HasDerivAt of the original logarithmic allocative loss;
 (2) HasDerivAt of the original log capital ratio;
 (3) exact equality omega_H = physical output share;
 (4) the equivalence of higher output share and higher physical MPK,
     written as alpha * (Y_i/k_i), with alpha > 0.

This does NOT assert that the paths solve a monetary equilibrium.
-/

namespace Ventura26LiquidityAllocation
namespace ProposedPaperLemma43DynamicIntegrated

theorem original_source_dynamic_lemma43_bundle
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
    let cH := vH * AH ^ (1 / (1 - b))
    let cL := vL * AL ^ (1 / (1 - b))
    let ZA := vH * AH ^ (1 / d) + vL * AL ^ (1 / d)
    let K := vH * kH t + vL * kL t
    let G := cH * (kH t) ^ gamma + cL * (kL t) ^ gamma
    let kappaH := vH * kH t / K
    let omegaH := cH * (kH t) ^ gamma / G
    let gH := AH ^ (1 / (1 - b)) * (kH t) ^ gamma
    let gL := AL ^ (1 / (1 - b)) * (kL t) ^ gamma
    let Gout := vH * gH + vL * gL
    let ellH := L * gH / Gout
    let ellL := L * gL / Gout
    let YH := AH * (kH t) ^ a * ellH ^ b
    let YL := AL * (kL t) ^ a * ellL ^ b
    HasDerivAt
      (fun s => a * Real.log (vH * kH s + vL * kL s) +
        d * Real.log ZA -
        (1 - b) * Real.log
          (cH * (kH s) ^ gamma + cL * (kL s) ^ gamma))
      (a * (kappaH - omegaH) *
        (dkH / kH t - dkL / kL t)) t ∧
    HasDerivAt
      (fun s => Real.log (kH s / kL s))
      (dkH / kH t - dkL / kL t) t ∧
    ProposedPaperAllocationLossElasticity.outputShareH vH vL YH YL = omegaH ∧
    (ProposedPaperAllocationLossElasticity.outputShareH vH vL YH YL >
        ProposedPaperAllocationLossElasticity.capitalShareH vH vL (kH t) (kL t) ↔
      a * (YH / kH t) > a * (YL / kL t)) := by
  let gamma : ℝ := a / (1 - b)
  let cH : ℝ := vH * AH ^ (1 / (1 - b))
  let cL : ℝ := vL * AL ^ (1 / (1 - b))
  let ZA : ℝ := vH * AH ^ (1 / d) + vL * AL ^ (1 / d)
  let K : ℝ := vH * kH t + vL * kL t
  let G : ℝ := cH * (kH t) ^ gamma + cL * (kL t) ^ gamma
  let kappaH : ℝ := vH * kH t / K
  let omegaH : ℝ := cH * (kH t) ^ gamma / G
  let gH : ℝ := AH ^ (1 / (1 - b)) * (kH t) ^ gamma
  let gL : ℝ := AL ^ (1 / (1 - b)) * (kL t) ^ gamma
  let Gout : ℝ := vH * gH + vL * gL
  let ellH : ℝ := L * gH / Gout
  let ellL : ℝ := L * gL / Gout
  let YH : ℝ := AH * (kH t) ^ a * ellH ^ b
  let YL : ℝ := AL * (kL t) ^ a * ellL ^ b
  change
    HasDerivAt
      (fun s => a * Real.log (vH * kH s + vL * kL s) +
        d * Real.log ZA -
        (1 - b) * Real.log
          (cH * (kH s) ^ gamma + cL * (kL s) ^ gamma))
      (a * (kappaH - omegaH) *
        (dkH / kH t - dkL / kL t)) t ∧
    HasDerivAt
      (fun s => Real.log (kH s / kL s))
      (dkH / kH t - dkL / kL t) t ∧
    ProposedPaperAllocationLossElasticity.outputShareH vH vL YH YL = omegaH ∧
    (ProposedPaperAllocationLossElasticity.outputShareH vH vL YH YL >
        ProposedPaperAllocationLossElasticity.capitalShareH vH vL (kH t) (kL t) ↔
      a * (YH / kH t) > a * (YL / kL t))
  have hb1 : b < 1 := by linarith [hsum, ha, hd]
  have hMain :
      HasDerivAt
        (fun s => a * Real.log (vH * kH s + vL * kL s) +
          d * Real.log ZA -
          (1 - b) * Real.log
            (cH * (kH s) ^ gamma + cL * (kL s) ^ gamma))
        (a * (kappaH - omegaH) *
          (dkH / kH t - dkL / kL t)) t :=
    ProposedPaperSourceLossChainRule.original_source_loss_hasDerivAt_relative_capital
      vH vL AH AL a b d kH kL t dkH dkL
      hvH hvL hAH hAL hkH hkL hb1 hH hLL
  have hRatio :
      HasDerivAt (fun s => Real.log (kH s / kL s))
        (dkH / kH t - dkL / kL t) t :=
    ProposedPaperSourceLogCapitalRatio.original_log_capital_ratio_hasDerivAt
      kH kL t dkH dkL hkH hkL hH hLL
  have hgH : 0 < gH := by
    dsimp [gH]
    positivity
  have hgL : 0 < gL := by
    dsimp [gL]
    positivity
  have hGout : 0 < Gout := by
    dsimp [Gout]
    exact add_pos (mul_pos hvH hgH) (mul_pos hvL hgL)
  have hGsame : G = Gout := by
    dsimp [G, Gout, cH, cL, gH, gL]
    ring
  have hShare0 :
      ProposedPaperAllocationLossElasticity.outputShareH vH vL YH YL =
        vH * gH / Gout :=
    ProposedPaperSourceOutputShare.original_output_share_equals_adjusted_weight
      vH vL AH AL (kH t) (kL t) L a b
      hvH hvL hAH hAL hkH hkL hL hb1
  have hShare :
      ProposedPaperAllocationLossElasticity.outputShareH vH vL YH YL =
        omegaH := by
    calc
      ProposedPaperAllocationLossElasticity.outputShareH vH vL YH YL =
        vH * gH / Gout := hShare0
      _ = omegaH := by
        rw [← hGsame]
        dsimp [omegaH, cH, gH]
        ring
  have hellH : 0 < ellH := by
    dsimp [ellH]
    exact div_pos (mul_pos hL hgH) hGout
  have hellL : 0 < ellL := by
    dsimp [ellL]
    exact div_pos (mul_pos hL hgL) hGout
  have hyH : 0 < YH := by
    dsimp [YH]
    positivity
  have hyL : 0 < YL := by
    dsimp [YL]
    positivity
  have hMPK :
      ProposedPaperAllocationLossElasticity.outputShareH vH vL YH YL >
          ProposedPaperAllocationLossElasticity.capitalShareH
            vH vL (kH t) (kL t) ↔
        a * (YH / kH t) > a * (YL / kL t) := by
    have hIff :=
      ProposedPaperAllocationLossElasticity.output_share_gt_capital_share_iff_productivity
        vH vL (kH t) (kL t) YH YL hvH hvL hkH hkL hyH hyL
    constructor
    · intro h
      exact mul_lt_mul_of_pos_left (hIff.mp h) ha
    · intro h
      exact hIff.mpr ((mul_lt_mul_iff_of_pos_left ha).mp h)
  exact ⟨hMain, hRatio, hShare, hMPK⟩

#print axioms original_source_dynamic_lemma43_bundle

end ProposedPaperLemma43DynamicIntegrated
end Ventura26LiquidityAllocation
