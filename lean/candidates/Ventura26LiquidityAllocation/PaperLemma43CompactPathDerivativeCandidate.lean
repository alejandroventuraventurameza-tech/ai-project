import Ventura26LiquidityAllocation.PaperLemma43CompactIntegratedCandidate
import Ventura26LiquidityAllocation.PaperAllocationSourceAlgebraBridgeCandidate

/-!
# Compact Appendix Lemma A.1.4: derivative of the literal output LOSS RATIO

Source: ai-project@bac3c6255da39cd1169a965df35bb5e9a230e6e8
  paper/appendix_eight_results.tex, lem:allocation_loss_identity.

The previous lemma proves the derivative of the *expanded* expression
  a*log K + d*log ZA - (1-b)*log G.
The new theorem proves directly that the *actual ratio function*
  s ↦ log ((K(s)^a L^b ZA^d)/(L^b G(s)^(1-b)))
has the SAME derivative at t. In particular, equality at t alone
would not imply a derivative: differentiability and strict positivity of
the capital paths provide an EVENTUAL equality near t.

This theorem does not impose global path positivity, dynamic equilibrium,
or the policy shock mechanism. It retains positive masses, productivity,
total labor, and elasticities a,b,d with a+b+d=1.
-/

namespace Ventura26LiquidityAllocation
namespace CurrentCompact

open Filter

/-- The *function* of output loss as the paper's log of the ratio,
using employment optimally allocated at each nearby capital level.
The mathematical derivative is local at t; no optimization of dynamic
capital paths or equilibrium market clearing is asserted. -/
theorem compactLossRatioAggregate_hasDerivAt
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
    HasDerivAt
      (fun s =>
        Real.log
          (((vH * kH s + vL * kL s) ^ a * L ^ b * ZA ^ d) /
            (L ^ b *
              (cH * (kH s) ^ gamma + cL * (kL s) ^ gamma) ^ (1 - b))))
      (a * (kappaH - omegaH) * (dkH / kH t - dkL / kL t)) t := by
  let gamma : ℝ := a / (1 - b)
  let cH : ℝ := vH * AH ^ (1 / (1 - b))
  let cL : ℝ := vL * AL ^ (1 / (1 - b))
  let ZA : ℝ := vH * AH ^ (1 / d) + vL * AL ^ (1 / d)
  let K : ℝ := vH * kH t + vL * kL t
  let G : ℝ := cH * (kH t) ^ gamma + cL * (kL t) ^ gamma
  let kappaH : ℝ := vH * kH t / K
  let omegaH : ℝ := cH * (kH t) ^ gamma / G
  change HasDerivAt
    (fun s =>
      Real.log
        (((vH * kH s + vL * kL s) ^ a * L ^ b * ZA ^ d) /
          (L ^ b *
            (cH * (kH s) ^ gamma + cL * (kL s) ^ gamma) ^ (1 - b))))
    (a * (kappaH - omegaH) * (dkH / kH t - dkL / kL t)) t
  have hb1 : b < 1 := by linarith [hsum, ha, hd]
  have hExpanded :
      HasDerivAt
        (fun s => a * Real.log (vH * kH s + vL * kL s) +
          d * Real.log ZA -
          (1 - b) * Real.log
            (cH * (kH s) ^ gamma + cL * (kL s) ^ gamma))
        (a * (kappaH - omegaH) * (dkH / kH t - dkL / kL t)) t :=
    ProposedPaperSourceLossChainRule.original_source_loss_hasDerivAt_relative_capital
      vH vL AH AL a b d kH kL t dkH dkL
      hvH hvL hAH hAL hkH hkL hb1 hH hLL

  -- Strict positivity at t propagates to a genuine neighborhood,
  -- so the logarithmic identity is an equality of local FUNCTIONS.
  have hPositiveH : ∀ᶠ s in 𝓝 t, 0 < kH s :=
    ContinuousAt.eventually_lt continuousAt_const hH.continuousAt hkH
  have hPositiveL : ∀ᶠ s in 𝓝 t, 0 < kL s :=
    ContinuousAt.eventually_lt continuousAt_const hLL.continuousAt hkL
  have hZA : 0 < ZA := by
    dsimp [ZA]
    positivity
  have hEventual :
      (fun s : ℝ =>
        Real.log
          (((vH * kH s + vL * kL s) ^ a * L ^ b * ZA ^ d) /
            (L ^ b *
              (cH * (kH s) ^ gamma + cL * (kL s) ^ gamma) ^ (1 - b)))) =ᶠ[𝓝 t]
        (fun s : ℝ =>
          a * Real.log (vH * kH s + vL * kL s) +
            d * Real.log ZA -
            (1 - b) * Real.log
              (cH * (kH s) ^ gamma + cL * (kL s) ^ gamma)) := by
    filter_upwards [hPositiveH, hPositiveL] with s hHs hLs
    have hKs : 0 < vH * kH s + vL * kL s :=
      add_pos (mul_pos hvH hHs) (mul_pos hvL hLs)
    have hGs : 0 < cH * (kH s) ^ gamma +
        cL * (kL s) ^ gamma := by
      dsimp [cH, cL]
      positivity
    have hOutput : 0 < L ^ b *
        (cH * (kH s) ^ gamma + cL * (kL s) ^ gamma) ^ (1 - b) := by
      positivity
    have hEff : 0 < (vH * kH s + vL * kL s) ^ a * L ^ b * ZA ^ d := by
      positivity
    calc
      Real.log
          (((vH * kH s + vL * kL s) ^ a * L ^ b * ZA ^ d) /
            (L ^ b *
              (cH * (kH s) ^ gamma + cL * (kL s) ^ gamma) ^ (1 - b))) =
          Real.log ((vH * kH s + vL * kL s) ^ a * L ^ b * ZA ^ d) -
            Real.log (L ^ b *
              (cH * (kH s) ^ gamma + cL * (kL s) ^ gamma) ^ (1 - b)) := by
        exact Real.log_div hEff.ne' hOutput.ne'
      _ = a * Real.log (vH * kH s + vL * kL s) +
            d * Real.log ZA -
            (1 - b) * Real.log
              (cH * (kH s) ^ gamma + cL * (kL s) ^ gamma) :=
        ProposedPaperAllocationSourceAlgebraBridge.positive_aggregate_loss_log_formula
          (vH * kH s + vL * kL s) L ZA
          (cH * (kH s) ^ gamma + cL * (kL s) ^ gamma)
          a b d hKs hL hZA hGs
  exact hExpanded.congr_of_eventuallyEq hEventual

#print axioms compactLossRatioAggregate_hasDerivAt

end CurrentCompact
end Ventura26LiquidityAllocation
