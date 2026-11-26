import Ventura26LiquidityAllocation.PaperLemma43CompactPhysicalPathCandidate

/-!
# Current paper Appendix A.1.4: ONE integrated mathematical specification

Locked source: ai-project@bac3c6255da39cd1169a965df35bb5e9a230e6e8
  paper/appendix_eight_results.tex, label lem:allocation_loss_identity.

This single endpoint combines the previously checked eleven historical
source-faithful claims, the current paper's positive log-of-output ratio,
and the newly checked pathwise derivative of the ratio constructed
DIRECTLY from the original Cobb-Douglas outputs of H and L with
source-optimal labor. All hypotheses are the lemma's standard positive
primitive domains and differentiability of the capital paths.

This is a mathematical paper-scoped candidate with explicit Spec;
it is NOT AppliedModelingLib's officially generated PaperInterface or
a proof that capital paths are DSGE equilibria.
-/

namespace Ventura26LiquidityAllocation
namespace CurrentCompact

/-- One transparent current-paper Spec for the physical, allocative
and local-differential statements of Appendix Lemma A.1.4. -/
def compactLemmaA14CurrentFullSpec
    (vH vL AH AL L a b d : ℝ)
    (kH kL : ℝ → ℝ) (t dkH dkL : ℝ) : Prop :=
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
  compactLemmaA14IntegratedSpec vH vL AH AL L a b d kH kL t dkH dkL ∧
    HasDerivAt
      (fun s : ℝ =>
        Real.log
          (((vH * kH s + vL * kL s) ^ a * L ^ b * ZA ^ d) /
            (vH * (AH * (kH s) ^ a *
                (L * gH s / (vH * gH s + vL * gL s)) ^ b) +
              vL * (AL * (kL s) ^ a *
                (L * gL s / (vH * gH s + vL * gL s)) ^ b))))
      (a * (kappaH - omegaH) * (dkH / kH t - dkL / kL t)) t

/-- Fully combined proof, with no hypothesis assuming output optimality,
the log identity, or the derivative conclusion. -/
theorem compactLemmaA14CurrentFull_exact
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
    compactLemmaA14CurrentFullSpec
      vH vL AH AL L a b d kH kL t dkH dkL := by
  have hIntegrated :=
    compactLemmaA14Integrated_exact
      vH vL AH AL L a b d kH kL t dkH dkL
      hvH hvL hAH hAL hL ha hb hd hsum hkH hkL hH hLL
  have hPhysical :=
    compactLossRatioPhysical_hasDerivAt
      vH vL AH AL L a b d kH kL t dkH dkL
      hvH hvL hAH hAL hL ha hb hd hsum hkH hkL hH hLL
  dsimp only [compactLemmaA14CurrentFullSpec]
  exact ⟨hIntegrated, hPhysical⟩

#print axioms compactLemmaA14CurrentFull_exact

end CurrentCompact
end Ventura26LiquidityAllocation
