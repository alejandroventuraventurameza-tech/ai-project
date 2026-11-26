import Ventura26LiquidityAllocation.PaperLemma43StaticIntegratedCandidate
import Ventura26LiquidityAllocation.PaperLemma43DynamicIntegratedCandidate

/-!
# Lemma 4.3 — source-faithful ONE-PREDICATE integration

The original checkpoint's allocationLossIdentitySpec is not the literal
paper lemma: it assumes aggregate Y/Yeff by definition and omits the
physical source, global optimality, loss derivative, and MPK ordering.

The replacement below DOES NOT alter that older spec. It states eleven
substantive linked claims about the SAME two firms, capital endowments,
labor at date t, technology elasticities and derivative direction. Every
claim is proved by the two checked integrated modules; no axiom is
introduced.

This theorem says nothing about monetary paths actually solving the
dynamic equilibrium or which policy shock selects a branch.
-/

namespace Ventura26LiquidityAllocation
namespace ProposedPaperLemma43SourceComplete

/-- Repaired source-faithful specification for Lemma 4.3, intentionally
stronger than the old checkpoint statement. Parameters are shared
through all static and differential conclusions. -/
def sourceLemma43CompleteSpec
    (vH vL AH AL L a b d : ℝ)
    (kH kL : ℝ → ℝ) (t dkH dkL : ℝ) : Prop :=
  let xH := kH t
  let xL := kL t
  let gamma := a / (1 - b)
  let gH := AH ^ (1 / (1 - b)) * xH ^ gamma
  let gL := AL ^ (1 / (1 - b)) * xL ^ gamma
  let G := vH * gH + vL * gL
  let K := vH * xH + vL * xL
  let zH := AH ^ (1 / d)
  let zL := AL ^ (1 / d)
  let ZA := vH * zH + vL * zL
  let ellH := L * gH / G
  let ellL := L * gL / G
  let YH := AH * xH ^ a * ellH ^ b
  let YL := AL * xL ^ a * ellL ^ b
  let Y := vH * YH + vL * YL
  let Yeff := K ^ a * L ^ b * ZA ^ d
  let cH := vH * AH ^ (1 / (1 - b))
  let cL := vL * AL ^ (1 / (1 - b))
  let Gpath := cH * xH ^ gamma + cL * xL ^ gamma
  let kappaH := vH * xH / K
  let omegaH := cH * xH ^ gamma / Gpath
  -- 1. Positive feasible optimal labor.
  (0 < ellH ∧ 0 < ellL ∧ vH * ellH + vL * ellL = L) ∧
  -- 2. Original production at that labor is the aggregate formula.
  Y = L ^ b * G ^ (1 - b) ∧
  -- 3. No other feasible allocation of both original factors exceeds Yeff.
  (∀ kHa kLa ellHa ellLa : ℝ,
    0 ≤ kHa → 0 ≤ kLa → 0 ≤ ellHa → 0 ≤ ellLa →
    vH * kHa + vL * kLa = K →
    vH * ellHa + vL * ellLa = L →
    vH * (AH * kHa ^ a * ellHa ^ b) +
      vL * (AL * kLa ^ a * ellLa ^ b) ≤ Yeff) ∧
  -- 4. A feasible original physical candidate ATTAINS the frontier.
  (vH * (AH * (K * zH / ZA) ^ a * (L * zH / ZA) ^ b) +
    vL * (AL * (K * zL / ZA) ^ a * (L * zL / ZA) ^ b) = Yeff) ∧
  -- 5. The physical production loss is nonnegative.
  0 ≤ Real.log Yeff - Real.log Y ∧
  -- 6. Exact logarithmic identity rather than a definition of source Y.
  (Real.log Yeff - Real.log Y =
    a * Real.log K + d * Real.log ZA - (1 - b) * Real.log G) ∧
  -- 7. The proposed labor allocation dominates ALL labor alternatives.
  (∀ ellHa ellLa : ℝ,
    0 ≤ ellHa → 0 ≤ ellLa →
    vH * ellHa + vL * ellLa = L →
    vH * (AH * xH ^ a * ellHa ^ b) +
      vL * (AL * xL ^ a * ellLa ^ b) ≤ Y) ∧
  -- 8. FULL chain-rule derivative for actual source capital paths.
  HasDerivAt
    (fun s => a * Real.log (vH * kH s + vL * kL s) +
      d * Real.log ZA -
      (1 - b) * Real.log
        (cH * (kH s) ^ gamma + cL * (kL s) ^ gamma))
    (a * (kappaH - omegaH) * (dkH / xH - dkL / xL)) t ∧
  -- 9. The capital-ratio direction itself is a derivative.
  HasDerivAt (fun s => Real.log (kH s / kL s))
    (dkH / xH - dkL / xL) t ∧
  -- 10. The weight omega is PHYSICAL output share at labor optimum.
  ProposedPaperAllocationLossElasticity.outputShareH vH vL YH YL = omegaH ∧
  -- 11. Output-share > capital-share iff H's physical MPK is higher.
  (ProposedPaperAllocationLossElasticity.outputShareH vH vL YH YL >
      ProposedPaperAllocationLossElasticity.capitalShareH vH vL xH xL ↔
    a * (YH / xH) > a * (YL / xL))

/-- An integrated proof of the original source's eleven static and
pathwise allocative-loss assertions with no unproven sorry and no
assumed output formula. This proof DOES NOT imply dynamic equilibrium. -/
theorem sourceLemma43CompleteSpec_proved
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
    sourceLemma43CompleteSpec vH vL AH AL L a b d kH kL t dkH dkL := by
  have hStatic :=
    ProposedPaperLemma43StaticIntegrated.original_source_static_lemma43_bundle
      vH vL AH AL (kH t) (kL t) L a b d
      hvH hvL hAH hAL hkH hkL hL ha hb hd hsum
  have hDynamic :=
    ProposedPaperLemma43DynamicIntegrated.original_source_dynamic_lemma43_bundle
      vH vL AH AL L a b d kH kL t dkH dkL
      hvH hvL hAH hAL hL ha hb hd hsum hkH hkL hH hLL
  rcases hStatic with
    ⟨hLabor, hProd, hGlobal, hAttain, hLossNN, hLossEq, hLaborOptimal⟩
  rcases hDynamic with
    ⟨hDeriv, hRatio, hOutputShare, hMPK⟩
  dsimp only [sourceLemma43CompleteSpec]
  exact ⟨hLabor, hProd, hGlobal, hAttain, hLossNN, hLossEq,
    hLaborOptimal, hDeriv, hRatio, hOutputShare, hMPK⟩

#print axioms sourceLemma43CompleteSpec_proved

end ProposedPaperLemma43SourceComplete
end Ventura26LiquidityAllocation
