import Ventura26LiquidityAllocation.PaperLemma43SourceCompleteCandidate
import Ventura26LiquidityAllocation.CurrentCompactLogLossBridge

/-!
# Current paper, Lemma A.1.4: integrated static and differential bundle

Scientific source locked to ai-project@bac3c6255da39cd1169a965df35bb5e9a230e6e8,
paper/appendix_eight_results.tex (lem:allocation_loss_identity).

The historical eleven-clause theorem supplies the physical production
functions, optimal labor, the feasible global efficient benchmark, its
attainment, nonnegative log difference, and the differential/MPK
identities.  The current paper defines loss using the LOG OF THE RATIO;
the independent currentCompactLogLoss_exact bridge converts these two
positive quantities using the physical efficiency bound derived here.

This integrated declaration does NOT claim an equilibrium allocation,
a policy shock mechanism, or the total derivative of log(Yeff/Y) as a
standalone function on an arbitrary global path: the historical result
gives HasDerivAt for the *expanded* loss expression under local
differentiability. A separate pathwise identification is required before
calling the whole source statement literally equivalent.
-/

namespace Ventura26LiquidityAllocation
namespace CurrentCompact

/-- The eleven source-faithful statements and the compact paper's
log-ratio definition, proven for the SAME physical firms and output.
Unlike a mere syntactic bridge, the positivity and efficient output bound
are derived from the primitive technology and the historical theorem. -/
def compactLemmaA14IntegratedSpec
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
  ProposedPaperLemma43SourceComplete.sourceLemma43CompleteSpec
    vH vL AH AL L a b d kH kL t dkH dkL ∧
    Real.log (Yeff / Y) = Real.log Yeff - Real.log Y ∧
    0 ≤ Real.log (Yeff / Y)

/-- An integrated *conditional* Lean proof of all eleven historical
clauses plus the compact paper's log-ratio definition and its sign.
No efficiency hypothesis is assumed: the bound follows from the
checked global efficiency clause in the historical package. -/
theorem compactLemmaA14Integrated_exact
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
    compactLemmaA14IntegratedSpec
      vH vL AH AL L a b d kH kL t dkH dkL := by
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
  have hOriginal :=
    ProposedPaperLemma43SourceComplete.sourceLemma43CompleteSpec_proved
      vH vL AH AL L a b d kH kL t dkH dkL
      hvH hvL hAH hAL hL ha hb hd hsum hkH hkL hH hLL
  have hOriginalSplit := hOriginal
  dsimp only [ProposedPaperLemma43SourceComplete.sourceLemma43CompleteSpec]
    at hOriginalSplit
  rcases hOriginalSplit with
    ⟨hLabor, _hProd, hGlobal, _hAttain, _hLossNonneg,
      _hLossEq, _hLaborOpt, _hDeriv, _hRatio, _hShare, _hMPK⟩
  have hxH : 0 < xH := hkH
  have hxL : 0 < xL := hkL
  have hEllH : 0 < ellH := hLabor.1
  have hEllL : 0 < ellL := hLabor.2.1
  have hYH : 0 < YH := by
    change 0 < AH * xH ^ a * ellH ^ b
    positivity
  have hYL : 0 < YL := by
    change 0 < AL * xL ^ a * ellL ^ b
    positivity
  have hY : 0 < Y := by
    change 0 < vH * YH + vL * YL
    exact add_pos (mul_pos hvH hYH) (mul_pos hvL hYL)
  have hK : vH * xH + vL * xL = K := rfl
  have hLaborBudget : vH * ellH + vL * ellL = L := hLabor.2.2
  have hEffBound : Y ≤ Yeff := by
    exact hGlobal xH xL ellH ellL
      (le_of_lt hxH) (le_of_lt hxL)
      (le_of_lt hEllH) (le_of_lt hEllL) hK hLaborBudget
  have hBridge :
      Real.log (Yeff / Y) = Real.log Yeff - Real.log Y ∧
      0 ≤ Real.log (Yeff / Y) :=
    currentCompactLogLoss_exact Y Yeff hY hEffBound
  dsimp only [compactLemmaA14IntegratedSpec]
  exact ⟨hOriginal, hBridge.1, hBridge.2⟩

#print axioms compactLemmaA14Integrated_exact

end CurrentCompact
end Ventura26LiquidityAllocation
