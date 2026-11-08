import Ventura26LiquidityAllocation.PaperSourceLogCapitalRatioCandidate

/-!
# Lemma 4.3 — one source-level static statement with seven substantive claims

This deliberately uses the ORIGINAL physical Cobb-Douglas technologies.
In particular, both Y and Yeff are tested against source output, not
merely given as definitions and then repeated as tautologies.

Positive firm masses/productivities/capital and 0<a,0<b,d=1-a-b>0
are explicit. Each alternative may place zero capital/labor in a firm,
but total resources are positive. No bank or monetary equilibrium
statement is implied.
-/

namespace Ventura26LiquidityAllocation
namespace ProposedPaperLemma43StaticIntegrated

/-- Integrated source-level STATIC component of Lemma 4.3.

The conjunction proves (1) feasible positive labor, (2) actual output
at optimal labor, (3) a global two-factor upper bound for ANY physical
nonnegative allocation satisfying both original budgets, (4) physical
attainment of that bound by the joint candidate, (5) nonnegative log
loss, (6) its exact paper formula, and (7) global labor optimum given
physical capital. All statements share one set of original quantities.
-/
theorem original_source_static_lemma43_bundle
    (vH vL AH AL kH kL L a b d : ℝ)
    (hvH : 0 < vH) (hvL : 0 < vL)
    (hAH : 0 < AH) (hAL : 0 < AL)
    (hkH : 0 < kH) (hkL : 0 < kL)
    (hL : 0 < L)
    (ha : 0 < a) (hb : 0 < b) (hd : 0 < d)
    (hsum : a + b + d = 1) :
    let gH := AH ^ (1 / (1 - b)) * kH ^ (a / (1 - b))
    let gL := AL ^ (1 / (1 - b)) * kL ^ (a / (1 - b))
    let G := vH * gH + vL * gL
    let K := vH * kH + vL * kL
    let ZA := vH * AH ^ (1 / d) + vL * AL ^ (1 / d)
    let zH := AH ^ (1 / d)
    let zL := AL ^ (1 / d)
    let ellH := L * gH / G
    let ellL := L * gL / G
    let YH := AH * kH ^ a * ellH ^ b
    let YL := AL * kL ^ a * ellL ^ b
    let Y := vH * YH + vL * YL
    let Yeff := K ^ a * L ^ b * ZA ^ d
    (0 < ellH ∧ 0 < ellL ∧ vH * ellH + vL * ellL = L) ∧
    Y = L ^ b * G ^ (1 - b) ∧
    (∀ kHa kLa ellHa ellLa : ℝ,
      0 ≤ kHa → 0 ≤ kLa → 0 ≤ ellHa → 0 ≤ ellLa →
      vH * kHa + vL * kLa = K →
      vH * ellHa + vL * ellLa = L →
      vH * (AH * kHa ^ a * ellHa ^ b) +
        vL * (AL * kLa ^ a * ellLa ^ b) ≤ Yeff) ∧
    (vH * (AH * (K * zH / ZA) ^ a * (L * zH / ZA) ^ b) +
        vL * (AL * (K * zL / ZA) ^ a * (L * zL / ZA) ^ b) = Yeff) ∧
    (0 ≤ Real.log Yeff - Real.log Y) ∧
    (Real.log Yeff - Real.log Y =
      a * Real.log K + d * Real.log ZA - (1 - b) * Real.log G) ∧
    (∀ ellHa ellLa : ℝ,
      0 ≤ ellHa → 0 ≤ ellLa →
      vH * ellHa + vL * ellLa = L →
      vH * (AH * kH ^ a * ellHa ^ b) +
        vL * (AL * kL ^ a * ellLa ^ b) ≤ Y) := by
  let gH : ℝ := AH ^ (1 / (1 - b)) * kH ^ (a / (1 - b))
  let gL : ℝ := AL ^ (1 / (1 - b)) * kL ^ (a / (1 - b))
  let G : ℝ := vH * gH + vL * gL
  let K : ℝ := vH * kH + vL * kL
  let ZA : ℝ := vH * AH ^ (1 / d) + vL * AL ^ (1 / d)
  let zH : ℝ := AH ^ (1 / d)
  let zL : ℝ := AL ^ (1 / d)
  let ellH : ℝ := L * gH / G
  let ellL : ℝ := L * gL / G
  let YH : ℝ := AH * kH ^ a * ellH ^ b
  let YL : ℝ := AL * kL ^ a * ellL ^ b
  let Y : ℝ := vH * YH + vL * YL
  let Yeff : ℝ := K ^ a * L ^ b * ZA ^ d
  change
    (0 < ellH ∧ 0 < ellL ∧ vH * ellH + vL * ellL = L) ∧
    Y = L ^ b * G ^ (1 - b) ∧
    (∀ kHa kLa ellHa ellLa : ℝ,
      0 ≤ kHa → 0 ≤ kLa → 0 ≤ ellHa → 0 ≤ ellLa →
      vH * kHa + vL * kLa = K →
      vH * ellHa + vL * ellLa = L →
      vH * (AH * kHa ^ a * ellHa ^ b) +
        vL * (AL * kLa ^ a * ellLa ^ b) ≤ Yeff) ∧
    (vH * (AH * (K * zH / ZA) ^ a * (L * zH / ZA) ^ b) +
        vL * (AL * (K * zL / ZA) ^ a * (L * zL / ZA) ^ b) = Yeff) ∧
    (0 ≤ Real.log Yeff - Real.log Y) ∧
    (Real.log Yeff - Real.log Y =
      a * Real.log K + d * Real.log ZA - (1 - b) * Real.log G) ∧
    (∀ ellHa ellLa : ℝ,
      0 ≤ ellHa → 0 ≤ ellLa →
      vH * ellHa + vL * ellLa = L →
      vH * (AH * kH ^ a * ellHa ^ b) +
        vL * (AL * kL ^ a * ellLa ^ b) ≤ Y)
  have hb1 : b < 1 := by linarith [hsum, ha, hd]
  have hgH : 0 < gH := by
    dsimp [gH]
    positivity
  have hgL : 0 < gL := by
    dsimp [gL]
    positivity
  have hG : 0 < G := by
    dsimp [G]
    exact add_pos (mul_pos hvH hgH) (mul_pos hvL hgL)
  have hK : 0 < K := by
    dsimp [K]
    positivity
  have hPosFeasible : 0 < ellH ∧ 0 < ellL ∧
      vH * ellH + vL * ellL = L :=
    ProposedPaperAllocationSourceAlgebraBridge.source_labor_candidate_clears_resources
      vH vL gH gL L hvH hvL hgH hgL hL
  have hY : Y = L ^ b * G ^ (1 - b) :=
    ProposedPaperAllocationSourceAlgebraBridge.source_two_type_output_at_optimal_labor
      vH vL AH AL kH kL L a b hvH hvL hAH hAL hkH hkL hL hb1
  have hAttains :
      vH * (AH * (K * zH / ZA) ^ a * (L * zH / ZA) ^ b) +
        vL * (AL * (K * zL / ZA) ^ a * (L * zL / ZA) ^ b) = Yeff :=
    ProposedPaperJointEfficiencyPhysical.original_physical_joint_candidate_attains_frontier
      vH vL AH AL K L a b d hvH hvL hAH hAL hK hL hd hsum
  have hLog : 0 ≤ Real.log Yeff - Real.log Y := by
    have raw := ProposedPaperOriginalLogLoss.original_physical_log_loss_nonnegative
      vH vL AH AL kH kL ellH ellL a b d
      hvH hvL hAH hAL hkH hkL hPosFeasible.1 hPosFeasible.2.1
      ha.le hb.le hd hsum
    simpa only [hPosFeasible.2.2] using raw
  have hLogIdentity :
      Real.log Yeff - Real.log Y =
        a * Real.log K + d * Real.log ZA - (1 - b) * Real.log G :=
    ProposedPaperOriginalLogLoss.original_labor_candidate_log_loss_formula
      vH vL AH AL kH kL L a b d
      hvH hvL hAH hAL hkH hkL hL hb1
  refine ⟨hPosFeasible, hY, ?_, hAttains, hLog, hLogIdentity, ?_⟩
  · intro kHa kLa ellHa ellLa hkHa hkLa hellHa hellLa hBudgetK hBudgetL
    have hAltK : 0 < vH * kHa + vL * kLa := by
      rw [hBudgetK]
      exact hK
    have hAltL : 0 < vH * ellHa + vL * ellLa := by
      rw [hBudgetL]
      exact hL
    have hBound :=
      ProposedPaperJointEfficiencyPhysical.original_physical_two_type_joint_output_bound
        vH vL AH AL kHa kLa ellHa ellLa a b d
        hvH hvL hAH hAL hkHa hkLa hellHa hellLa
        hAltK hAltL ha.le hb.le hd hsum
    simpa only [hBudgetK, hBudgetL] using hBound
  · intro ellHa ellLa hellHa hellLa hBudgetL
    have hLaborBound :=
      ProposedPaperOriginalLaborGlobal.original_two_type_labor_global_bound
        vH vL AH AL kH kL ellHa ellLa L a b
        hvH hvL hAH hAL hkH hkL hL hellHa hellLa
        hb hb1 hBudgetL
    calc
      vH * (AH * kH ^ a * ellHa ^ b) +
          vL * (AL * kL ^ a * ellLa ^ b) ≤
        L ^ b * G ^ (1 - b) := hLaborBound
      _ = Y := hY.symm

#print axioms original_source_static_lemma43_bundle

end ProposedPaperLemma43StaticIntegrated
end Ventura26LiquidityAllocation
