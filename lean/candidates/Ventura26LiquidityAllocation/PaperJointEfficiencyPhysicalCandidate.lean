import Ventura26LiquidityAllocation.PaperJointEfficiencyBoundCandidate

/-!
# Lemma 4.3: original two-type physical production and joint K/L efficiency

This file states the global production bound entirely in source quantities
(A_i,k_i,ell_i,v_i) and maps BOTH original resource constraints into the
normalized AM-GM proof. Zero capital or zero labor in any individual firm
is admitted, as long as both aggregate endowments are positive.

The reference candidate is also evaluated in source Cobb-Douglas production,
without postulating Yeff := K^a L^b ZA^d in the hypothesis.
The separate terminal/equilibrium and original loss derivative obligations
remain open.
-/

namespace Ventura26LiquidityAllocation
namespace ProposedPaperJointEfficiencyPhysical

/-- Conditional efficient output frontier for any feasible PHYSICAL allocation
of nonnegative capital and labor among two positive-mass firms.
The numerator is actual source Cobb-Douglas production, not an alias
for its normalized expression. All exponents are common across types.
The aggregate endowments must be positive even if some inputs are zero. -/
theorem original_physical_two_type_joint_output_bound
    (vH vL AH AL kH kL ellH ellL a b d : ℝ)
    (hvH : 0 < vH) (hvL : 0 < vL)
    (hAH : 0 < AH) (hAL : 0 < AL)
    (hkH : 0 ≤ kH) (hkL : 0 ≤ kL)
    (hellH : 0 ≤ ellH) (hellL : 0 ≤ ellL)
    (hK : 0 < vH * kH + vL * kL)
    (hL : 0 < vH * ellH + vL * ellL)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hd : 0 < d)
    (hsum : a + b + d = 1) :
    vH * (AH * kH ^ a * ellH ^ b) +
      vL * (AL * kL ^ a * ellL ^ b) ≤
      (vH * kH + vL * kL) ^ a *
      (vH * ellH + vL * ellL) ^ b *
      (vH * AH ^ (1 / d) + vL * AL ^ (1 / d)) ^ d := by
  let K : ℝ := vH * kH + vL * kL
  let L : ℝ := vH * ellH + vL * ellL
  let zH : ℝ := AH ^ (1 / d)
  let zL : ℝ := AL ^ (1 / d)
  let Z : ℝ := vH * zH + vL * zL
  let xH : ℝ := kH * Z / (K * zH)
  let xL : ℝ := kL * Z / (K * zL)
  let yH : ℝ := ellH * Z / (L * zH)
  let yL : ℝ := ellL * Z / (L * zL)
  change vH * (AH * kH ^ a * ellH ^ b) +
      vL * (AL * kL ^ a * ellL ^ b) ≤ K ^ a * L ^ b * Z ^ d
  have hKpos : 0 < K := hK
  have hLpos : 0 < L := hL
  have hzH : 0 < zH := Real.rpow_pos_of_pos hAH _
  have hzL : 0 < zL := Real.rpow_pos_of_pos hAL _
  have hZpos : 0 < Z := by
    dsimp [Z]
    exact add_pos (mul_pos hvH hzH) (mul_pos hvL hzL)
  have hxH : 0 ≤ xH := by
    dsimp [xH]
    exact div_nonneg (mul_nonneg hkH hZpos.le)
      (mul_nonneg hKpos.le hzH.le)
  have hxL : 0 ≤ xL := by
    dsimp [xL]
    exact div_nonneg (mul_nonneg hkL hZpos.le)
      (mul_nonneg hKpos.le hzL.le)
  have hyH : 0 ≤ yH := by
    dsimp [yH]
    exact div_nonneg (mul_nonneg hellH hZpos.le)
      (mul_nonneg hLpos.le hzH.le)
  have hyL : 0 ≤ yL := by
    dsimp [yL]
    exact div_nonneg (mul_nonneg hellL hZpos.le)
      (mul_nonneg hLpos.le hzL.le)
  have hcapital :
      vH * zH * xH + vL * zL * xL = Z := by
    exact ProposedPaperJointEfficiencyBound.source_resource_budget_normalizes
      vH vL zH zL kH kL K Z hzH hzL hKpos rfl rfl
  have hlabor :
      vH * zH * yH + vL * zL * yL = Z := by
    exact ProposedPaperJointEfficiencyBound.source_resource_budget_normalizes
      vH vL zH zL ellH ellL L Z hzH hzL hLpos rfl rfl
  have hscaledKH : K * zH / Z * xH = kH := by
    dsimp [xH]
    field_simp [ne_of_gt hKpos, ne_of_gt hzH, ne_of_gt hZpos] <;> ring
  have hscaledKL : K * zL / Z * xL = kL := by
    dsimp [xL]
    field_simp [ne_of_gt hKpos, ne_of_gt hzL, ne_of_gt hZpos] <;> ring
  have hscaledLH : L * zH / Z * yH = ellH := by
    dsimp [yH]
    field_simp [ne_of_gt hLpos, ne_of_gt hzH, ne_of_gt hZpos] <;> ring
  have hscaledLL : L * zL / Z * yL = ellL := by
    dsimp [yL]
    field_simp [ne_of_gt hLpos, ne_of_gt hzL, ne_of_gt hZpos] <;> ring
  have hAHsource : zH ^ d = AH := by
    dsimp [zH]
    exact ProposedPaperAllocationSourceAlgebraBridge.productivity_weight_recovers_A
      AH d hAH hd
  have hALsource : zL ^ d = AL := by
    dsimp [zL]
    exact ProposedPaperAllocationSourceAlgebraBridge.productivity_weight_recovers_A
      AL d hAL hd
  have hbound :
      vH * (zH ^ d * (K * zH / Z * xH) ^ a *
          (L * zH / Z * yH) ^ b) +
        vL * (zL ^ d * (K * zL / Z * xL) ^ a *
          (L * zL / Z * yL) ^ b) ≤
        K ^ a * L ^ b * Z ^ d :=
    ProposedPaperJointEfficiencyBound.normalized_two_type_source_output_le_efficient
      vH vL zH zL K L Z a b d xH xL yH yL
      hvH hvL hzH hzL hKpos hLpos hZpos
      hxH hxL hyH hyL ha hb hd.le hsum rfl hcapital hlabor
  calc
    vH * (AH * kH ^ a * ellH ^ b) +
        vL * (AL * kL ^ a * ellL ^ b) =
      vH * (zH ^ d * (K * zH / Z * xH) ^ a *
          (L * zH / Z * yH) ^ b) +
        vL * (zL ^ d * (K * zL / Z * xL) ^ a *
          (L * zL / Z * yL) ^ b) := by
            simp only [hscaledKH, hscaledKL, hscaledLH, hscaledLL,
              hAHsource, hALsource]
    _ ≤ K ^ a * L ^ b * Z ^ d := hbound

/-- At K,L>0 the source candidate k_i=K z_i/Z, ell_i=L z_i/Z
achieves the production bound exactly (not only a first-order condition). -/
theorem original_physical_joint_candidate_attains_frontier
    (vH vL AH AL K L a b d : ℝ)
    (hvH : 0 < vH) (hvL : 0 < vL)
    (hAH : 0 < AH) (hAL : 0 < AL)
    (hK : 0 < K) (hL : 0 < L)
    (hd : 0 < d) (hsum : a + b + d = 1) :
    let zH := AH ^ (1 / d)
    let zL := AL ^ (1 / d)
    let Z := vH * zH + vL * zL
    vH * (AH * (K * zH / Z) ^ a * (L * zH / Z) ^ b) +
      vL * (AL * (K * zL / Z) ^ a * (L * zL / Z) ^ b) =
        K ^ a * L ^ b * Z ^ d := by
  let zH : ℝ := AH ^ (1 / d)
  let zL : ℝ := AL ^ (1 / d)
  let Z : ℝ := vH * zH + vL * zL
  change vH * (AH * (K * zH / Z) ^ a * (L * zH / Z) ^ b) +
      vL * (AL * (K * zL / Z) ^ a * (L * zL / Z) ^ b) =
      K ^ a * L ^ b * Z ^ d
  have hzH : 0 < zH := Real.rpow_pos_of_pos hAH _
  have hzL : 0 < zL := Real.rpow_pos_of_pos hAL _
  have hZ : 0 < Z := by
    dsimp [Z]
    exact add_pos (mul_pos hvH hzH) (mul_pos hvL hzL)
  have hArecH : zH ^ d = AH := by
    dsimp [zH]
    exact ProposedPaperAllocationSourceAlgebraBridge.productivity_weight_recovers_A
      AH d hAH hd
  have hArecL : zL ^ d = AL := by
    dsimp [zL]
    exact ProposedPaperAllocationSourceAlgebraBridge.productivity_weight_recovers_A
      AL d hAL hd
  have hfirmH :
      AH * (K * zH / Z) ^ a * (L * zH / Z) ^ b =
        ((K / Z) ^ a * (L / Z) ^ b) * zH := by
    have hnorm :=
      ProposedPaperJointEfficiencySource.normalized_source_firm_output
        K L Z zH 1 1 a b d hK hL hZ hzH
        (by norm_num) (by norm_num) hsum
    simpa [hArecH] using hnorm
  have hfirmL :
      AL * (K * zL / Z) ^ a * (L * zL / Z) ^ b =
        ((K / Z) ^ a * (L / Z) ^ b) * zL := by
    have hnorm :=
      ProposedPaperJointEfficiencySource.normalized_source_firm_output
        K L Z zL 1 1 a b d hK hL hZ hzL
        (by norm_num) (by norm_num) hsum
    simpa [hArecL] using hnorm
  calc
    vH * (AH * (K * zH / Z) ^ a * (L * zH / Z) ^ b) +
        vL * (AL * (K * zL / Z) ^ a * (L * zL / Z) ^ b) =
      ((K / Z) ^ a * (L / Z) ^ b) * (vH * zH + vL * zL) := by
        rw [hfirmH, hfirmL]
        ring
    _ = (K / Z) ^ a * (L / Z) ^ b * Z := by
        dsimp [Z] <;> ring
    _ = K ^ a * L ^ b * Z ^ d :=
      ProposedPaperJointEfficiencySource.normalized_joint_scale_identity
        K L Z a b d hK hL hZ hsum

#print axioms original_physical_two_type_joint_output_bound
#print axioms original_physical_joint_candidate_attains_frontier

end ProposedPaperJointEfficiencyPhysical
end Ventura26LiquidityAllocation
