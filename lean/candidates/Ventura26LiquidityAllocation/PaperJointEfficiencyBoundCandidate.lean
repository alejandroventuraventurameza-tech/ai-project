import Ventura26LiquidityAllocation.PaperJointEfficiencySourceCandidate

/-!
# Lemma 4.3: normalized joint K/L efficiency after source-level power bridge

The source micro-production identity is imported rather than assumed as
a definition. Combined with global three-factor AM-GM this provides a
GLOBAL aggregate output inequality under normalized budgets. A second
lemma prepares the exact translation of arbitrary original K/L budgets.
The end-to-end original arbitrary-allocation claim is a separate target.
-/

namespace Ventura26LiquidityAllocation
namespace ProposedPaperJointEfficiencyBound

theorem normalized_two_type_source_output_le_efficient
    (vH vL zH zL K L Z a b d xH xL yH yL : ℝ)
    (hvH : 0 < vH) (hvL : 0 < vL)
    (hzH : 0 < zH) (hzL : 0 < zL)
    (hK : 0 < K) (hL : 0 < L) (hZ : 0 < Z)
    (hxH : 0 ≤ xH) (hxL : 0 ≤ xL)
    (hyH : 0 ≤ yH) (hyL : 0 ≤ yL)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hd : 0 ≤ d)
    (hsum : a + b + d = 1)
    (hZdef : vH * zH + vL * zL = Z)
    (hcapital : vH * zH * xH + vL * zL * xL = Z)
    (hlabor : vH * zH * yH + vL * zL * yL = Z) :
    vH * (zH ^ d * (K * zH / Z * xH) ^ a *
        (L * zH / Z * yH) ^ b) +
      vL * (zL ^ d * (K * zL / Z * xL) ^ a *
        (L * zL / Z * yL) ^ b) ≤
      K ^ a * L ^ b * Z ^ d := by
  have hc :
      (vH * zH) * xH + (vL * zL) * xL =
        vH * zH + vL * zL := by
    calc
      (vH * zH) * xH + (vL * zL) * xL =
          vH * zH * xH + vL * zL * xL := by ring
      _ = Z := hcapital
      _ = vH * zH + vL * zL := hZdef.symm
  have hl :
      (vH * zH) * yH + (vL * zL) * yL =
        vH * zH + vL * zL := by
    calc
      (vH * zH) * yH + (vL * zL) * yL =
          vH * zH * yH + vL * zL * yL := by ring
      _ = Z := hlabor
      _ = vH * zH + vL * zL := hZdef.symm
  have hamgm :=
    ProposedPaperAllocationEfficiencySupport.normalized_two_type_output_le_benchmark
      a b d (vH * zH) (vL * zL) xH xL yH yL
      ha hb hd hsum (mul_pos hvH hzH).le (mul_pos hvL hzL).le
      hxH hxL hyH hyL hc hl
  have hscale : 0 ≤ (K / Z) ^ a * (L / Z) ^ b :=
    mul_nonneg (Real.rpow_nonneg (div_pos hK hZ).le a)
      (Real.rpow_nonneg (div_pos hL hZ).le b)
  calc
    vH * (zH ^ d * (K * zH / Z * xH) ^ a *
        (L * zH / Z * yH) ^ b) +
      vL * (zL ^ d * (K * zL / Z * xL) ^ a *
        (L * zL / Z * yL) ^ b) =
      ((K / Z) ^ a * (L / Z) ^ b) *
        ((vH * zH) * (xH ^ a * yH ^ b) +
          (vL * zL) * (xL ^ a * yL ^ b)) := by
            rw [
              ProposedPaperJointEfficiencySource.normalized_source_firm_output
                K L Z zH xH yH a b d hK hL hZ hzH hxH hyH hsum,
              ProposedPaperJointEfficiencySource.normalized_source_firm_output
                K L Z zL xL yL a b d hK hL hZ hzL hxL hyL hsum]
            ring
    _ ≤ ((K / Z) ^ a * (L / Z) ^ b) *
        (vH * zH + vL * zL) :=
          mul_le_mul_of_nonneg_left hamgm hscale
    _ = ((K / Z) ^ a * (L / Z) ^ b) * Z := by rw [hZdef]
    _ = K ^ a * L ^ b * Z ^ d :=
      ProposedPaperJointEfficiencySource.normalized_joint_scale_identity
        K L Z a b d hK hL hZ hsum

/-- Original mass-weighted resource budget implies its normalized
weighted budget. This removes the normalized-budget assumption
from the subsequent original physical efficiency theorem. -/
theorem source_resource_budget_normalizes
    (vH vL zH zL qH qL Q Z : ℝ)
    (hzH : 0 < zH) (hzL : 0 < zL)
    (hQ : 0 < Q)
    (hresource : vH * qH + vL * qL = Q)
    (hZdef : vH * zH + vL * zL = Z) :
    vH * zH * (qH * Z / (Q * zH)) +
      vL * zL * (qL * Z / (Q * zL)) = Z := by
  have hweightH :
      vH * zH * (qH * Z / (Q * zH)) = (Z / Q) * (vH * qH) := by
    field_simp [ne_of_gt hQ, ne_of_gt hzH] <;> ring
  have hweightL :
      vL * zL * (qL * Z / (Q * zL)) = (Z / Q) * (vL * qL) := by
    field_simp [ne_of_gt hQ, ne_of_gt hzL] <;> ring
  calc
    vH * zH * (qH * Z / (Q * zH)) +
        vL * zL * (qL * Z / (Q * zL)) =
      (Z / Q) * (vH * qH + vL * qL) := by
        rw [hweightH, hweightL]
        ring
    _ = (Z / Q) * Q := by rw [hresource]
    _ = Z := by field_simp [ne_of_gt hQ] <;> ring

#print axioms normalized_two_type_source_output_le_efficient
#print axioms source_resource_budget_normalizes

end ProposedPaperJointEfficiencyBound
end Ventura26LiquidityAllocation
