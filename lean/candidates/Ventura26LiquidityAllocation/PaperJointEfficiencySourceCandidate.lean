import Ventura26LiquidityAllocation.PaperOriginalLaborGlobalCandidate

/-!
# Lemma 4.3: joint capital/labor Cobb-Douglas source normalization

New source-level bridges for the EFFICIENT two-factor frontier:
  A_i = z_i^d, z_i = A_i^(1/d), d = 1-a-b > 0,
  k_i = (K*z_i/Z)*x_i, ell_i = (L*z_i/Z)*y_i.

The two identities below are kernel targets:
1. Original individual production equals the source-normalized term,
   also for nonnegative x_i,y_i at the boundary.
2. The common scale factor equals K^a L^b Z^d.

The AM-GM inequality is in PaperAllocationEfficiencySupportCandidate.
The next steps will remove the normalized-budget assumptions and
prove the original two-type source frontier and candidate attainment.
No financial equilibrium, welfare, or permanent growth claim is made.
-/

namespace Ventura26LiquidityAllocation
namespace ProposedPaperJointEfficiencySource

/-- A single positive-productivity, two-factor Cobb-Douglas firm
in normalized real coordinates, with possibly zero inputs x,y.
Exponents are common across firm types and sum with d to one. -/
theorem normalized_source_firm_output
    (K L Z z x y a b d : ℝ)
    (hK : 0 < K) (hL : 0 < L)
    (hZ : 0 < Z) (hz : 0 < z)
    (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hsum : a + b + d = 1) :
    z ^ d * (K * z / Z * x) ^ a * (L * z / Z * y) ^ b =
      ((K / Z) ^ a * (L / Z) ^ b) * z * (x ^ a * y ^ b) := by
  have hratioK : 0 ≤ K / Z := (div_pos hK hZ).le
  have hratioL : 0 ≤ L / Z := (div_pos hL hZ).le
  have hbaseK : 0 ≤ (K / Z) * z := mul_nonneg hratioK hz.le
  have hbaseL : 0 ≤ (L / Z) * z := mul_nonneg hratioL hz.le
  have hinputK : K * z / Z * x = ((K / Z) * z) * x := by ring
  have hinputL : L * z / Z * y = ((L / Z) * z) * y := by ring
  have hzpow : z ^ d * z ^ a * z ^ b = z := by
    rw [← Real.rpow_add hz d a, ← Real.rpow_add hz (d + a) b]
    have horder : d + a + b = 1 := by linarith [hsum]
    rw [horder]
    simp
  calc
    z ^ d * (K * z / Z * x) ^ a * (L * z / Z * y) ^ b =
        z ^ d * (((K / Z) * z) * x) ^ a *
          (((L / Z) * z) * y) ^ b := by
          rw [hinputK, hinputL]
    _ = z ^ d * (((K / Z) ^ a * z ^ a) * x ^ a) *
          (((L / Z) ^ b * z ^ b) * y ^ b) := by
          rw [Real.mul_rpow hbaseK hx, Real.mul_rpow hbaseL hy,
              Real.mul_rpow hratioK hz.le, Real.mul_rpow hratioL hz.le]
    _ = ((K / Z) ^ a * (L / Z) ^ b) *
          (z ^ d * z ^ a * z ^ b) * (x ^ a * y ^ b) := by ring
    _ = ((K / Z) ^ a * (L / Z) ^ b) * z * (x ^ a * y ^ b) := by
          rw [hzpow]

/-- Convert the aggregate normalization back to the exact efficient
production frontier in the paper, with positive aggregate resources.
This is the scale identity only, not a bound on arbitrary allocations. -/
theorem normalized_joint_scale_identity
    (K L Z a b d : ℝ)
    (hK : 0 < K) (hL : 0 < L) (hZ : 0 < Z)
    (hsum : a + b + d = 1) :
    (K / Z) ^ a * (L / Z) ^ b * Z = K ^ a * L ^ b * Z ^ d := by
  have hZa : 0 < Z ^ a := Real.rpow_pos_of_pos hZ _
  have hZb : 0 < Z ^ b := Real.rpow_pos_of_pos hZ _
  have hZpow : Z ^ d * (Z ^ a * Z ^ b) = Z := by
    rw [← Real.rpow_add hZ a b, ← Real.rpow_add hZ d (a + b)]
    have horder : d + (a + b) = 1 := by linarith [hsum]
    rw [horder]
    simp
  have hquot : Z / (Z ^ a * Z ^ b) = Z ^ d := by
    apply (div_eq_iff (mul_ne_zero (ne_of_gt hZa) (ne_of_gt hZb))).2
    exact hZpow.symm
  calc
    (K / Z) ^ a * (L / Z) ^ b * Z =
        (K ^ a / Z ^ a) * (L ^ b / Z ^ b) * Z := by
          rw [Real.div_rpow hK.le hZ.le, Real.div_rpow hL.le hZ.le]
    _ = K ^ a * L ^ b * (Z / (Z ^ a * Z ^ b)) := by
          field_simp [ne_of_gt hZa, ne_of_gt hZb] <;> ring
    _ = K ^ a * L ^ b * Z ^ d := by rw [hquot]

#print axioms normalized_source_firm_output
#print axioms normalized_joint_scale_identity

end ProposedPaperJointEfficiencySource
end Ventura26LiquidityAllocation
