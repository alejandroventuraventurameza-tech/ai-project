import Ventura26LiquidityAllocation.PaperJointEfficiencyPhysicalCandidate
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Lemma 4.3: logarithmic loss from physical firm technologies

Unlike the older allocationLossIdentitySpec, the numerator of the
output gap here is proven as an efficient upper bound on the ORIGINAL
individual Cobb-Douglas technologies, not simply postulated as a
definition. For positive individual positions, original output is
strictly positive, making log monotonicity available.

The second result substitutes the source-proven optimal labor rule
and derives exactly the paper's log loss expression. No derivative
of K or G is claimed here, nor any monetary-policy response.
-/

namespace Ventura26LiquidityAllocation
namespace ProposedPaperOriginalLogLoss

/-- Global production loss is nonnegative for strictly positive
original physical inputs, with positive masses/productivities, common
nonnegative factor elasticities and decreasing returns to scale.
The original aggregate source production is used on the left. -/
theorem original_physical_log_loss_nonnegative
    (vH vL AH AL kH kL ellH ellL a b d : ℝ)
    (hvH : 0 < vH) (hvL : 0 < vL)
    (hAH : 0 < AH) (hAL : 0 < AL)
    (hkH : 0 < kH) (hkL : 0 < kL)
    (hellH : 0 < ellH) (hellL : 0 < ellL)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hd : 0 < d)
    (hsum : a + b + d = 1) :
    0 ≤
      Real.log
        ((vH * kH + vL * kL) ^ a *
          (vH * ellH + vL * ellL) ^ b *
          (vH * AH ^ (1 / d) + vL * AL ^ (1 / d)) ^ d) -
      Real.log
        (vH * (AH * kH ^ a * ellH ^ b) +
          vL * (AL * kL ^ a * ellL ^ b)) := by
  have hK : 0 < vH * kH + vL * kL := by positivity
  have hL : 0 < vH * ellH + vL * ellL := by positivity
  have hY : 0 <
      vH * (AH * kH ^ a * ellH ^ b) +
        vL * (AL * kL ^ a * ellL ^ b) := by positivity
  have hbound :=
    ProposedPaperJointEfficiencyPhysical.original_physical_two_type_joint_output_bound
      vH vL AH AL kH kL ellH ellL a b d
      hvH hvL hAH hAL hkH.le hkL.le hellH.le hellL.le
      hK hL ha hb hd hsum
  exact sub_nonneg.mpr (Real.log_le_log hY hbound)

/-- At the source-derived optimal labor allocation, the physical
output ratio yields EXACTLY a log K + d log ZA - (1-b) log G,
with firm-specific capital stocks strictly positive. This is an
identity of source-constructed outputs, not their derivative. -/
theorem original_labor_candidate_log_loss_formula
    (vH vL AH AL kH kL L a b d : ℝ)
    (hvH : 0 < vH) (hvL : 0 < vL)
    (hAH : 0 < AH) (hAL : 0 < AL)
    (hkH : 0 < kH) (hkL : 0 < kL)
    (hL : 0 < L) (hb : b < 1) :
    let K := vH * kH + vL * kL
    let Z := vH * AH ^ (1 / d) + vL * AL ^ (1 / d)
    let gH := AH ^ (1 / (1 - b)) * kH ^ (a / (1 - b))
    let gL := AL ^ (1 / (1 - b)) * kL ^ (a / (1 - b))
    let G := vH * gH + vL * gL
    Real.log (K ^ a * L ^ b * Z ^ d) -
      Real.log
        (vH * (AH * kH ^ a * (L * gH / G) ^ b) +
          vL * (AL * kL ^ a * (L * gL / G) ^ b)) =
      a * Real.log K + d * Real.log Z - (1 - b) * Real.log G := by
  let K : ℝ := vH * kH + vL * kL
  let Z : ℝ := vH * AH ^ (1 / d) + vL * AL ^ (1 / d)
  let gH : ℝ := AH ^ (1 / (1 - b)) * kH ^ (a / (1 - b))
  let gL : ℝ := AL ^ (1 / (1 - b)) * kL ^ (a / (1 - b))
  let G : ℝ := vH * gH + vL * gL
  change Real.log (K ^ a * L ^ b * Z ^ d) -
      Real.log
        (vH * (AH * kH ^ a * (L * gH / G) ^ b) +
          vL * (AL * kL ^ a * (L * gL / G) ^ b)) =
      a * Real.log K + d * Real.log Z - (1 - b) * Real.log G
  have hK : 0 < K := by dsimp [K]; positivity
  have hZ : 0 < Z := by dsimp [Z]; positivity
  have hgH : 0 < gH := by dsimp [gH]; positivity
  have hgL : 0 < gL := by dsimp [gL]; positivity
  have hG : 0 < G := by
    dsimp [G]
    exact add_pos (mul_pos hvH hgH) (mul_pos hvL hgL)
  have hY :
      vH * (AH * kH ^ a * (L * gH / G) ^ b) +
        vL * (AL * kL ^ a * (L * gL / G) ^ b) =
      L ^ b * G ^ (1 - b) :=
    ProposedPaperAllocationSourceAlgebraBridge.source_two_type_output_at_optimal_labor
      vH vL AH AL kH kL L a b
      hvH hvL hAH hAL hkH hkL hL hb
  calc
    Real.log (K ^ a * L ^ b * Z ^ d) -
        Real.log
          (vH * (AH * kH ^ a * (L * gH / G) ^ b) +
            vL * (AL * kL ^ a * (L * gL / G) ^ b)) =
      Real.log (K ^ a * L ^ b * Z ^ d) -
        Real.log (L ^ b * G ^ (1 - b)) := by rw [hY]
    _ = a * Real.log K + d * Real.log Z -
        (1 - b) * Real.log G :=
      ProposedPaperAllocationSourceAlgebraBridge.positive_aggregate_loss_log_formula
        K L Z G a b d hK hL hZ hG

#print axioms original_physical_log_loss_nonnegative
#print axioms original_labor_candidate_log_loss_formula

end ProposedPaperOriginalLogLoss
end Ventura26LiquidityAllocation
