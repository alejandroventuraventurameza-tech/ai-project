import Ventura26LiquidityAllocation.PaperAllocationEfficiencySupportCandidate
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Lemma 4.3: source real-power/logarithmic algebra bridge

These lemmas address two missing source-mapping obligations:
(1) recovering productivity A from z = A^(1/d), d > 0;
(2) converting the efficient/output ratio into the exact log-loss
formula used by the paper under positive aggregate quantities.

Neither statement by itself proves the micro-output formula,
the optimal labor reallocation, or the full pinned
allocationLossIdentitySpec. They deliberately expose positivity
assumptions rather than silently using log rules at zero.
-/

namespace Ventura26LiquidityAllocation
namespace ProposedPaperAllocationSourceAlgebraBridge

/-- If productivity A and 1-alpha-beta=d are positive, the adjusted
productivity weight z=A^(1/d) satisfies z^d=A. This is the first
real-power bridge from the normalized AM-GM theorem to Cobb-Douglas. -/
theorem productivity_weight_recovers_A
    (A d : ℝ) (hA : 0 < A) (hd : 0 < d) :
    (A ^ (1 / d)) ^ d = A := by
  have hdne : d ≠ 0 := ne_of_gt hd
  have hcancel : (1 / d) * d = 1 := by field_simp [hdne]
  calc
    (A ^ (1 / d)) ^ d = A ^ ((1 / d) * d) :=
      (Real.rpow_mul hA.le (1 / d) d).symm
    _ = A := by rw [hcancel]; simp

/-- Exact decomposition of the logarithmic output gap, corresponding
to equation (dynamic_loss_at_optimal_labor) in the paper. No claim
about production efficiency follows without the separate inequality
from the global AM-GM proof and the original production mapping. -/
theorem positive_aggregate_loss_log_formula
    (K L ZA G alpha beta d : ℝ)
    (hK : 0 < K) (hL : 0 < L)
    (hZA : 0 < ZA) (hG : 0 < G) :
    Real.log (K ^ alpha * L ^ beta * ZA ^ d) -
        Real.log (L ^ beta * G ^ (1 - beta)) =
      alpha * Real.log K + d * Real.log ZA -
        (1 - beta) * Real.log G := by
  have hKpow : K ^ alpha ≠ 0 :=
    ne_of_gt (Real.rpow_pos_of_pos hK alpha)
  have hLpow : L ^ beta ≠ 0 :=
    ne_of_gt (Real.rpow_pos_of_pos hL beta)
  have hZpow : ZA ^ d ≠ 0 :=
    ne_of_gt (Real.rpow_pos_of_pos hZA d)
  have hGpow : G ^ (1 - beta) ≠ 0 :=
    ne_of_gt (Real.rpow_pos_of_pos hG (1 - beta))
  rw [Real.log_mul (mul_ne_zero hKpow hLpow) hZpow,
      Real.log_mul hKpow hLpow,
      Real.log_mul hLpow hGpow]
  simp only [Real.log_rpow hK alpha, Real.log_rpow hL beta,
    Real.log_rpow hZA d, Real.log_rpow hG (1 - beta)]
  ring

#print axioms productivity_weight_recovers_A
#print axioms positive_aggregate_loss_log_formula

end ProposedPaperAllocationSourceAlgebraBridge
end Ventura26LiquidityAllocation
