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


/-! ## Explicit micro-production and labor-aggregation bridge

These results connect the original firm technology to the aggregator
computed after allocating labor in proportion to adjusted productivity.
They do not prove the labor policy itself is globally optimal or
differentiate the resulting output with respect to capital.
-/

/-- Source Cobb-Douglas productivity times installed capital equals
the adjusted labor weight to the power 1-beta. The same exponent
b is required for both firm types in any subsequent aggregation. -/
theorem source_weight_pow_identity
    (A k a b : ℝ) (hA : 0 < A) (hk : 0 < k) (hb : b < 1) :
    (A ^ (1 / (1 - b)) * k ^ (a / (1 - b))) ^ (1 - b) =
      A * k ^ a := by
  have hden : 1 - b ≠ 0 := ne_of_gt (sub_pos.mpr hb)
  have hApow : 0 ≤ A ^ (1 / (1 - b)) :=
    (Real.rpow_pos_of_pos hA _).le
  have hkpow : 0 ≤ k ^ (a / (1 - b)) :=
    (Real.rpow_pos_of_pos hk _).le
  have hcancelA : (1 / (1 - b)) * (1 - b) = 1 := by
    field_simp [hden]
  have hcancelK : (a / (1 - b)) * (1 - b) = a := by
    field_simp [hden]
  calc
    (A ^ (1 / (1 - b)) * k ^ (a / (1 - b))) ^ (1 - b) =
        (A ^ (1 / (1 - b))) ^ (1 - b) *
          (k ^ (a / (1 - b))) ^ (1 - b) :=
      Real.mul_rpow hApow hkpow
    _ = A ^ ((1 / (1 - b)) * (1 - b)) *
          k ^ ((a / (1 - b)) * (1 - b)) := by
      rw [← Real.rpow_mul hA.le (1 / (1 - b)) (1 - b),
          ← Real.rpow_mul hk.le (a / (1 - b)) (1 - b)]
    _ = A * k ^ a := by rw [hcancelA, hcancelK]; simp

/-- The physical output of ONE firm, evaluated at a labor allocation
proportional to its adjusted weight g, is (L/G)^beta times g.
This proves the source mapping rather than assuming an output identity. -/
theorem source_output_at_weighted_labor
    (A k L G a b : ℝ)
    (hA : 0 < A) (hk : 0 < k)
    (hL : 0 < L) (hG : 0 < G) (hb : b < 1) :
    let g := A ^ (1 / (1 - b)) * k ^ (a / (1 - b))
    A * k ^ a * (L * g / G) ^ b = (L / G) ^ b * g := by
  let g : ℝ := A ^ (1 / (1 - b)) * k ^ (a / (1 - b))
  change A * k ^ a * (L * g / G) ^ b = (L / G) ^ b * g
  have hg : 0 < g := by
    dsimp [g]
    exact mul_pos (Real.rpow_pos_of_pos hA _) (Real.rpow_pos_of_pos hk _)
  have hsource : A * k ^ a = g ^ (1 - b) :=
    (source_weight_pow_identity A k a b hA hk hb).symm
  have hratio : 0 ≤ L / G := (div_pos hL hG).le
  have hfactor : (L * g / G) ^ b = (L / G) ^ b * g ^ b := by
    have hdiv : L * g / G = (L / G) * g := by ring
    rw [hdiv, Real.mul_rpow hratio hg.le]
  calc
    A * k ^ a * (L * g / G) ^ b =
        g ^ (1 - b) * ((L / G) ^ b * g ^ b) := by
      rw [hsource, hfactor]
    _ = (L / G) ^ b * (g ^ (1 - b) * g ^ b) := by ring
    _ = (L / G) ^ b * g := by
      have hexp : (1 - b) + b = 1 := by ring
      rw [← Real.rpow_add hg (1 - b) b, hexp]
      simp

/-- The positive aggregate scale cancels exactly when moving from
the weighted labor outputs to the paper's L^beta G^(1-beta). -/
theorem positive_labor_aggregate_power
    (L G b : ℝ) (hL : 0 < L) (hG : 0 < G) :
    (L / G) ^ b * G = L ^ b * G ^ (1 - b) := by
  calc
    (L / G) ^ b * G = (L ^ b / G ^ b) * G := by
      rw [Real.div_rpow hL.le hG.le]
    _ = L ^ b * (G / G ^ b) := by ring
    _ = L ^ b * G ^ (1 - b) := by
      rw [Real.rpow_sub hG 1 b]
      simp

/-- Direct production aggregation from the TWO original Cobb-Douglas
technologies when their elasticities a,b are common and labor is
assigned as ell_i=L*g_i/G. This is the micro-to-aggregate equality
missing from the older interface (which assumed the RHS as a definition). -/
theorem source_two_type_output_at_optimal_labor
    (vH vL AH AL kH kL L a b : ℝ)
    (hvH : 0 < vH) (hvL : 0 < vL)
    (hAH : 0 < AH) (hAL : 0 < AL)
    (hkH : 0 < kH) (hkL : 0 < kL)
    (hL : 0 < L) (hb : b < 1) :
    let gH := AH ^ (1 / (1 - b)) * kH ^ (a / (1 - b))
    let gL := AL ^ (1 / (1 - b)) * kL ^ (a / (1 - b))
    let G := vH * gH + vL * gL
    vH * (AH * kH ^ a * (L * gH / G) ^ b) +
      vL * (AL * kL ^ a * (L * gL / G) ^ b) =
      L ^ b * G ^ (1 - b) := by
  let gH : ℝ := AH ^ (1 / (1 - b)) * kH ^ (a / (1 - b))
  let gL : ℝ := AL ^ (1 / (1 - b)) * kL ^ (a / (1 - b))
  let G : ℝ := vH * gH + vL * gL
  change vH * (AH * kH ^ a * (L * gH / G) ^ b) +
      vL * (AL * kL ^ a * (L * gL / G) ^ b) =
      L ^ b * G ^ (1 - b)
  have hgH : 0 < gH := by
    dsimp [gH]
    exact mul_pos (Real.rpow_pos_of_pos hAH _) (Real.rpow_pos_of_pos hkH _)
  have hgL : 0 < gL := by
    dsimp [gL]
    exact mul_pos (Real.rpow_pos_of_pos hAL _) (Real.rpow_pos_of_pos hkL _)
  have hG : 0 < G := by
    dsimp [G]
    exact add_pos (mul_pos hvH hgH) (mul_pos hvL hgL)
  have hfirmH : AH * kH ^ a * (L * gH / G) ^ b =
      (L / G) ^ b * gH := by
    exact source_output_at_weighted_labor AH kH L G a b hAH hkH hL hG hb
  have hfirmL : AL * kL ^ a * (L * gL / G) ^ b =
      (L / G) ^ b * gL := by
    exact source_output_at_weighted_labor AL kL L G a b hAL hkL hL hG hb
  calc
    vH * (AH * kH ^ a * (L * gH / G) ^ b) +
        vL * (AL * kL ^ a * (L * gL / G) ^ b) =
      vH * ((L / G) ^ b * gH) + vL * ((L / G) ^ b * gL) := by
        rw [hfirmH, hfirmL]
    _ = (L / G) ^ b * G := by dsimp [G]; ring
    _ = L ^ b * G ^ (1 - b) := positive_labor_aggregate_power L G b hL hG

/-- The labor distribution used in the source aggregation is strictly
positive and satisfies the original aggregate labor budget. -/
theorem source_labor_candidate_clears_resources
    (vH vL gH gL L : ℝ)
    (hvH : 0 < vH) (hvL : 0 < vL)
    (hgH : 0 < gH) (hgL : 0 < gL) (hL : 0 < L) :
    let G := vH * gH + vL * gL
    0 < L * gH / G ∧
      0 < L * gL / G ∧
      vH * (L * gH / G) + vL * (L * gL / G) = L := by
  let G : ℝ := vH * gH + vL * gL
  change 0 < L * gH / G ∧
    0 < L * gL / G ∧
    vH * (L * gH / G) + vL * (L * gL / G) = L
  have hG : 0 < G := by
    dsimp [G]
    exact add_pos (mul_pos hvH hgH) (mul_pos hvL hgL)
  constructor
  · exact div_pos (mul_pos hL hgH) hG
  constructor
  · exact div_pos (mul_pos hL hgL) hG
  · dsimp [G]
    field_simp [ne_of_gt hG]
    ring

#print axioms source_weight_pow_identity
#print axioms source_output_at_weighted_labor
#print axioms positive_labor_aggregate_power
#print axioms source_two_type_output_at_optimal_labor
#print axioms source_labor_candidate_clears_resources

#print axioms productivity_weight_recovers_A
#print axioms positive_aggregate_loss_log_formula

end ProposedPaperAllocationSourceAlgebraBridge
end Ventura26LiquidityAllocation
