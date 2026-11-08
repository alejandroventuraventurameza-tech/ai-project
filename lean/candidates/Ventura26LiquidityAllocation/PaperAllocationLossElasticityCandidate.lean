import Ventura26LiquidityAllocation.PaperInterface

/-!
# Lemma 4.3: algebraic allocation-loss derivative and marginal-product ordering

The paper's full Lemma 4.3 also proves welfare-reference production and
nonnegative loss via production concavity and optimal labor. Those statements
are NOT claimed here.

This candidate formalizes:
1. the exact chain-rule coefficient algebra for differential changes in
   log capital K and in the optimal-labor aggregator G;
2. the equivalence between output-share > capital-share and physical
   marginal product of capital H > L for common alpha > 0;
3. the resulting strictly negative sign for a positive reallocation
   towards H when output share exceeds capital share.

Shares and the pair of log-capital directions are arbitrary real numbers
in the algebraic claim. The derivatives of K, G, capital paths and the
efficient benchmark are separate unproven source-mapping obligations.
-/

namespace Ventura26LiquidityAllocation
namespace ProposedPaperAllocationLossElasticity

/-- Capital share of H when each firm type has positive population mass
and the aggregate is the mass-weighted sum of capital per firm. -/
noncomputable def capitalShareH
    (vH vL kH kL : ℝ) : ℝ :=
  vH * kH / (vH * kH + vL * kL)

/-- Output share of H for the same type masses and output per firm. -/
noncomputable def outputShareH
    (vH vL yH yL : ℝ) : ℝ :=
  vH * yH / (vH * yH + vL * yL)

/-- Exact algebra behind the last line of Lemma 4.3:
    d(loss) = alpha * (kappaH - omegaH) * (d log kH - d log kL).
For two types, d log K and d log G have the respective weighted formulas
shown on the LHS, with gamma = alpha/(1-beta).
This does not itself prove those derivatives are supplied by the source
Cobb-Douglas production functions. -/
theorem allocation_loss_log_differential_algebra
    (alpha beta kappaH omegaH dLogKH dLogKL : ℝ)
    (hbeta : beta < 1) :
    alpha * (kappaH * dLogKH + (1 - kappaH) * dLogKL) -
      (1 - beta) * (alpha / (1 - beta)) *
        (omegaH * dLogKH + (1 - omegaH) * dLogKL) =
      alpha * (kappaH - omegaH) * (dLogKH - dLogKL) := by
  have hden : 1 - beta ≠ 0 := ne_of_gt (sub_pos.mpr hbeta)
  have hcancel : (1 - beta) * (alpha / (1 - beta)) = alpha := by
    field_simp [hden]
  rw [hcancel]
  ring

/-- Under common, positive capital elasticity alpha, a larger
H output share than capital share is equivalent to H having the larger
physical MPK; population weights cancel exactly. -/
theorem output_share_gt_capital_share_iff_productivity
    (vH vL kH kL yH yL : ℝ)
    (hvH : 0 < vH) (hvL : 0 < vL)
    (hkH : 0 < kH) (hkL : 0 < kL)
    (hyH : 0 < yH) (hyL : 0 < yL) :
    outputShareH vH vL yH yL > capitalShareH vH vL kH kL ↔
      yH / kH > yL / kL := by
  unfold outputShareH capitalShareH
  have hK : 0 < vH * kH + vL * kL := by positivity
  have hY : 0 < vH * yH + vL * yL := by positivity
  have hw : 0 < vH * vL := mul_pos hvH hvL
  constructor
  · intro h
    have hcross :
        (vH * kH) * (vH * yH + vL * yL) <
          (vH * yH) * (vH * kH + vL * kL) :=
      (div_lt_div_iff₀ hK hY).mp h
    have hweighted :
        (vH * vL) * (yL * kH) < (vH * vL) * (yH * kL) := by
      nlinarith [hcross]
    have hraw : yL * kH < yH * kL :=
      (mul_lt_mul_left hw).mp hweighted
    exact (div_lt_div_iff₀ hkL hkH).2 (by nlinarith [hraw])
  · intro h
    have hraw : yL * kH < yH * kL :=
      (div_lt_div_iff₀ hkL hkH).mp h
    have hweighted :
        (vH * vL) * (yL * kH) < (vH * vL) * (yH * kL) :=
      (mul_lt_mul_left hw).2 hraw
    have hcross :
        (vH * kH) * (vH * yH + vL * yL) <
          (vH * yH) * (vH * kH + vL * kL) := by
      nlinarith [hweighted]
    exact (div_lt_div_iff₀ hK hY).2 hcross

/-- Strictly proproductive reallocation reduces the local conditional
loss when H has an output share above its capital share. This is a sign
conditional on the differential identity above, not a comparative-static
equilibrium theorem. -/
theorem loss_direction_negative_of_reallocation
    (alpha kappaH omegaH dLogRatio : ℝ)
    (halpha : 0 < alpha) (hshare : kappaH < omegaH)
    (hreallocation : 0 < dLogRatio) :
    alpha * (kappaH - omegaH) * dLogRatio < 0 := by
  have hgap : kappaH - omegaH < 0 := sub_neg.mpr hshare
  have hfirst : alpha * (kappaH - omegaH) < 0 :=
    mul_neg_of_pos_of_neg halpha hgap
  exact mul_neg_of_neg_of_pos hfirst hreallocation

#print axioms allocation_loss_log_differential_algebra
#print axioms output_share_gt_capital_share_iff_productivity
#print axioms loss_direction_negative_of_reallocation

end ProposedPaperAllocationLossElasticity
end Ventura26LiquidityAllocation
