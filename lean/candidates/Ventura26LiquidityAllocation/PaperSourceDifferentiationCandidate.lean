import Ventura26LiquidityAllocation.PaperOriginalLogLossCandidate
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# Lemma 4.3: differential bridge from original capital paths

The older paper proof computed differential coefficient algebra but did not
differentiate K(k) and G(k) as source functions. This file begins that
missing formal bridge. Firm masses and productivities are fixed; capital
per firm may vary through any differentiable positive paths kH(t), kL(t).
All claims below are exact HasDerivAt statements and are not definitions
of derivatives or assumptions about those derivatives.
-/

namespace Ventura26LiquidityAllocation
namespace ProposedPaperSourceDifferentiation

/-- Aggregate physical capital, with each per-firm capital stock a
differentiable real-valued path. -/
theorem source_total_capital_hasDerivAt
    (vH vL : ℝ) (kH kL : ℝ → ℝ) (t dkH dkL : ℝ)
    (hH : HasDerivAt kH dkH t)
    (hL : HasDerivAt kL dkL t) :
    HasDerivAt (fun s => vH * kH s + vL * kL s)
      (vH * dkH + vL * dkL) t := by
  exact (hH.const_mul vH).add (hL.const_mul vL)

/-- Derivative of the ORIGINAL adjusted productivity aggregator
G(t)=sum_i v_i A_i^(1/(1-beta)) k_i(t)^(alpha/(1-beta)).
The two firms share the same exponents and strictly positive capital
at the evaluation date. -/
theorem source_productivity_aggregate_hasDerivAt
    (vH vL AH AL a b : ℝ) (kH kL : ℝ → ℝ)
    (t dkH dkL : ℝ)
    (hkH : 0 < kH t) (hkL : 0 < kL t)
    (hH : HasDerivAt kH dkH t)
    (hL : HasDerivAt kL dkL t) :
    let gamma := a / (1 - b)
    let cH := vH * AH ^ (1 / (1 - b))
    let cL := vL * AL ^ (1 / (1 - b))
    HasDerivAt
      (fun s => cH * (kH s) ^ gamma + cL * (kL s) ^ gamma)
      (cH * (gamma * (kH t) ^ (gamma - 1) * dkH) +
        cL * (gamma * (kL t) ^ (gamma - 1) * dkL)) t := by
  let gamma : ℝ := a / (1 - b)
  let cH : ℝ := vH * AH ^ (1 / (1 - b))
  let cL : ℝ := vL * AL ^ (1 / (1 - b))
  change HasDerivAt
    (fun s => cH * (kH s) ^ gamma + cL * (kL s) ^ gamma)
    (cH * (gamma * (kH t) ^ (gamma - 1) * dkH) +
      cL * (gamma * (kL t) ^ (gamma - 1) * dkL)) t
  have hpH :
      HasDerivAt (fun s => (kH s) ^ gamma)
        (gamma * (kH t) ^ (gamma - 1) * dkH) t :=
    (Real.hasDerivAt_rpow_const (Or.inl (ne_of_gt hkH))).comp t hH
  have hpL :
      HasDerivAt (fun s => (kL s) ^ gamma)
        (gamma * (kL t) ^ (gamma - 1) * dkL) t :=
    (Real.hasDerivAt_rpow_const (Or.inl (ne_of_gt hkL))).comp t hL
  exact (hpH.const_mul cH).add (hpL.const_mul cL)

/-- Exact log derivative from the original mass-weighted K(t);
the positivity assumption concerns the observed aggregate K(t). -/
theorem source_log_total_capital_hasDerivAt
    (vH vL : ℝ) (kH kL : ℝ → ℝ)
    (t dkH dkL : ℝ)
    (hK : 0 < vH * kH t + vL * kL t)
    (hH : HasDerivAt kH dkH t)
    (hL : HasDerivAt kL dkL t) :
    HasDerivAt
      (fun s => Real.log (vH * kH s + vL * kL s))
      ((vH * kH t + vL * kL t)⁻¹ * (vH * dkH + vL * dkL)) t := by
  have hsource := source_total_capital_hasDerivAt
    vH vL kH kL t dkH dkL hH hL
  have hlog := (Real.hasDerivAt_log (ne_of_gt hK)).comp t hsource
  simpa only [Function.comp_def] using hlog

/-- Exact derivative of log G(t) by differentiating its positive
source-weighted rpow terms. No share-weighted identity is assumed. -/
theorem source_log_productivity_aggregate_hasDerivAt
    (vH vL AH AL a b : ℝ) (kH kL : ℝ → ℝ)
    (t dkH dkL : ℝ)
    (hkH : 0 < kH t) (hkL : 0 < kL t)
    (hG : 0 < vH * AH ^ (1 / (1 - b)) * (kH t) ^ (a / (1 - b)) +
      vL * AL ^ (1 / (1 - b)) * (kL t) ^ (a / (1 - b)))
    (hH : HasDerivAt kH dkH t)
    (hL : HasDerivAt kL dkL t) :
    let gamma := a / (1 - b)
    let cH := vH * AH ^ (1 / (1 - b))
    let cL := vL * AL ^ (1 / (1 - b))
    HasDerivAt
      (fun s => Real.log
        (cH * (kH s) ^ gamma + cL * (kL s) ^ gamma))
      ( (cH * (kH t) ^ gamma + cL * (kL t) ^ gamma)⁻¹ *
          (cH * (gamma * (kH t) ^ (gamma - 1) * dkH) +
            cL * (gamma * (kL t) ^ (gamma - 1) * dkL))) t := by
  let gamma : ℝ := a / (1 - b)
  let cH : ℝ := vH * AH ^ (1 / (1 - b))
  let cL : ℝ := vL * AL ^ (1 / (1 - b))
  change HasDerivAt
    (fun s => Real.log (cH * (kH s) ^ gamma + cL * (kL s) ^ gamma))
    ((cH * (kH t) ^ gamma + cL * (kL t) ^ gamma)⁻¹ *
      (cH * (gamma * (kH t) ^ (gamma - 1) * dkH) +
        cL * (gamma * (kL t) ^ (gamma - 1) * dkL))) t
  have hsource := source_productivity_aggregate_hasDerivAt
    vH vL AH AL a b kH kL t dkH dkL hkH hkL hH hL
  have hlog := (Real.hasDerivAt_log (ne_of_gt hG)).comp t hsource
  simpa only [Function.comp_def] using hlog

#print axioms source_total_capital_hasDerivAt
#print axioms source_productivity_aggregate_hasDerivAt
#print axioms source_log_total_capital_hasDerivAt
#print axioms source_log_productivity_aggregate_hasDerivAt

end ProposedPaperSourceDifferentiation
end Ventura26LiquidityAllocation
