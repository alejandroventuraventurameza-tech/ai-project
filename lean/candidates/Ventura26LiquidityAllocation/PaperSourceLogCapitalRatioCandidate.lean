import Ventura26LiquidityAllocation.PaperSourceOutputShareCandidate

/-!
# Lemma 4.3: formal derivative of log(kH(t)/kL(t))

This completes the interpretation of the capital-path direction on
the RHS of the paper's equation as the derivative of the actual log
capital ratio, instead of treating dLogKH-dLogKL as free symbols.
The capital stocks must be strictly positive at the reference time.
-/

namespace Ventura26LiquidityAllocation
namespace ProposedPaperSourceLogCapitalRatio

theorem original_log_capital_ratio_hasDerivAt
    (kH kL : ℝ → ℝ) (t dkH dkL : ℝ)
    (hkH : 0 < kH t) (hkL : 0 < kL t)
    (hH : HasDerivAt kH dkH t)
    (hL : HasDerivAt kL dkL t) :
    HasDerivAt
      (fun s => Real.log (kH s / kL s))
      (dkH / kH t - dkL / kL t) t := by
  have hdiv : HasDerivAt (fun s => kH s / kL s)
      ((dkH * kL t - kH t * dkL) / (kL t) ^ (2 : ℕ)) t :=
    hH.div hL (ne_of_gt hkL)
  have hlog := (Real.hasDerivAt_log
    (ne_of_gt (div_pos hkH hkL))).comp t hdiv
  have hquot :
      (kH t / kL t)⁻¹ *
        ((dkH * kL t - kH t * dkL) / (kL t) ^ (2 : ℕ)) =
        dkH / kH t - dkL / kL t := by
    field_simp [ne_of_gt hkH, ne_of_gt hkL] <;> ring
  rw [hquot] at hlog
  simpa only [Function.comp_def] using hlog

#print axioms original_log_capital_ratio_hasDerivAt

end ProposedPaperSourceLogCapitalRatio
end Ventura26LiquidityAllocation
