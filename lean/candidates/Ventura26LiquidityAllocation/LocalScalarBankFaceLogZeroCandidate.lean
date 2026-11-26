import Ventura26LiquidityAllocation.LocalScalarAugmented34SourceCandidate

/-!
# Exact zero equivalence of log and level bank-face residuals

The legacy Python evaluator uses a logarithmic bank-face transition
row. EconomicModel.lean uses a residual in levels. Their derivatives
need NOT agree. This module proves an iff about zero sets for the
source-defined renewal factor, under strict positivity of the two
terms in the ratio.

The Python constant aB=1/s.rate has NOT been identified with the
source bankRenewalFactor P here. That separate parameter equality
remains necessary before transferring a numerical root to the exact
source bank row.
-/

namespace Ventura26LiquidityAllocation
namespace ProposedLocalScalarBankFaceLogZero

/-- Real.log has extra zeros at 0 and -1 in mathlib's totalized
definition. Strict positivity of numerator and denominator therefore
matters economically and logically. -/
theorem log_ratio_zero_iff_level_zero
    (numerator denominator : ℝ)
    (hnum : 0 < numerator) (hden : 0 < denominator) :
    Real.log (numerator / denominator) = 0 ↔
      numerator - denominator = 0 := by
  constructor
  · intro hlog
    have hratio : numerator / denominator = 1 :=
      Real.eq_one_of_pos_of_log_eq_zero (div_pos hnum hden) hlog
    have heq : numerator = 1 * denominator :=
      (div_eq_iff (ne_of_gt hden)).mp hratio
    exact sub_eq_zero.mpr (by simpa using heq)
  · intro hzero
    have heq : numerator = denominator := sub_eq_zero.mp hzero
    rw [heq]
    simp [ne_of_gt hden]

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- The bank-face source equation is zero exactly when the log
of the source-consistent transition ratio is zero.
The state-positive hypotheses are NOT inferred from F=0. -/
theorem source_bankFace_log_residual_zero_iff
    (P : Primitives S) (d : LocalPrefixDateData)
    (hnext : 0 < d.nextBankFace)
    (hflow : 0 < bankRenewalFactor P *
      d.controls.loanRate * d.currentBankFace / d.controls.inflation) :
    Real.log
      (d.nextBankFace /
        (bankRenewalFactor P *
          d.controls.loanRate * d.currentBankFace / d.controls.inflation)) = 0 ↔
    localReducedRemainingResidual P d (0 : Fin 11) = 0 := by
  change Real.log
      (d.nextBankFace /
        (bankRenewalFactor P *
          d.controls.loanRate * d.currentBankFace / d.controls.inflation)) = 0 ↔
    d.nextBankFace -
      bankRenewalFactor P * d.controls.loanRate *
        d.currentBankFace / d.controls.inflation = 0
  exact log_ratio_zero_iff_level_zero _ _ hnext hflow

#print axioms log_ratio_zero_iff_level_zero
#print axioms source_bankFace_log_residual_zero_iff

end ProposedLocalScalarBankFaceLogZero
end Ventura26LiquidityAllocation
