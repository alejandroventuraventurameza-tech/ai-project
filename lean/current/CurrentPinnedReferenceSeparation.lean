import Ventura26LiquidityAllocation.CurrentPinnedRationalBall

/-!
# Two mathematically distinct reference loan-rate brackets

The exact pinned SOURCE stationary construction has
  R_L < 81/80 = 1.0125
as proved by CurrentPinnedRationalBall.

The older interval-AD Python boundary constructor make_boundary()
solves a DIFFERENT scalar problem for a loan-rate R in the initial
bracket [1.025, 1.032], i.e., [41/40, 129/125].

This module proves the purely REAL incompatibility of those
rate intervals. It does NOT certify the Python interval producer
or identify its variables with the Lean SOURCE economic chart.

Consequently a conditional 34-row numerical root near the legacy
reference cannot be passed off as a 34-row root near the new
pinned SOURCE stationary reference. Different references are
consistent; equality is ruled out under the explicit bracket premise.
-/

namespace Ventura26LiquidityAllocation
namespace CurrentPinnedReferenceSeparation

open CurrentPinnedRationalBall

/-- The pinned loan rate lies strictly below the exact historical
Python boundary search's lower initial loan-rate bracket endpoint. -/
theorem pinned_loanRate_lt_legacy_lower :
    ProposedStationaryBank.loanRate < (41 / 40 : ℝ) := by
  have h := pinned_stationary_loanRate_lt_81_80
  linarith

#print axioms pinned_loanRate_lt_legacy_lower

/-- Any rate R in the historical search interval (or above its lower
endpoint) CANNOT equal the pinned stationary SOURCE loan rate.
This is conditional on interpreting R as the same gross loan-rate
variable, NOT a proof of Python-to-Lean semantic identity. -/
theorem legacy_boundary_rate_not_pinned
    (R : ℝ) (hlegacy : (41 / 40 : ℝ) ≤ R) :
    R ≠ ProposedStationaryBank.loanRate := by
  intro hEq
  have hupper := pinned_loanRate_lt_legacy_lower
  rw [hEq] at hlegacy
  linarith

#print axioms legacy_boundary_rate_not_pinned


/-- If the historical rate R is compared using the SAME pinned SOURCE
loan-rate log coordinate z[15], its initial bracket forces a positive
log displacement strictly larger than the certified 1/200 interior
radius. This is a CONDITIONAL chart statement, not a SOURCE-Python
chart identification, and does not assert existence of a 34-row root. -/
theorem legacy_rate_same_chart_forces_large_log_shift
    (R : ℝ) (z : CurrentSourceFullFDeriv.Row33)
    (hlegacy : (41 / 40 : ℝ) ≤ R)
    (hchart :
      R = ProposedStationaryBank.loanRate * Real.exp (z 15)) :
    (1 / 200 : ℝ) < z 15 := by
  have hrl :
      0 < ProposedStationaryBank.loanRate :=
    ProposedStationaryRealScale.loanRate_pos
  have hUpper := pinned_stationary_loanRate_lt_81_80
  have hprod :
      ProposedStationaryBank.loanRate * (82 / 81 : ℝ) <
        (41 / 40 : ℝ) := by
    nlinarith
  have hscaled :
      ProposedStationaryBank.loanRate * (82 / 81 : ℝ) <
        ProposedStationaryBank.loanRate * Real.exp (z 15) := by
    calc
      _ < (41 / 40 : ℝ) := hprod
      _ ≤ R := hlegacy
      _ = ProposedStationaryBank.loanRate * Real.exp (z 15) := hchart
  have hexp : (82 / 81 : ℝ) < Real.exp (z 15) :=
    (mul_lt_mul_left hrl).mp hscaled
  have hlog :
      Real.log (82 / 81 : ℝ) < z 15 := by
    simpa only [Real.log_exp] using
      (Real.log_lt_log (by norm_num : (0 : ℝ) < 82 / 81) hexp)
  have hlogLower : (1 / 82 : ℝ) ≤ Real.log (82 / 81 : ℝ) := by
    have h := Real.one_sub_inv_le_log_of_pos
      (show (0 : ℝ) < 82 / 81 by norm_num)
    convert h using 1 <;> norm_num
  linarith

#print axioms legacy_rate_same_chart_forces_large_log_shift

end CurrentPinnedReferenceSeparation
end Ventura26LiquidityAllocation
