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

end CurrentPinnedReferenceSeparation
end Ventura26LiquidityAllocation
