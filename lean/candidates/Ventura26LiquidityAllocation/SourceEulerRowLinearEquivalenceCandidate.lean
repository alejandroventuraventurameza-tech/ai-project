import Ventura26LiquidityAllocation.SourceFirmEulerThreeRowZeroSetCandidate

/-!
# Exact invertible linear row operations on SOURCE's 33-equation index set

This is an abstract algebraic operator on residual vectors indexed by
LocalPrefixEquation.  The SOURCE-economic shear coefficients may be
obtained by evaluating the genuine SOURCE fields at a fixed Z, but that
economic identification and any Fréchet differentiability is separate.

A row operation adding a_i times the common pledge row to the date-one
Euler H and L rows has a two-sided inverse obtained by subtracting the
SAME multiples of that same, unchanged common pledge row.

No numerical determinant, Python transcription, or economic Jacobian
inverse is claimed here.
-/

namespace Ventura26LiquidityAllocation

/-- Two simultaneous linear row shears, leaving the common-pledge row
and all other rows untouched. -/
def sourceEulerRowsForward (aH aL : ℝ)
    (v : LocalPrefixEquation → ℝ) : LocalPrefixEquation → ℝ :=
  fun row => match row with
  | .firmCapitalEulerOneH => v .firmCapitalEulerOneH + aH * v .commonPledgeOne
  | .firmCapitalEulerOneL => v .firmCapitalEulerOneL + aL * v .commonPledgeOne
  | _ => v row

/-- Explicit inverse of the linear row shear. -/
def sourceEulerRowsBackward (aH aL : ℝ)
    (v : LocalPrefixEquation → ℝ) : LocalPrefixEquation → ℝ :=
  sourceEulerRowsForward (-aH) (-aL) v

/-- Right inverse for any 33-row real residual vector. -/
theorem sourceEulerRows_backward_forward
    (aH aL : ℝ) (v : LocalPrefixEquation → ℝ) :
    sourceEulerRowsBackward aH aL
      (sourceEulerRowsForward aH aL v) = v := by
  funext row
  cases row <;> simp [sourceEulerRowsBackward, sourceEulerRowsForward] <;> ring

#print axioms sourceEulerRows_backward_forward

/-- Left inverse, establishing a genuine bijection on the SOURCE row
index space, without computing an approximate floating determinant. -/
theorem sourceEulerRows_forward_backward
    (aH aL : ℝ) (v : LocalPrefixEquation → ℝ) :
    sourceEulerRowsForward aH aL
      (sourceEulerRowsBackward aH aL v) = v := by
  funext row
  cases row <;> simp [sourceEulerRowsBackward, sourceEulerRowsForward] <;> ring

#print axioms sourceEulerRows_forward_backward

/-- The full 33-row linear row transform is additive. -/
theorem sourceEulerRowsForward_add
    (aH aL : ℝ) (u v : LocalPrefixEquation → ℝ) :
    sourceEulerRowsForward aH aL (fun r => u r + v r) =
      (fun r => sourceEulerRowsForward aH aL u r +
        sourceEulerRowsForward aH aL v r) := by
  funext row
  cases row <;> simp [sourceEulerRowsForward] <;> ring

#print axioms sourceEulerRowsForward_add

/-- The full 33-row linear row transform respects real scalars. -/
theorem sourceEulerRowsForward_smul
    (aH aL c : ℝ) (v : LocalPrefixEquation → ℝ) :
    sourceEulerRowsForward aH aL (fun r => c * v r) =
      (fun r => c * sourceEulerRowsForward aH aL v r) := by
  funext row
  cases row <;> simp [sourceEulerRowsForward] <;> ring

#print axioms sourceEulerRowsForward_smul

/-- Exact preservation of a zero residual vector under the invertible
linear row operation (no economic equilibrium existence statement). -/
theorem sourceEulerRowsForward_all_zero_iff
    (aH aL : ℝ) (v : LocalPrefixEquation → ℝ) :
    (∀ r, sourceEulerRowsForward aH aL v r = 0) ↔
      (∀ r, v r = 0) := by
  constructor
  · intro h r
    have hv : sourceEulerRowsForward aH aL v =
        (fun _ => 0) := by
      funext k
      exact h k
    have hb := congrArg (sourceEulerRowsBackward aH aL) hv
    rw [sourceEulerRows_backward_forward] at hb
    have hz : sourceEulerRowsBackward aH aL (fun _ => 0) =
        (fun _ => 0) := by
      funext k
      cases k <;> simp [sourceEulerRowsBackward, sourceEulerRowsForward]
    rw [hz] at hb
    exact congrFun hb r
  · intro h r
    cases r <;> simp [sourceEulerRowsForward, h]

#print axioms sourceEulerRowsForward_all_zero_iff

end Ventura26LiquidityAllocation
