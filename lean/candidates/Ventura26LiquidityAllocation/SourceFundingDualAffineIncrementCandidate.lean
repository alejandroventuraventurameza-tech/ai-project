import Ventura26LiquidityAllocation.SourceReduced33RootEquivCandidate

/-!
# Genuine SOURCE exact affine funding-dual loan-rate elimination

The original SOURCE stationary L funding-dual zero condition is solved
by replacing log loan-rate coordinate z15 with
  -log(R0) - log(betaE) - z8 + z24 + z28.

Here this is proved directly from the literal SOURCE logarithm, with
strict positivity of the baseline loan rate and entrepreneurial discount.
The resulting 32-free-log lift has an EXACT finite-increment formula:
  delta z15 = -delta u8 + delta u23 + delta u27.
All other log coordinates retain their original increments.

This is exact real algebra, not binary64 automatic differentiation.
It does not identify Python with the complete SOURCE residual, verify
SOURCE Jacobian box bounds, or prove an economic root.
-/

namespace Ventura26LiquidityAllocation

open ProposedLocalScalarAugmented34Source
open ProposedLocalScalarEconomicSlice

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- The SOURCE closed-form eliminated loan-rate log is affine in the
three other economically relevant SOURCE log coordinates. -/
theorem sourceDualLoanLogTarget_exact_affine
    (P : Primitives S) (Z0 : LocalPrefixCoordinates)
    (z : Fin 33 → ℝ)
    (hr : 0 < Z0.controlsZero.loanRate)
    (hbeta : 0 < P.entrepreneurDiscount) :
    sourceDualLoanLogTarget P Z0 z =
      -Real.log Z0.controlsZero.loanRate -
        Real.log P.entrepreneurDiscount -
        z (8 : Fin 33) + z (24 : Fin 33) + z (28 : Fin 33) := by
  have hnum : P.entrepreneurDiscount * Real.exp (z (8 : Fin 33)) ≠ 0 :=
    mul_ne_zero (ne_of_gt hbeta) (Real.exp_ne_zero _)
  have hden :
      Real.exp (z (24 : Fin 33)) *
        Real.exp (z (28 : Fin 33)) ≠ 0 :=
    mul_ne_zero (Real.exp_ne_zero _) (Real.exp_ne_zero _)
  have hquot :
      (P.entrepreneurDiscount * Real.exp (z (8 : Fin 33))) /
        (Real.exp (z (24 : Fin 33)) *
          Real.exp (z (28 : Fin 33))) ≠ 0 :=
    div_ne_zero hnum hden
  unfold sourceDualLoanLogTarget
  rw [one_div, Real.log_inv,
    Real.log_mul (ne_of_gt hr) hquot,
    Real.log_div hnum hden,
    Real.log_mul (ne_of_gt hbeta) (Real.exp_ne_zero _),
    Real.log_mul (Real.exp_ne_zero _) (Real.exp_ne_zero _)]
  simp only [Real.log_exp]
  ring

#print axioms sourceDualLoanLogTarget_exact_affine

/-- The 15th SOURCE log of the precise 32-free-coordinate chart uses
indices 8,23,27 after removing coordinate 15. No policy innovation h
enters the analytic eliminated log rate directly. -/
theorem sourceFundingDualLift32_loanLog_affine
    (P : Primitives S) (Z0 : LocalPrefixCoordinates)
    (u : Fin 32 → ℝ)
    (hr : 0 < Z0.controlsZero.loanRate)
    (hbeta : 0 < P.entrepreneurDiscount) :
    sourceFundingDualLift32 P Z0 u (15 : Fin 33) =
      -Real.log Z0.controlsZero.loanRate -
        Real.log P.entrepreneurDiscount -
        u (8 : Fin 32) + u (23 : Fin 32) + u (27 : Fin 32) := by
  have htarget :
      sourceFundingDualLift32 P Z0 u (15 : Fin 33) =
        sourceDualLoanLogTarget P Z0 (sourceFundingDualLift32 P Z0 u) := by
    change
      sourceDualLoanLogEliminate P Z0
        ((15 : Fin 33).insertNth (0 : ℝ) u) (15 : Fin 33) =
      sourceDualLoanLogTarget P Z0
        (sourceDualLoanLogEliminate P Z0
          ((15 : Fin 33).insertNth (0 : ℝ) u))
    rw [sourceDualLoanLogEliminate_target_invariant]
    simp [sourceDualLoanLogEliminate]
  have h8 : sourceFundingDualLift32 P Z0 u (8 : Fin 33) =
      u (8 : Fin 32) := by
    simpa using sourceFundingDualLift32_other P Z0 u (8 : Fin 32)
  have h24 : sourceFundingDualLift32 P Z0 u (24 : Fin 33) =
      u (23 : Fin 32) := by
    simpa using sourceFundingDualLift32_other P Z0 u (23 : Fin 32)
  have h28 : sourceFundingDualLift32 P Z0 u (28 : Fin 33) =
      u (27 : Fin 32) := by
    simpa using sourceFundingDualLift32_other P Z0 u (27 : Fin 32)
  calc
    sourceFundingDualLift32 P Z0 u (15 : Fin 33) =
      sourceDualLoanLogTarget P Z0
        (sourceFundingDualLift32 P Z0 u) := htarget
    _ = -Real.log Z0.controlsZero.loanRate -
          Real.log P.entrepreneurDiscount -
          sourceFundingDualLift32 P Z0 u (8 : Fin 33) +
          sourceFundingDualLift32 P Z0 u (24 : Fin 33) +
          sourceFundingDualLift32 P Z0 u (28 : Fin 33) :=
      sourceDualLoanLogTarget_exact_affine P Z0
        (sourceFundingDualLift32 P Z0 u) hr hbeta
    _ = _ := by rw [h8, h24, h28]

#print axioms sourceFundingDualLift32_loanLog_affine

/-- The exact finite increment of the eliminated economic coordinate;
no finite-difference limit or numerical AD approximation is involved. -/
theorem sourceFundingDualLift32_loanLog_increment
    (P : Primitives S) (Z0 : LocalPrefixCoordinates)
    (u d : Fin 32 → ℝ)
    (hr : 0 < Z0.controlsZero.loanRate)
    (hbeta : 0 < P.entrepreneurDiscount) :
    sourceFundingDualLift32 P Z0 (u + d) (15 : Fin 33) -
      sourceFundingDualLift32 P Z0 u (15 : Fin 33) =
        -d (8 : Fin 32) + d (23 : Fin 32) + d (27 : Fin 32) := by
  rw [sourceFundingDualLift32_loanLog_affine P Z0 (u + d) hr hbeta,
    sourceFundingDualLift32_loanLog_affine P Z0 u hr hbeta]
  simp only [Pi.add_apply]
  ring

#print axioms sourceFundingDualLift32_loanLog_increment

/-- Every retained SOURCE log has exactly its corresponding free
coordinate increment under the 32-variable affine elimination. -/
theorem sourceFundingDualLift32_other_increment
    (P : Primitives S) (Z0 : LocalPrefixCoordinates)
    (u d : Fin 32 → ℝ) (i : Fin 32) :
    sourceFundingDualLift32 P Z0 (u + d)
        ((15 : Fin 33).succAbove i) -
      sourceFundingDualLift32 P Z0 u
        ((15 : Fin 33).succAbove i) = d i := by
  rw [sourceFundingDualLift32_other,
    sourceFundingDualLift32_other]
  simp

#print axioms sourceFundingDualLift32_other_increment

end Ventura26LiquidityAllocation
