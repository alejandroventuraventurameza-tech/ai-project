import Ventura26LiquidityAllocation.SourceFrozenP0ExactDecimalTailCandidate

/-!
# Date-zero and date-one actual SOURCE data for the frozen 10x6 P0 tail

The original source data builders localPrefixDateZeroData and
localPrefixDateOneData are used directly. Date zero's future controls
are the free prefix controls at date one. The date-one future controls
come from the frozen P0 SOURCE-typed finite continuation.

The actual source date-two control at every j is exactly
  u0_j * exp(sum_k C_jk z_k)
if the date-two compact state is x0 * exp(z), x0 is positive, and
C is the exact decimal-rational 10x6 P0 coefficient table already
checked against the frozen Python P0 input.

This is an OFF-ROOT identity on the genuine SOURCE finite prefix, not
equality of all Python economic functions, a proof of roundoff bounds,
or the infinite-horizon competitive equilibrium continuation.
-/

namespace Ventura26LiquidityAllocation

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- SOURCE date-zero next controls are the actual date-one PREFIX
controls, NOT the P0 tail; protects one-period timing. -/
theorem sourceFrozenP0_dateZero_nextControls
    (P : Primitives S) (I : InheritedState)
    (Z : LocalPrefixCoordinates) (dateOne : S) :
    (localPrefixDateZeroData P I Z dateOne).nextControls =
      Z.controlsOne := by
  rfl

#print axioms sourceFrozenP0_dateZero_nextControls

/-- In the actual date-one SOURCE record, date-two control levels
equal the P0 exponential response on the six-state log chart. -/
theorem sourceFrozenP0_dateOne_nextControl_level
    (P : Primitives S) (Z : LocalPrefixCoordinates)
    (dateOne recurrent : S)
    (x0 : LocalPrefixStateSix) (u0 : LocalPrefixControlsTen)
    (hx0 : LocalPrefixStateSixPositive x0)
    (z : Fin 6 → ℝ)
    (hstate : Z.stateTwo = localPrefixStateSixLogChart x0 z)
    (j : Fin 10) :
    localPrefixControlsTenVector
      (localPrefixDateOneData P Z dateOne recurrent
        (sourceLogLinearContinuation x0 u0
          sourceFrozenP0TenControls)).nextControls j =
      localPrefixControlsTenVector u0 j *
        Real.exp (∑ k : Fin 6,
          sourceFrozenP0TenControls j k * z k) := by
  change localPrefixControlsTenVector
    (sourceLogLinearContinuation x0 u0
      sourceFrozenP0TenControls Z.stateTwo) j = _
  rw [hstate, sourceLogLinearContinuation_on_chart
    x0 u0 sourceFrozenP0TenControls hx0 z]
  exact sourceFiniteTailControls_vector_eq
    u0 sourceFrozenP0TenControls z j

#print axioms sourceFrozenP0_dateOne_nextControl_level

/-- The same actual date-one SOURCE controls have the EXACT P0
log deviation; this uses positive baseline u0_j and zero-division
cancellation, not numerical approximation. -/
theorem sourceFrozenP0_dateOne_nextControl_log
    (P : Primitives S) (Z : LocalPrefixCoordinates)
    (dateOne recurrent : S)
    (x0 : LocalPrefixStateSix) (u0 : LocalPrefixControlsTen)
    (hx0 : LocalPrefixStateSixPositive x0)
    (hu0 : ∀ j : Fin 10, 0 < localPrefixControlsTenVector u0 j)
    (z : Fin 6 → ℝ)
    (hstate : Z.stateTwo = localPrefixStateSixLogChart x0 z)
    (j : Fin 10) :
    Real.log
      (localPrefixControlsTenVector
        (localPrefixDateOneData P Z dateOne recurrent
          (sourceLogLinearContinuation x0 u0
            sourceFrozenP0TenControls)).nextControls j /
        localPrefixControlsTenVector u0 j) =
    ∑ k : Fin 6, sourceFrozenP0TenControls j k * z k := by
  rw [sourceFrozenP0_dateOne_nextControl_level
    P Z dateOne recurrent x0 u0 hx0 z hstate j]
  have hne : localPrefixControlsTenVector u0 j ≠ 0 :=
    ne_of_gt (hu0 j)
  have hcancel :
      (localPrefixControlsTenVector u0 j *
          Real.exp (∑ k : Fin 6,
            sourceFrozenP0TenControls j k * z k)) /
            localPrefixControlsTenVector u0 j =
      Real.exp (∑ k : Fin 6,
        sourceFrozenP0TenControls j k * z k) := by
    field_simp [hne]
  rw [hcancel, Real.log_exp]

#print axioms sourceFrozenP0_dateOne_nextControl_log

/-- Every date-two finite-tail control in this SOURCE record remains
strictly positive for arbitrary finite log state deviations. -/
theorem sourceFrozenP0_dateOne_nextControl_positive
    (P : Primitives S) (Z : LocalPrefixCoordinates)
    (dateOne recurrent : S)
    (x0 : LocalPrefixStateSix) (u0 : LocalPrefixControlsTen)
    (hx0 : LocalPrefixStateSixPositive x0)
    (hu0 : ∀ j : Fin 10, 0 < localPrefixControlsTenVector u0 j)
    (z : Fin 6 → ℝ)
    (hstate : Z.stateTwo = localPrefixStateSixLogChart x0 z)
    (j : Fin 10) :
    0 < localPrefixControlsTenVector
      (localPrefixDateOneData P Z dateOne recurrent
        (sourceLogLinearContinuation x0 u0
          sourceFrozenP0TenControls)).nextControls j := by
  rw [sourceFrozenP0_dateOne_nextControl_level
    P Z dateOne recurrent x0 u0 hx0 z hstate j]
  exact mul_pos (hu0 j) (Real.exp_pos _)

#print axioms sourceFrozenP0_dateOne_nextControl_positive

end Ventura26LiquidityAllocation
