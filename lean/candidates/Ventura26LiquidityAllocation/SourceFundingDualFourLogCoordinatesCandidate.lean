import Ventura26LiquidityAllocation.LocalScalarAugmented34SourceCandidate

/-!
# SOURCE normalized firm-L funding dual depends on exactly four log coordinates

These identities unfold the exact SOURCE economic definition
`localNormalizedCollateralDualL`, not a Python transcription.
They do not assume differentiability, positivity or Jacobian rank.

In the 33-dimensional positive log chart the scalar funding dual
depends directly only on date-zero L consumption (8), date-zero
loan rate (15), date-one L consumption (24) and date-one
inflation (28). Indirect equilibrium responses are not excluded.
-/

namespace Ventura26LiquidityAllocation

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- Exact four-coordinate formula for the true SOURCE normalized
funding dual in the original 33-dimensional logarithmic chart.
Valid algebraically even off the positive economic domain. -/
theorem sourceFundingDual_four_log_coordinate_formula
    (P : Primitives S) (Z0 : LocalPrefixCoordinates)
    (z : Fin 33 → ℝ) :
    localNormalizedCollateralDualL P (localPrefixLogChart Z0 z) =
      1 / (Z0.controlsZero.loanRate * Real.exp (z (15 : Fin 33))) -
      (P.entrepreneurDiscount *
        (Z0.controlsOne.consumptionL * Real.exp (z (24 : Fin 33))) ^
          (-P.entrepreneurRiskAversion) /
        (Z0.controlsZero.consumptionL * Real.exp (z (8 : Fin 33))) ^
          (-P.entrepreneurRiskAversion)) /
        (Z0.controlsOne.inflation * Real.exp (z (28 : Fin 33))) := by
  rfl

#print axioms sourceFundingDual_four_log_coordinate_formula

/-- At fixed primitives and chart origin, changing ANY of the other
29 SOURCE log coordinates leaves the normalized L funding dual
unchanged. This is direct functional dependence, not total policy
comparative statics. -/
theorem sourceFundingDual_eq_of_four_log_coordinates
    (P : Primitives S) (Z0 : LocalPrefixCoordinates)
    (z w : Fin 33 → ℝ)
    (h8 : z (8 : Fin 33) = w 8)
    (h15 : z (15 : Fin 33) = w 15)
    (h24 : z (24 : Fin 33) = w 24)
    (h28 : z (28 : Fin 33) = w 28) :
    localNormalizedCollateralDualL P (localPrefixLogChart Z0 z) =
      localNormalizedCollateralDualL P (localPrefixLogChart Z0 w) := by
  rw [sourceFundingDual_four_log_coordinate_formula P Z0 z,
      sourceFundingDual_four_log_coordinate_formula P Z0 w,
      h8, h15, h24, h28]

#print axioms sourceFundingDual_eq_of_four_log_coordinates

/-- The same four-coordinate sparsity is inherited verbatim by
the actual 34th SOURCE augmented residual; it is independent
of *both* the direct remuneration shock and the remaining 29
log coordinates at fixed listed four coordinates. -/
theorem sourceAugmented34_dual_eq_of_four_log_coordinates
    (P : Primitives S) (I : InheritedState)
    (Z0 : LocalPrefixCoordinates)
    (dateOne recurrent : S) (tail : LocalPrefixContinuationRule)
    (z w : Fin 33 → ℝ) (h h' : ℝ)
    (h8 : z (8 : Fin 33) = w 8)
    (h15 : z (15 : Fin 33) = w 15)
    (h24 : z (24 : Fin 33) = w 24)
    (h28 : z (28 : Fin 33) = w 28) :
    (ProposedLocalScalarAugmented34Source.augmentedBoundaryZeroResidual
      P I Z0 dateOne recurrent tail z h).2 =
    (ProposedLocalScalarAugmented34Source.augmentedBoundaryZeroResidual
      P I Z0 dateOne recurrent tail w h').2 := by
  change localNormalizedCollateralDualL P (localPrefixLogChart Z0 z) =
      localNormalizedCollateralDualL P (localPrefixLogChart Z0 w)
  exact sourceFundingDual_eq_of_four_log_coordinates
    P Z0 z w h8 h15 h24 h28

#print axioms sourceAugmented34_dual_eq_of_four_log_coordinates

end Ventura26LiquidityAllocation
