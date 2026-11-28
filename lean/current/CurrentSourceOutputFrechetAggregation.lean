import Ventura26LiquidityAllocation.CurrentPinnedMonetaryRoots

/-!
# SOURCE aggregate output: exact Frechet aggregation bridge

This lemma is about the ORIGINAL two-firm SOURCE functions
`localPrefixOutput` and `localPrefixAggregateOutput`.
It does not assume that the aggregate function is differentiable.
Instead, it deduces the aggregate derivative from the two firm-level
derivatives. Proving those original Cobb-Douglas / labor-choice
firm derivatives remains the next scientific obligation in Issue #87.

No Jacobian identification, equilibrium existence, or external
Python surrogate is claimed.
-/

namespace Ventura26LiquidityAllocation
namespace CurrentSourceOutputFrechetAggregation

open CurrentSourceFullFDeriv
open CurrentPinnedBankDomain
open scoped Topology BigOperators

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- Exact SOURCE aggregation of the two firm-level Frechet derivatives. -/
theorem localPrefixAggregateOutput_hasFDerivAt_of_firms
    (P : Primitives S) (d : Row33 → LocalPrefixDateData)
    (x : Row33) (jH jL : Row33 →L[ℝ] ℝ)
    (hH : HasFDerivAt
      (fun z : Row33 => localPrefixOutput P (d z) .H) jH x)
    (hL : HasFDerivAt
      (fun z : Row33 => localPrefixOutput P (d z) .L) jL x) :
    HasFDerivAt
      (fun z : Row33 => localPrefixAggregateOutput P (d z))
      (P.mass .H • jH + P.mass .L • jL) x := by
  have hSum :
      (fun z : Row33 => localPrefixAggregateOutput P (d z)) =
        (fun z : Row33 =>
          P.mass .H * localPrefixOutput P (d z) .H +
          P.mass .L * localPrefixOutput P (d z) .L) := by
    funext z
    change (∑ i : FirmType, P.mass i * localPrefixOutput P (d z) i) =
      P.mass .H * localPrefixOutput P (d z) .H +
      P.mass .L * localPrefixOutput P (d z) .L
    rw [sum_firmType_eq_H_add_L]
  rw [hSum]
  exact (hH.const_mul (P.mass .H)).add (hL.const_mul (P.mass .L))

#print axioms localPrefixAggregateOutput_hasFDerivAt_of_firms

/-- Both original SOURCE dates inherit the same aggregation formula.
The four firm derivatives are explicit remaining hypotheses. -/
theorem pinned_two_aggregate_outputs_hasFDerivAt_of_firms
    (G : ℝ) (jH0 jL0 jH1 jL1 : Row33 →L[ℝ] ℝ)
    (hH0 : HasFDerivAt
      (fun z : Row33 => localPrefixOutput
        (ProposedStationaryPrimitives.primitives G)
        (pinnedDateZero G z) .H) jH0 (0 : Row33))
    (hL0 : HasFDerivAt
      (fun z : Row33 => localPrefixOutput
        (ProposedStationaryPrimitives.primitives G)
        (pinnedDateZero G z) .L) jL0 (0 : Row33))
    (hH1 : HasFDerivAt
      (fun z : Row33 => localPrefixOutput
        (ProposedStationaryPrimitives.primitives G)
        (pinnedDateOne G z) .H) jH1 (0 : Row33))
    (hL1 : HasFDerivAt
      (fun z : Row33 => localPrefixOutput
        (ProposedStationaryPrimitives.primitives G)
        (pinnedDateOne G z) .L) jL1 (0 : Row33)) :
    HasFDerivAt
      (fun z : Row33 => localPrefixAggregateOutput
        (ProposedStationaryPrimitives.primitives G)
        (pinnedDateZero G z))
      ((ProposedStationaryPrimitives.primitives G).mass .H • jH0 +
       (ProposedStationaryPrimitives.primitives G).mass .L • jL0)
      (0 : Row33) ∧
    HasFDerivAt
      (fun z : Row33 => localPrefixAggregateOutput
        (ProposedStationaryPrimitives.primitives G)
        (pinnedDateOne G z))
      ((ProposedStationaryPrimitives.primitives G).mass .H • jH1 +
       (ProposedStationaryPrimitives.primitives G).mass .L • jL1)
      (0 : Row33) := by
  constructor
  · exact localPrefixAggregateOutput_hasFDerivAt_of_firms
      (ProposedStationaryPrimitives.primitives G)
      (pinnedDateZero G) (0 : Row33) jH0 jL0 hH0 hL0
  · exact localPrefixAggregateOutput_hasFDerivAt_of_firms
      (ProposedStationaryPrimitives.primitives G)
      (pinnedDateOne G) (0 : Row33) jH1 jL1 hH1 hL1

#print axioms pinned_two_aggregate_outputs_hasFDerivAt_of_firms

end CurrentSourceOutputFrechetAggregation
end Ventura26LiquidityAllocation
