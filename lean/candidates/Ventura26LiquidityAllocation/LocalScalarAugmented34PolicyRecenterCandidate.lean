import Ventura26LiquidityAllocation.LocalScalarAugmented34LogRecenterCandidate

/-!
# Exact policy recentering on the original reserve-remuneration instrument

A conditional 34x34 zero can have a nonzero hStar even if it is
extremely close to the legacy numerical center. Consequently, an
incremental shock dh must be applied to the ALREADY INTERVENED
primitives P(hStar), not directly to the old unshifted primitives P.

This module checks exactly what changes when the reserve-remuneration
innovation is applied twice, for every Markov state and calendar
history. It does not claim that the complete source residual map is
semantically identical to a Python enclosure, or that a root exists.
-/

namespace Ventura26LiquidityAllocation
namespace ProposedLocalScalarAugmented34PolicyRecenter

open ProposedLocalScalarEconomicSlice

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- The only policy instrument modified in this slice is the
state-contingent reserve-remuneration innovation. -/
noncomputable def reserveRemunerationShiftedPrimitives
    (P : Primitives S) (h : ℝ) : Primitives S :=
  initialIntervenedPrimitives P
    (localScalarParameterIntervention (reserveRemunerationSlice 0 h))

/-- The policy slice is affine in its two nonzero coordinates, with
the original zero-slack rate shift hStar pulled out explicitly. -/
theorem reserveRemunerationSlice_shift_add
    (s hStar dh : ℝ) :
    reserveRemunerationSlice s (hStar + dh) =
      reserveRemunerationSlice 0 hStar +
        reserveRemunerationSlice s dh := by
  funext j
  fin_cases j <;>
    simp [reserveRemunerationSlice, localScalarSlackDirection,
      localScalarReserveRateDirection] <;> ring

/-- Reserve remuneration has not changed the Markov tree. -/
@[simp] theorem reserveRemunerationShiftedPrimitives_tree
    (P : Primitives S) (h : ℝ) :
    (reserveRemunerationShiftedPrimitives P h).tree = P.tree := by
  rfl

/-- Exact reserve-rule innovation at every state. -/
theorem reserveRemunerationShiftedPrimitives_rate
    (P : Primitives S) (h : ℝ) (state : S) :
    (reserveRemunerationShiftedPrimitives P h).reserveRateInnovation state =
      P.reserveRateInnovation state +
        (if state = P.tree.initial then h else 0) := by
  simp [reserveRemunerationShiftedPrimitives,
    initialIntervenedPrimitives, localScalarParameterIntervention,
    reserveRemunerationSlice_rate]

/-- The quantity innovation is not an accidental second shock. -/
theorem reserveRemunerationShiftedPrimitives_quantity
    (P : Primitives S) (h : ℝ) (state : S) :
    (reserveRemunerationShiftedPrimitives P h).reserveQuantityInnovation state =
      P.reserveQuantityInnovation state := by
  simp [reserveRemunerationShiftedPrimitives,
    initialIntervenedPrimitives, localScalarParameterIntervention,
    reserveRemunerationSlice_quantity]

/-- The coefficient of reserve requirements is untouched throughout
the inherited and future calendar, including at date zero. -/
theorem reserveRemunerationShiftedPrimitives_requirement
    (P : Primitives S) (h : ℝ)
    (t : ℕ) (history : History S t) :
    (reserveRemunerationShiftedPrimitives P h).reserveRequirementPath t history =
      P.reserveRequirementPath t history := by
  simp [reserveRemunerationShiftedPrimitives,
    initialIntervenedPrimitives, localScalarParameterIntervention,
    reserveRemunerationSlice_requirement]

/-- The interest-rate corridor is not silently altered by a reserve
remuneration innovation. -/
theorem reserveRemunerationShiftedPrimitives_corridor
    (P : Primitives S) (h : ℝ)
    (t : ℕ) (history : History S t) :
    (reserveRemunerationShiftedPrimitives P h).corridorWidthPath t history =
      P.corridorWidthPath t history := by
  simp [reserveRemunerationShiftedPrimitives,
    initialIntervenedPrimitives, localScalarParameterIntervention,
    reserveRemunerationSlice_corridor]

/-- The baseline shift hStar and a later incremental shock dh add
as innovations of the EXACT source monetary rule in every state. -/
theorem reserveRemunerationShiftedPrimitives_rate_add
    (P : Primitives S) (hStar dh : ℝ) (state : S) :
    (reserveRemunerationShiftedPrimitives
      (reserveRemunerationShiftedPrimitives P hStar) dh).reserveRateInnovation state =
    (reserveRemunerationShiftedPrimitives P (hStar + dh)).reserveRateInnovation state := by
  by_cases hs : state = P.tree.initial
  · simp [reserveRemunerationShiftedPrimitives_rate, hs, add_assoc]
  · simp [reserveRemunerationShiftedPrimitives_rate, hs]

/-- The same composition preserves the source quantity innovation,
even in the double-intervention representation. -/
theorem reserveRemunerationShiftedPrimitives_quantity_add
    (P : Primitives S) (hStar dh : ℝ) (state : S) :
    (reserveRemunerationShiftedPrimitives
      (reserveRemunerationShiftedPrimitives P hStar) dh).reserveQuantityInnovation state =
    (reserveRemunerationShiftedPrimitives P (hStar + dh)).reserveQuantityInnovation state := by
  simp only [reserveRemunerationShiftedPrimitives_quantity]

/-- Reserve requirements are unchanged even by two consecutive
reserve-remuneration interventions. -/
theorem reserveRemunerationShiftedPrimitives_requirement_add
    (P : Primitives S) (hStar dh : ℝ)
    (t : ℕ) (history : History S t) :
    (reserveRemunerationShiftedPrimitives
      (reserveRemunerationShiftedPrimitives P hStar) dh).reserveRequirementPath t history =
    (reserveRemunerationShiftedPrimitives P (hStar + dh)).reserveRequirementPath t history := by
  simp only [reserveRemunerationShiftedPrimitives_requirement]

/-- The original corridor width is preserved by composing the two
reserve-remuneration interventions. -/
theorem reserveRemunerationShiftedPrimitives_corridor_add
    (P : Primitives S) (hStar dh : ℝ)
    (t : ℕ) (history : History S t) :
    (reserveRemunerationShiftedPrimitives
      (reserveRemunerationShiftedPrimitives P hStar) dh).corridorWidthPath t history =
    (reserveRemunerationShiftedPrimitives P (hStar + dh)).corridorWidthPath t history := by
  simp only [reserveRemunerationShiftedPrimitives_corridor]

#print axioms reserveRemunerationSlice_shift_add
#print axioms reserveRemunerationShiftedPrimitives_tree
#print axioms reserveRemunerationShiftedPrimitives_rate
#print axioms reserveRemunerationShiftedPrimitives_quantity
#print axioms reserveRemunerationShiftedPrimitives_requirement
#print axioms reserveRemunerationShiftedPrimitives_corridor
#print axioms reserveRemunerationShiftedPrimitives_rate_add
#print axioms reserveRemunerationShiftedPrimitives_quantity_add
#print axioms reserveRemunerationShiftedPrimitives_requirement_add
#print axioms reserveRemunerationShiftedPrimitives_corridor_add

end ProposedLocalScalarAugmented34PolicyRecenter
end Ventura26LiquidityAllocation
