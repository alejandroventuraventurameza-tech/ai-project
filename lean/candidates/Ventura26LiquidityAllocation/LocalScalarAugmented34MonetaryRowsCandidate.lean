import Ventura26LiquidityAllocation.LocalScalarPythonMonetaryFourPrefixRowsCandidate
import Ventura26LiquidityAllocation.LocalScalarAugmented34PolicyRecenterCandidate

/-!
# Actual four monetary rows of the augmented 34-equation SOURCE operator

The previously checked generic date-data identities are now applied to
the REAL source operator `augmentedBoundaryZeroResidual`. The latter
uses the source log chart and date-zero remuneration intervention.
The four indices (12, 13, 28, 29) are literal original prefix rows,
not a guessed reordering of the external Python residual list.

Under the explicitly displayed calibration, date data and positivity
premises, the four monetary components equal the Python-style
`log(realized / auxiliary target)` functions. This is a theorem about
the Lean representation of those expressions; it does NOT prove that
Python's concrete arrays, interval AD, or external numerical input
have been identified with the Lean source data. Nor is this a proof
of the other 30 equations or a full competitive equilibrium.
-/

namespace Ventura26LiquidityAllocation
namespace ProposedLocalScalarAugmented34MonetaryRows

open ProposedLocalScalarPythonMonetaryExpTargets
open ProposedLocalScalarPythonMonetaryFourPrefixRows
open ProposedLocalScalarAugmented34Source
open ProposedLocalScalarAugmented34PolicyRecenter

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- Exact source rate-rule calibration required by the Python
illustrative `auxiliary`; no calibration is manufactured. -/
def RateCalibration
    (P : Primitives S) (referenceRate outputRef : ℝ) : Prop :=
  P.reserveRatePersistence = (1 / 2 : ℝ) ∧
  P.reserveRateSteady = referenceRate ∧
  P.inflationResponse = (3 / 2 : ℝ) ∧
  P.outputResponse = (1 / 8 : ℝ) ∧
  P.outputReference = outputRef

/-- Exact source quantity-rule calibration, independent of the
remuneration innovation and of the reserve requirement. -/
def QuantityCalibration
    (P : Primitives S) (quantityRef : ℝ) : Prop :=
  P.reserveQuantityPersistence = (1 / 2 : ℝ) ∧
  P.reserveQuantitySteady = quantityRef

/-- An initial-date remuneration shock changes neither the
persistence and Taylor coefficients nor the source steady targets. -/
theorem rate_calibration_preserved
    (P : Primitives S) (h referenceRate outputRef : ℝ)
    (hc : RateCalibration P referenceRate outputRef) :
    RateCalibration (reserveRemunerationShiftedPrimitives P h)
      referenceRate outputRef := by
  simpa only [RateCalibration, reserveRemunerationShiftedPrimitives,
    initialIntervenedPrimitives] using hc

/-- The same source experiment leaves the quantity calibration intact. -/
theorem quantity_calibration_preserved
    (P : Primitives S) (h quantityRef : ℝ)
    (hc : QuantityCalibration P quantityRef) :
    QuantityCalibration (reserveRemunerationShiftedPrimitives P h)
      quantityRef := by
  simpa only [QuantityCalibration, reserveRemunerationShiftedPrimitives,
    initialIntervenedPrimitives] using hc

/-- Original augmented rows 12 and 28, at dates zero and one,
respectively, are EXACTLY the source representations of the
Python auxiliary rate log ratios. The two dates share coefficients
but use DIFFERENT lag and innovation data. -/
theorem augmented_reserve_rate_rows_eq_python_log_ratios
    (P : Primitives S) (I : InheritedState) (Z0 : LocalPrefixCoordinates)
    (dateOne recurrent : S) (tail : LocalPrefixContinuationRule)
    (z : Fin 33 → ℝ) (h referenceRate outputRef : ℝ)
    (hcal : RateCalibration P referenceRate outputRef)
    (hrate0 : 0 <
      (localPrefixDateZeroData (reserveRemunerationShiftedPrimitives P h)
        I (localPrefixLogChart Z0 z) dateOne).currentReserveRate)
    (hlag0 : 0 <
      (localPrefixDateZeroData (reserveRemunerationShiftedPrimitives P h)
        I (localPrefixLogChart Z0 z) dateOne).lagReserveRate)
    (hrate1 : 0 <
      (localPrefixDateOneData (reserveRemunerationShiftedPrimitives P h)
        (localPrefixLogChart Z0 z) dateOne recurrent tail).currentReserveRate)
    (hlag1 : 0 <
      (localPrefixDateOneData (reserveRemunerationShiftedPrimitives P h)
        (localPrefixLogChart Z0 z) dateOne recurrent tail).lagReserveRate)
    (href : 0 < referenceRate) :
    let Pv := reserveRemunerationShiftedPrimitives P h
    let Z := localPrefixLogChart Z0 z
    let d0 := localPrefixDateZeroData Pv I Z dateOne
    let d1 := localPrefixDateOneData Pv Z dateOne recurrent tail
    ((augmentedBoundaryZeroResidual P I Z0 dateOne recurrent tail z h).1
        (12 : Fin 33) =
      Real.log (d0.currentReserveRate /
        pythonAuxiliaryRateTarget Pv d0 referenceRate outputRef)) ∧
    ((augmentedBoundaryZeroResidual P I Z0 dateOne recurrent tail z h).1
        (28 : Fin 33) =
      Real.log (d1.currentReserveRate /
        pythonAuxiliaryRateTarget Pv d1 referenceRate outputRef)) := by
  let Pv := reserveRemunerationShiftedPrimitives P h
  let Z := localPrefixLogChart Z0 z
  let d0 := localPrefixDateZeroData Pv I Z dateOne
  let d1 := localPrefixDateOneData Pv Z dateOne recurrent tail
  have hcal' := rate_calibration_preserved P h referenceRate outputRef hcal
  rcases hcal' with ⟨hpersist, hsteady, hinflation, houtput, houtputRef⟩
  have hsource := both_prefix_reserve_rate_rows_eq_python_log_ratios
    LocalPrefixBranch.binding Pv I Z dateOne recurrent tail
    referenceRate outputRef hpersist hsteady hinflation houtput
    houtputRef hrate0 hlag0 hrate1 hlag1 href
  constructor
  · change localReducedPrefixResidual LocalPrefixBranch.binding
      Pv I Z dateOne recurrent tail
      LocalPrefixEquation.reserveRateRuleZero =
      Real.log (d0.currentReserveRate /
        pythonAuxiliaryRateTarget Pv d0 referenceRate outputRef)
    exact hsource.1
  · change localReducedPrefixResidual LocalPrefixBranch.binding
      Pv I Z dateOne recurrent tail
      LocalPrefixEquation.reserveRateRuleOne =
      Real.log (d1.currentReserveRate /
        pythonAuxiliaryRateTarget Pv d1 referenceRate outputRef)
    exact hsource.2

/-- Original augmented rows 13 and 29 are the TWO genuine
quantity-rule log ratios, without conflating quantity and rate shocks. -/
theorem augmented_reserve_quantity_rows_eq_python_log_ratios
    (P : Primitives S) (I : InheritedState) (Z0 : LocalPrefixCoordinates)
    (dateOne recurrent : S) (tail : LocalPrefixContinuationRule)
    (z : Fin 33 → ℝ) (h quantityRef : ℝ)
    (hcal : QuantityCalibration P quantityRef)
    (hquantity0 : 0 <
      (localPrefixDateZeroData (reserveRemunerationShiftedPrimitives P h)
        I (localPrefixLogChart Z0 z) dateOne).currentReservesPre)
    (hlag0 : 0 <
      (localPrefixDateZeroData (reserveRemunerationShiftedPrimitives P h)
        I (localPrefixLogChart Z0 z) dateOne).lagReservesPre)
    (hquantity1 : 0 <
      (localPrefixDateOneData (reserveRemunerationShiftedPrimitives P h)
        (localPrefixLogChart Z0 z) dateOne recurrent tail).currentReservesPre)
    (hlag1 : 0 <
      (localPrefixDateOneData (reserveRemunerationShiftedPrimitives P h)
        (localPrefixLogChart Z0 z) dateOne recurrent tail).lagReservesPre)
    (href : 0 < quantityRef) :
    let Pv := reserveRemunerationShiftedPrimitives P h
    let Z := localPrefixLogChart Z0 z
    let d0 := localPrefixDateZeroData Pv I Z dateOne
    let d1 := localPrefixDateOneData Pv Z dateOne recurrent tail
    ((augmentedBoundaryZeroResidual P I Z0 dateOne recurrent tail z h).1
        (13 : Fin 33) =
      Real.log (d0.currentReservesPre /
        pythonAuxiliaryQuantityTarget d0 quantityRef)) ∧
    ((augmentedBoundaryZeroResidual P I Z0 dateOne recurrent tail z h).1
        (29 : Fin 33) =
      Real.log (d1.currentReservesPre /
        pythonAuxiliaryQuantityTarget d1 quantityRef)) := by
  let Pv := reserveRemunerationShiftedPrimitives P h
  let Z := localPrefixLogChart Z0 z
  let d0 := localPrefixDateZeroData Pv I Z dateOne
  let d1 := localPrefixDateOneData Pv Z dateOne recurrent tail
  have hcal' := quantity_calibration_preserved P h quantityRef hcal
  rcases hcal' with ⟨hpersist, hsteady⟩
  have hsource := both_prefix_reserve_quantity_rows_eq_python_log_ratios
    LocalPrefixBranch.binding Pv I Z dateOne recurrent tail
    quantityRef hpersist hsteady hquantity0 hlag0 hquantity1 hlag1 href
  constructor
  · change localReducedPrefixResidual LocalPrefixBranch.binding
      Pv I Z dateOne recurrent tail
      LocalPrefixEquation.reserveQuantityRuleZero =
      Real.log (d0.currentReservesPre /
        pythonAuxiliaryQuantityTarget d0 quantityRef)
    exact hsource.1
  · change localReducedPrefixResidual LocalPrefixBranch.binding
      Pv I Z dateOne recurrent tail
      LocalPrefixEquation.reserveQuantityRuleOne =
      Real.log (d1.currentReservesPre /
        pythonAuxiliaryQuantityTarget d1 quantityRef)
    exact hsource.2

/-- Source date-zero remuneration innovation is additive. -/
theorem date_zero_rate_innovation_is_original_plus_shock
    (P : Primitives S) (I : InheritedState)
    (Z0 : LocalPrefixCoordinates) (dateOne : S)
    (z : Fin 33 → ℝ) (h : ℝ) :
    (localPrefixDateZeroData
      (reserveRemunerationShiftedPrimitives P h) I
      (localPrefixLogChart Z0 z) dateOne).reserveRateInnovation =
        P.reserveRateInnovation P.tree.initial + h := by
  simp [localPrefixDateZeroData,
    reserveRemunerationShiftedPrimitives_rate]

/-- If date one is a distinct Markov state, it inherits its ORIGINAL
rate innovation: the experimental shock applies only at date zero. -/
theorem date_one_rate_innovation_is_unchanged
    (P : Primitives S) (Z0 : LocalPrefixCoordinates)
    (dateOne recurrent : S) (tail : LocalPrefixContinuationRule)
    (z : Fin 33 → ℝ) (h : ℝ)
    (hdate : dateOne ≠ P.tree.initial) :
    (localPrefixDateOneData
      (reserveRemunerationShiftedPrimitives P h)
      (localPrefixLogChart Z0 z) dateOne recurrent tail).reserveRateInnovation =
        P.reserveRateInnovation dateOne := by
  simp [localPrefixDateOneData,
    reserveRemunerationShiftedPrimitives_rate, hdate]

#print axioms rate_calibration_preserved
#print axioms quantity_calibration_preserved
#print axioms augmented_reserve_rate_rows_eq_python_log_ratios
#print axioms augmented_reserve_quantity_rows_eq_python_log_ratios
#print axioms date_zero_rate_innovation_is_original_plus_shock
#print axioms date_one_rate_innovation_is_unchanged

end ProposedLocalScalarAugmented34MonetaryRows
end Ventura26LiquidityAllocation
