import Ventura26LiquidityAllocation.LocalScalarPolicyRuleTargetsCandidate

/-!
# Monetary policy source rows vs illustrative Python-style log residuals

The source EconomicModel.lean retains general persistence and Taylor
coefficients. The finite illustrative Python auxiliary uses:
  rate persistence 1/2; inflation coefficient 3/2; output 1/8;
  quantity persistence 1/2;
  steady rate rr, steady reserves M; a dated rule innovation.

Under explicit parameter identifications and positive gross nominal
variables, this file proves equality of the corresponding LOG
RESIDUAL FUNCTIONS in generic source LocalPrefixDateData, not just
their zero sets. It avoids asserting that the current Python
inputs or the stored numerical interval AD source coincide with
a specific Lean economic primitive.

The Python auxiliary computes positive exp targets; the additional
identity between these log residuals and Python's realized/target
log ratios is left outside the present file.
-/

namespace Ventura26LiquidityAllocation
namespace ProposedLocalScalarPythonMonetaryRuleBridge

variable {S : Type*} [Fintype S] [DecidableEq S]

open ProposedLocalScalarPolicyRuleTargets

/-- Log residual corresponding to the Python central-bank reserve
remuneration rule, after expanding the positive target into logs. -/
noncomputable def pythonStyleReserveRateResidual
    (P : Primitives S) (d : LocalPrefixDateData)
    (referenceRate outputRef : ℝ) : ℝ :=
  Real.log (d.currentReserveRate / referenceRate) -
    ((1 / 2 : ℝ) * Real.log (d.lagReserveRate / referenceRate) +
      (1 / 2 : ℝ) *
        ((3 / 2 : ℝ) * Real.log d.controls.inflation +
          (1 / 8 : ℝ) *
            Real.log (localPrefixAggregateOutput P d / outputRef)) +
      d.reserveRateInnovation)

/-- Log residual of the illustrative prepayment reserve-quantity rule. -/
noncomputable def pythonStyleReserveQuantityResidual
    (d : LocalPrefixDateData) (quantityRef : ℝ) : ℝ :=
  Real.log (d.currentReservesPre / quantityRef) -
    ((1 / 2 : ℝ) * Real.log (d.lagReservesPre / quantityRef) +
      d.reserveQuantityInnovation)

/-- Under EXACT coefficient and positive-domain restrictions, Lean's
original rate-rule residual is IDENTICAL to the illustrative
Python-style log residual. No economic parameter calibration is
silently provided here. -/
theorem source_rate_residual_eq_python_style
    (P : Primitives S) (d : LocalPrefixDateData)
    (referenceRate outputRef : ℝ)
    (hpersist : P.reserveRatePersistence = (1 / 2 : ℝ))
    (hsteady : P.reserveRateSteady = referenceRate)
    (hinflation : P.inflationResponse = (3 / 2 : ℝ))
    (houtput : P.outputResponse = (1 / 8 : ℝ))
    (houtputRef : P.outputReference = outputRef)
    (hrate : 0 < d.currentReserveRate)
    (hlag : 0 < d.lagReserveRate)
    (href : 0 < referenceRate) :
    localReducedRemainingResidual P d (6 : Fin 11) =
      pythonStyleReserveRateResidual P d referenceRate outputRef := by
  unfold pythonStyleReserveRateResidual
  change Real.log d.currentReserveRate -
    (P.reserveRatePersistence * Real.log d.lagReserveRate +
      (1 - P.reserveRatePersistence) *
        (Real.log P.reserveRateSteady +
          P.inflationResponse * Real.log d.controls.inflation +
          P.outputResponse *
            Real.log (localPrefixAggregateOutput P d / P.outputReference)) +
      d.reserveRateInnovation) = _
  rw [hpersist, hsteady, hinflation, houtput, houtputRef]
  rw [Real.log_div (ne_of_gt hrate) (ne_of_gt href),
    Real.log_div (ne_of_gt hlag) (ne_of_gt href)]
  ring

/-- Under 1/2 quantity persistence and positive nominal stocks,
the source money/reserve-quantity rule is literally the Python-style
log residual after the source steady quantity is identified. -/
theorem source_quantity_residual_eq_python_style
    (P : Primitives S) (d : LocalPrefixDateData)
    (quantityRef : ℝ)
    (hpersist : P.reserveQuantityPersistence = (1 / 2 : ℝ))
    (hsteady : P.reserveQuantitySteady = quantityRef)
    (hquantity : 0 < d.currentReservesPre)
    (hlag : 0 < d.lagReservesPre)
    (href : 0 < quantityRef) :
    localReducedRemainingResidual P d (7 : Fin 11) =
      pythonStyleReserveQuantityResidual d quantityRef := by
  unfold pythonStyleReserveQuantityResidual
  change Real.log d.currentReservesPre -
    (P.reserveQuantityPersistence * Real.log d.lagReservesPre +
      (1 - P.reserveQuantityPersistence) *
        Real.log P.reserveQuantitySteady +
      d.reserveQuantityInnovation) = _
  rw [hpersist, hsteady]
  rw [Real.log_div (ne_of_gt hquantity) (ne_of_gt href),
    Real.log_div (ne_of_gt hlag) (ne_of_gt href)]
  ring

/-- The zero-set results are immediate consequences of literal
residual equality under the same coefficient restrictions. -/
theorem source_rate_zero_iff_python_style_zero
    (P : Primitives S) (d : LocalPrefixDateData)
    (referenceRate outputRef : ℝ)
    (hpersist : P.reserveRatePersistence = (1 / 2 : ℝ))
    (hsteady : P.reserveRateSteady = referenceRate)
    (hinflation : P.inflationResponse = (3 / 2 : ℝ))
    (houtput : P.outputResponse = (1 / 8 : ℝ))
    (houtputRef : P.outputReference = outputRef)
    (hrate : 0 < d.currentReserveRate)
    (hlag : 0 < d.lagReserveRate)
    (href : 0 < referenceRate) :
    localReducedRemainingResidual P d (6 : Fin 11) = 0 ↔
      pythonStyleReserveRateResidual P d referenceRate outputRef = 0 := by
  rw [source_rate_residual_eq_python_style P d referenceRate outputRef
    hpersist hsteady hinflation houtput houtputRef hrate hlag href]

/-- Same zero-set transfer for reserve quantities. -/
theorem source_quantity_zero_iff_python_style_zero
    (P : Primitives S) (d : LocalPrefixDateData)
    (quantityRef : ℝ)
    (hpersist : P.reserveQuantityPersistence = (1 / 2 : ℝ))
    (hsteady : P.reserveQuantitySteady = quantityRef)
    (hquantity : 0 < d.currentReservesPre)
    (hlag : 0 < d.lagReservesPre)
    (href : 0 < quantityRef) :
    localReducedRemainingResidual P d (7 : Fin 11) = 0 ↔
      pythonStyleReserveQuantityResidual d quantityRef = 0 := by
  rw [source_quantity_residual_eq_python_style P d quantityRef
    hpersist hsteady hquantity hlag href]

#print axioms source_rate_residual_eq_python_style
#print axioms source_quantity_residual_eq_python_style
#print axioms source_rate_zero_iff_python_style_zero
#print axioms source_quantity_zero_iff_python_style_zero

end ProposedLocalScalarPythonMonetaryRuleBridge
end Ventura26LiquidityAllocation
