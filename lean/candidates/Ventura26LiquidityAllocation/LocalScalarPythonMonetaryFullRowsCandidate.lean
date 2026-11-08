import Ventura26LiquidityAllocation.LocalScalarPythonMonetaryExpTargetsCandidate

/-!
# Exact monetary policy RESIDUALS from source to Python auxiliary

The finite_bridge.py remaining(...) policy rows use the logarithms
    log(realized_reserve_rate / auxiliary(...).rr)
    log(realized_reserves_pre / auxiliary(...).money).
This module proves these expressions IDENTICAL (not only zero-set
equivalent) to the ORIGINAL EconomicModel.lean source residuals
under explicit source parameter and state identifications and
strictly positive current/lagged nominal rates and reference stocks.

These theorems hold for generic LocalPrefixDateData, and thus can
serve date-zero and date-one row matches. They do not certify
the concrete numerical Python base vector, continuation, initial
policy intervention, or the Banach interval boxes as a Lean witness.
-/

namespace Ventura26LiquidityAllocation
namespace ProposedLocalScalarPythonMonetaryFullRows

open ProposedLocalScalarPolicyRuleTargets
open ProposedLocalScalarPythonMonetaryExpTargets

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- The source reserve-remuneration row is literally the Python
log(realized/auxiliary rate target), not just an equivalent zero
condition. The model's numerical references are explicit premises. -/
theorem source_reserve_rate_row_eq_python_auxiliary_log_ratio
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
      Real.log
        (d.currentReserveRate /
          pythonAuxiliaryRateTarget P d referenceRate outputRef) := by
  calc
    localReducedRemainingResidual P d (6 : Fin 11)
        = Real.log d.currentReserveRate -
            sourceReserveRateLogTarget P d := by rfl
    _ = Real.log
        (d.currentReserveRate /
          Real.exp (sourceReserveRateLogTarget P d)) := by
      rw [Real.log_div (ne_of_gt hrate)
        (ne_of_gt (Real.exp_pos (sourceReserveRateLogTarget P d))),
        Real.log_exp]
    _ = Real.log
        (d.currentReserveRate /
          pythonAuxiliaryRateTarget P d referenceRate outputRef) := by
      rw [source_rate_exp_target_eq_python_auxiliary P d
        referenceRate outputRef hpersist hsteady hinflation houtput
        houtputRef hlag href]

/-- The source reserve-quantity row is literally the Python
log(realized/auxiliary quantity target), with quantity innovation,
not a reserve remuneration or reserve requirement shock. -/
theorem source_reserve_quantity_row_eq_python_auxiliary_log_ratio
    (P : Primitives S) (d : LocalPrefixDateData)
    (quantityRef : ℝ)
    (hpersist : P.reserveQuantityPersistence = (1 / 2 : ℝ))
    (hsteady : P.reserveQuantitySteady = quantityRef)
    (hquantity : 0 < d.currentReservesPre)
    (hlag : 0 < d.lagReservesPre)
    (href : 0 < quantityRef) :
    localReducedRemainingResidual P d (7 : Fin 11) =
      Real.log
        (d.currentReservesPre /
          pythonAuxiliaryQuantityTarget d quantityRef) := by
  calc
    localReducedRemainingResidual P d (7 : Fin 11)
        = Real.log d.currentReservesPre -
            sourceReserveQuantityLogTarget P d := by rfl
    _ = Real.log
        (d.currentReservesPre /
          Real.exp (sourceReserveQuantityLogTarget P d)) := by
      rw [Real.log_div (ne_of_gt hquantity)
        (ne_of_gt (Real.exp_pos (sourceReserveQuantityLogTarget P d))),
        Real.log_exp]
    _ = Real.log
        (d.currentReservesPre /
          pythonAuxiliaryQuantityTarget d quantityRef) := by
      rw [source_quantity_exp_target_eq_python_auxiliary P d
        quantityRef hpersist hsteady hlag href]

/-- A zero of the actual Python-shaped log ratio forces the
ORIGINAL source reserve remuneration equation to zero under the
stated restrictions; the converse holds as well. -/
theorem source_rate_row_zero_iff_python_auxiliary_log_ratio_zero
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
      Real.log
        (d.currentReserveRate /
          pythonAuxiliaryRateTarget P d referenceRate outputRef) = 0 := by
  rw [source_reserve_rate_row_eq_python_auxiliary_log_ratio P d
    referenceRate outputRef hpersist hsteady hinflation houtput
    houtputRef hrate hlag href]

/-- Same zero-set transfer for the actual reserve quantity row. -/
theorem source_quantity_row_zero_iff_python_auxiliary_log_ratio_zero
    (P : Primitives S) (d : LocalPrefixDateData)
    (quantityRef : ℝ)
    (hpersist : P.reserveQuantityPersistence = (1 / 2 : ℝ))
    (hsteady : P.reserveQuantitySteady = quantityRef)
    (hquantity : 0 < d.currentReservesPre)
    (hlag : 0 < d.lagReservesPre)
    (href : 0 < quantityRef) :
    localReducedRemainingResidual P d (7 : Fin 11) = 0 ↔
      Real.log
        (d.currentReservesPre /
          pythonAuxiliaryQuantityTarget d quantityRef) = 0 := by
  rw [source_reserve_quantity_row_eq_python_auxiliary_log_ratio P d
    quantityRef hpersist hsteady hquantity hlag href]

#print axioms source_reserve_rate_row_eq_python_auxiliary_log_ratio
#print axioms source_reserve_quantity_row_eq_python_auxiliary_log_ratio
#print axioms source_rate_row_zero_iff_python_auxiliary_log_ratio_zero
#print axioms source_quantity_row_zero_iff_python_auxiliary_log_ratio_zero

end ProposedLocalScalarPythonMonetaryFullRows
end Ventura26LiquidityAllocation
