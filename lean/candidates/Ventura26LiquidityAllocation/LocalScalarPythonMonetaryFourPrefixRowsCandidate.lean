import Ventura26LiquidityAllocation.LocalScalarPythonMonetaryFullRowsCandidate

/-!
# Four literal monetary rows of the date-0/date-1 economic prefix

The generic residual equalities from MonetaryFullRows are applied to
the EXACT two source LocalPrefixDateData records, rather than
silently interpreting an arbitrary Python date datum as the source.
Under positive source coordinates and coefficient restrictions, the
four source prefix rows 12,13,28,29 equal the log(realized/target)
expressions of the Python illustrative auxiliary.

The identities hold for either branch S or B; they do not prove
the concrete Python X,U,continuation vectors match source records
nor close the remaining 30 economic equations or a competitive
equilibrium.
-/

namespace Ventura26LiquidityAllocation
namespace ProposedLocalScalarPythonMonetaryFourPrefixRows

open ProposedLocalScalarPythonMonetaryExpTargets
open ProposedLocalScalarPythonMonetaryFullRows

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- Reserve remuneration at dates zero and one: same original
source rule, but with two DISTINGUISHED date-data records. -/
theorem both_prefix_reserve_rate_rows_eq_python_log_ratios
    (branch : LocalPrefixBranch)
    (P : Primitives S) (I : InheritedState)
    (Z : LocalPrefixCoordinates) (dateOne recurrent : S)
    (tail : LocalPrefixContinuationRule)
    (referenceRate outputRef : ℝ)
    (hpersist : P.reserveRatePersistence = (1 / 2 : ℝ))
    (hsteady : P.reserveRateSteady = referenceRate)
    (hinflation : P.inflationResponse = (3 / 2 : ℝ))
    (houtput : P.outputResponse = (1 / 8 : ℝ))
    (houtputRef : P.outputReference = outputRef)
    (hrate0 : 0 <
      (localPrefixDateZeroData P I Z dateOne).currentReserveRate)
    (hlag0 : 0 <
      (localPrefixDateZeroData P I Z dateOne).lagReserveRate)
    (hrate1 : 0 <
      (localPrefixDateOneData P Z dateOne recurrent tail).currentReserveRate)
    (hlag1 : 0 <
      (localPrefixDateOneData P Z dateOne recurrent tail).lagReserveRate)
    (href : 0 < referenceRate) :
    (localReducedPrefixResidual branch P I Z dateOne recurrent tail
        LocalPrefixEquation.reserveRateRuleZero =
      Real.log
        ((localPrefixDateZeroData P I Z dateOne).currentReserveRate /
          pythonAuxiliaryRateTarget P
            (localPrefixDateZeroData P I Z dateOne)
            referenceRate outputRef)) ∧
    (localReducedPrefixResidual branch P I Z dateOne recurrent tail
        LocalPrefixEquation.reserveRateRuleOne =
      Real.log
        ((localPrefixDateOneData P Z dateOne recurrent tail).currentReserveRate /
          pythonAuxiliaryRateTarget P
            (localPrefixDateOneData P Z dateOne recurrent tail)
            referenceRate outputRef)) := by
  constructor
  · change localReducedRemainingResidual P
      (localPrefixDateZeroData P I Z dateOne) (6 : Fin 11) = _
    exact source_reserve_rate_row_eq_python_auxiliary_log_ratio
      P (localPrefixDateZeroData P I Z dateOne) referenceRate outputRef
      hpersist hsteady hinflation houtput houtputRef hrate0 hlag0 href
  · change localReducedRemainingResidual P
      (localPrefixDateOneData P Z dateOne recurrent tail) (6 : Fin 11) = _
    exact source_reserve_rate_row_eq_python_auxiliary_log_ratio
      P (localPrefixDateOneData P Z dateOne recurrent tail)
      referenceRate outputRef hpersist hsteady hinflation houtput
      houtputRef hrate1 hlag1 href

/-- Reserve quantity at dates zero and one: the quantity-rule
innovation is independent of reserve remuneration and corridor width. -/
theorem both_prefix_reserve_quantity_rows_eq_python_log_ratios
    (branch : LocalPrefixBranch)
    (P : Primitives S) (I : InheritedState)
    (Z : LocalPrefixCoordinates) (dateOne recurrent : S)
    (tail : LocalPrefixContinuationRule)
    (quantityRef : ℝ)
    (hpersist : P.reserveQuantityPersistence = (1 / 2 : ℝ))
    (hsteady : P.reserveQuantitySteady = quantityRef)
    (hquantity0 : 0 <
      (localPrefixDateZeroData P I Z dateOne).currentReservesPre)
    (hlag0 : 0 <
      (localPrefixDateZeroData P I Z dateOne).lagReservesPre)
    (hquantity1 : 0 <
      (localPrefixDateOneData P Z dateOne recurrent tail).currentReservesPre)
    (hlag1 : 0 <
      (localPrefixDateOneData P Z dateOne recurrent tail).lagReservesPre)
    (href : 0 < quantityRef) :
    (localReducedPrefixResidual branch P I Z dateOne recurrent tail
        LocalPrefixEquation.reserveQuantityRuleZero =
      Real.log
        ((localPrefixDateZeroData P I Z dateOne).currentReservesPre /
          pythonAuxiliaryQuantityTarget
            (localPrefixDateZeroData P I Z dateOne) quantityRef)) ∧
    (localReducedPrefixResidual branch P I Z dateOne recurrent tail
        LocalPrefixEquation.reserveQuantityRuleOne =
      Real.log
        ((localPrefixDateOneData P Z dateOne recurrent tail).currentReservesPre /
          pythonAuxiliaryQuantityTarget
            (localPrefixDateOneData P Z dateOne recurrent tail)
            quantityRef)) := by
  constructor
  · change localReducedRemainingResidual P
      (localPrefixDateZeroData P I Z dateOne) (7 : Fin 11) = _
    exact source_reserve_quantity_row_eq_python_auxiliary_log_ratio
      P (localPrefixDateZeroData P I Z dateOne) quantityRef
      hpersist hsteady hquantity0 hlag0 href
  · change localReducedRemainingResidual P
      (localPrefixDateOneData P Z dateOne recurrent tail) (7 : Fin 11) = _
    exact source_reserve_quantity_row_eq_python_auxiliary_log_ratio
      P (localPrefixDateOneData P Z dateOne recurrent tail) quantityRef
      hpersist hsteady hquantity1 hlag1 href

#print axioms both_prefix_reserve_rate_rows_eq_python_log_ratios
#print axioms both_prefix_reserve_quantity_rows_eq_python_log_ratios

end ProposedLocalScalarPythonMonetaryFourPrefixRows
end Ventura26LiquidityAllocation
