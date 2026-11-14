import Ventura26LiquidityAllocation.LocalScalarPythonMonetaryRuleBridgeCandidate

/-!
# Exact source monetary-policy EXP targets vs Python auxiliary()

The actual finite_bridge.py auxiliary computes:
 rr_target = rr_ref * exp(0.5*log(rr_lag/rr_ref)
              +0.5*(1.5*log(pi)+0.125*log(Y/Yref))+e_R)
 M_target = M_ref * exp(0.5*log(M_lag/M_ref)+e_M).

This module proves those targets equal the EXPONENTIAL TARGETS of the
literal source EconomicModel.lean monetary equations when all
coefficients and references are explicitly identified, and nominal
reference and lag variables are strictly positive. It is a theorem
about formulae over generic source economic date data, NOT a witness
that the illustrative Python inputs have been identified with an
actual Primitives S instance or a Banach root.
-/

namespace Ventura26LiquidityAllocation
namespace ProposedLocalScalarPythonMonetaryExpTargets

open ProposedLocalScalarPolicyRuleTargets

variable {S : Type*} [Fintype S] [DecidableEq S]

noncomputable def pythonAuxiliaryRateTarget
    (P : Primitives S) (d : LocalPrefixDateData)
    (referenceRate outputRef : ℝ) : ℝ :=
  referenceRate * Real.exp
    ((1 / 2 : ℝ) * Real.log (d.lagReserveRate / referenceRate) +
      (1 / 2 : ℝ) *
        ((3 / 2 : ℝ) * Real.log d.controls.inflation +
          (1 / 8 : ℝ) *
            Real.log (localPrefixAggregateOutput P d / outputRef)) +
      d.reserveRateInnovation)

noncomputable def pythonAuxiliaryQuantityTarget
    (d : LocalPrefixDateData) (quantityRef : ℝ) : ℝ :=
  quantityRef * Real.exp
    ((1 / 2 : ℝ) * Real.log (d.lagReservesPre / quantityRef) +
      d.reserveQuantityInnovation)

/-- Exact rate target equality, not just zero-set equivalence. -/
theorem source_rate_exp_target_eq_python_auxiliary
    (P : Primitives S) (d : LocalPrefixDateData)
    (referenceRate outputRef : ℝ)
    (hpersist : P.reserveRatePersistence = (1 / 2 : ℝ))
    (hsteady : P.reserveRateSteady = referenceRate)
    (hinflation : P.inflationResponse = (3 / 2 : ℝ))
    (houtput : P.outputResponse = (1 / 8 : ℝ))
    (houtputRef : P.outputReference = outputRef)
    (hlag : 0 < d.lagReserveRate)
    (href : 0 < referenceRate) :
    Real.exp (sourceReserveRateLogTarget P d) =
      pythonAuxiliaryRateTarget P d referenceRate outputRef := by
  have hlog :
      Real.log (d.lagReserveRate / referenceRate) =
        Real.log d.lagReserveRate - Real.log referenceRate :=
    Real.log_div (ne_of_gt hlag) (ne_of_gt href)
  have htarget :
      sourceReserveRateLogTarget P d =
        Real.log referenceRate +
        ((1 / 2 : ℝ) * Real.log (d.lagReserveRate / referenceRate) +
          (1 / 2 : ℝ) *
            ((3 / 2 : ℝ) * Real.log d.controls.inflation +
              (1 / 8 : ℝ) *
                Real.log (localPrefixAggregateOutput P d / outputRef)) +
          d.reserveRateInnovation) := by
    simp only [sourceReserveRateLogTarget, hpersist,
      hsteady, hinflation, houtput, houtputRef]
    rw [hlog]
    ring
  unfold pythonAuxiliaryRateTarget
  rw [htarget, Real.exp_add, Real.exp_log href]

/-- Exact quantity target equality, retaining its OWN balance-sheet
innovation rather than substituting a rate, corridor or encaje shock. -/
theorem source_quantity_exp_target_eq_python_auxiliary
    (P : Primitives S) (d : LocalPrefixDateData)
    (quantityRef : ℝ)
    (hpersist : P.reserveQuantityPersistence = (1 / 2 : ℝ))
    (hsteady : P.reserveQuantitySteady = quantityRef)
    (hlag : 0 < d.lagReservesPre)
    (href : 0 < quantityRef) :
    Real.exp (sourceReserveQuantityLogTarget P d) =
      pythonAuxiliaryQuantityTarget d quantityRef := by
  have hlog :
      Real.log (d.lagReservesPre / quantityRef) =
        Real.log d.lagReservesPre - Real.log quantityRef :=
    Real.log_div (ne_of_gt hlag) (ne_of_gt href)
  have htarget :
      sourceReserveQuantityLogTarget P d =
        Real.log quantityRef +
          ((1 / 2 : ℝ) * Real.log (d.lagReservesPre / quantityRef) +
            d.reserveQuantityInnovation) := by
    simp only [sourceReserveQuantityLogTarget, hpersist, hsteady]
    rw [hlog]
    ring
  unfold pythonAuxiliaryQuantityTarget
  rw [htarget, Real.exp_add, Real.exp_log href]

/-- An exact zero of the ORIGINAL source rate rule therefore
corresponds to equality with the Python target under the stated
parameter and positivity premises. -/
theorem source_rate_zero_iff_python_auxiliary_target
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
      d.currentReserveRate =
        pythonAuxiliaryRateTarget P d referenceRate outputRef := by
  rw [source_reserve_rate_rule_zero_iff_exp_target P d hrate,
    source_rate_exp_target_eq_python_auxiliary P d referenceRate outputRef
      hpersist hsteady hinflation houtput houtputRef hlag href]

/-- Analogous exact zero-set bridge for the source quantity rule. -/
theorem source_quantity_zero_iff_python_auxiliary_target
    (P : Primitives S) (d : LocalPrefixDateData)
    (quantityRef : ℝ)
    (hpersist : P.reserveQuantityPersistence = (1 / 2 : ℝ))
    (hsteady : P.reserveQuantitySteady = quantityRef)
    (hquantity : 0 < d.currentReservesPre)
    (hlag : 0 < d.lagReservesPre)
    (href : 0 < quantityRef) :
    localReducedRemainingResidual P d (7 : Fin 11) = 0 ↔
      d.currentReservesPre = pythonAuxiliaryQuantityTarget d quantityRef := by
  rw [source_reserve_quantity_rule_zero_iff_exp_target P d hquantity,
    source_quantity_exp_target_eq_python_auxiliary P d quantityRef
      hpersist hsteady hlag href]

#print axioms source_rate_exp_target_eq_python_auxiliary
#print axioms source_quantity_exp_target_eq_python_auxiliary
#print axioms source_rate_zero_iff_python_auxiliary_target
#print axioms source_quantity_zero_iff_python_auxiliary_target

end ProposedLocalScalarPythonMonetaryExpTargets
end Ventura26LiquidityAllocation
