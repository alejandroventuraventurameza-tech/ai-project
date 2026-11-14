import Ventura26LiquidityAllocation.LocalScalarEconomicSliceCandidate

/-!
# Exact zero sets of the central-bank reserve-rate and quantity rules

The finite source writes policy rules in log residuals, while the
illustrative Python evaluator writes log realized/target ratios.
On the strictly positive economic domain the ORIGINAL source
equations are zero exactly at the prescribed positive exponential
targets. This establishes the exact source rule (dates zero and one
through generic LocalPrefixDateData), NOT the equality of its
targets with those constructed by Python's auxiliary(...).

Reserve remuneration and reserve quantity are separate primitive
innovations, and neither is identified with a corridor shock.
-/

namespace Ventura26LiquidityAllocation
namespace ProposedLocalScalarPolicyRuleTargets

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- Log target for the source's gross reserve remuneration rate. -/
noncomputable def sourceReserveRateLogTarget
    (P : Primitives S) (d : LocalPrefixDateData) : ℝ :=
  P.reserveRatePersistence * Real.log d.lagReserveRate +
    (1 - P.reserveRatePersistence) *
      (Real.log P.reserveRateSteady +
        P.inflationResponse * Real.log d.controls.inflation +
        P.outputResponse *
          Real.log (localPrefixAggregateOutput P d / P.outputReference)) +
    d.reserveRateInnovation

/-- Log target for the source's nominal prepayment reserve quantity. -/
noncomputable def sourceReserveQuantityLogTarget
    (P : Primitives S) (d : LocalPrefixDateData) : ℝ :=
  P.reserveQuantityPersistence * Real.log d.lagReservesPre +
    (1 - P.reserveQuantityPersistence) *
      Real.log P.reserveQuantitySteady +
    d.reserveQuantityInnovation

/-- At strictly positive realized remuneration, the original
policy-rate row is exactly its exponential Taylor-like rule. -/
theorem source_reserve_rate_rule_zero_iff_exp_target
    (P : Primitives S) (d : LocalPrefixDateData)
    (hrate : 0 < d.currentReserveRate) :
    localReducedRemainingResidual P d (6 : Fin 11) = 0 ↔
      d.currentReserveRate = Real.exp (sourceReserveRateLogTarget P d) := by
  change Real.log d.currentReserveRate -
    sourceReserveRateLogTarget P d = 0 ↔
      d.currentReserveRate = Real.exp (sourceReserveRateLogTarget P d)
  constructor
  · intro hzero
    have hlog : Real.log d.currentReserveRate =
        sourceReserveRateLogTarget P d := sub_eq_zero.mp hzero
    calc
      d.currentReserveRate = Real.exp (Real.log d.currentReserveRate) :=
        (Real.exp_log hrate).symm
      _ = Real.exp (sourceReserveRateLogTarget P d) := by rw [hlog]
  · intro htarget
    have hlog : Real.log d.currentReserveRate =
        sourceReserveRateLogTarget P d := by
      rw [htarget, Real.log_exp]
    exact sub_eq_zero.mpr hlog

/-- At strictly positive prepayment reserves, the original
policy-quantity row is exactly its exponential balance-sheet rule.
This does NOT conflate reserve requirements and reserve quantity. -/
theorem source_reserve_quantity_rule_zero_iff_exp_target
    (P : Primitives S) (d : LocalPrefixDateData)
    (hquantity : 0 < d.currentReservesPre) :
    localReducedRemainingResidual P d (7 : Fin 11) = 0 ↔
      d.currentReservesPre =
        Real.exp (sourceReserveQuantityLogTarget P d) := by
  change Real.log d.currentReservesPre -
    sourceReserveQuantityLogTarget P d = 0 ↔
      d.currentReservesPre = Real.exp (sourceReserveQuantityLogTarget P d)
  constructor
  · intro hzero
    have hlog : Real.log d.currentReservesPre =
        sourceReserveQuantityLogTarget P d := sub_eq_zero.mp hzero
    calc
      d.currentReservesPre = Real.exp (Real.log d.currentReservesPre) :=
        (Real.exp_log hquantity).symm
      _ = Real.exp (sourceReserveQuantityLogTarget P d) := by rw [hlog]
  · intro htarget
    have hlog : Real.log d.currentReservesPre =
        sourceReserveQuantityLogTarget P d := by
      rw [htarget, Real.log_exp]
    exact sub_eq_zero.mpr hlog

#print axioms source_reserve_rate_rule_zero_iff_exp_target
#print axioms source_reserve_quantity_rule_zero_iff_exp_target

end ProposedLocalScalarPolicyRuleTargets
end Ventura26LiquidityAllocation
