import Ventura26LiquidityAllocation.LocalScalarDualSigmaOneBridgeCandidate
import Ventura26LiquidityAllocation.LocalScalarBankFaceLogZeroCandidate

/-!
# Household Euler: log-to-level zero equivalence in source coordinates

The illustrative Python evaluator writes the household deposit Euler
condition as a logarithm of the gross intertemporal pricing ratio,
whereas EconomicModel.lean uses 1 minus the same ratio in levels.

This module proves equality of their zero sets, NOT equality of their
Jacobians, with explicit assumptions for the unit-CRRA illustration.
The two source coordinate values and model parameters must still be
identified independently with the Python producer's data.
-/

namespace Ventura26LiquidityAllocation
namespace ProposedLocalScalarWorkerEulerLogZero

open ProposedLocalScalarDualSigmaOneBridge
open ProposedLocalScalarBankFaceLogZero

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- The exact source household gross deposit-Euler expression. -/
noncomputable def sourceWorkerEulerGross
    (P : Primitives S) (d : LocalPrefixDateData) : ℝ :=
  (P.workerDiscount *
      crraMarginal P.workerRiskAversion d.nextControls.workerConsumption /
      crraMarginal P.workerRiskAversion d.controls.workerConsumption) *
    d.controls.depositRate / d.nextControls.inflation

/-- Lean's fourth 'remaining' equation is precisely 1 minus the
source worker intertemporal valuation multiplied by the gross
deposit rate divided by next-period inflation. -/
theorem source_worker_euler_is_one_sub_gross
    (P : Primitives S) (d : LocalPrefixDateData) :
    localReducedRemainingResidual P d (4 : Fin 11) =
      1 - sourceWorkerEulerGross P d := by
  rfl

/-- For a strictly positive gross valuation, the log and level
Euler equations have identical zero sets, but not derivatives. -/
theorem source_worker_euler_log_zero_iff
    (P : Primitives S) (d : LocalPrefixDateData)
    (hpos : 0 < sourceWorkerEulerGross P d) :
    Real.log (sourceWorkerEulerGross P d) = 0 ↔
      localReducedRemainingResidual P d (4 : Fin 11) = 0 := by
  rw [source_worker_euler_is_one_sub_gross]
  constructor
  · intro hlog
    have hone : sourceWorkerEulerGross P d = 1 :=
      Real.eq_one_of_pos_of_log_eq_zero hpos hlog
    simp [hone]
  · intro hrow
    have hone : sourceWorkerEulerGross P d = 1 := by
      linarith
    simp [hone]

/-- Under sigmaW=1 and positive source consumptions, the source
ratio of worker marginal utilities is exactly CW0/CW1. -/
theorem source_worker_gross_sigma_one
    (P : Primitives S) (d : LocalPrefixDateData)
    (hsigma : P.workerRiskAversion = 1)
    (hc0 : 0 < d.controls.workerConsumption)
    (hc1 : 0 < d.nextControls.workerConsumption) :
    sourceWorkerEulerGross P d =
      (P.workerDiscount *
        (d.controls.workerConsumption / d.nextControls.workerConsumption)) *
        d.controls.depositRate / d.nextControls.inflation := by
  unfold sourceWorkerEulerGross
  rw [hsigma]
  rw [mul_div_assoc, source_crra_ratio_sigma_one _ _ hc0 hc1]

/-- Economic positivity assumptions provide the strictly positive
gross valuation required by the logarithmic expression. -/
theorem source_worker_gross_pos_sigma_one
    (P : Primitives S) (d : LocalPrefixDateData)
    (hsigma : P.workerRiskAversion = 1)
    (hc0 : 0 < d.controls.workerConsumption)
    (hc1 : 0 < d.nextControls.workerConsumption)
    (hbeta : 0 < P.workerDiscount)
    (hdeposit : 0 < d.controls.depositRate)
    (hinfl : 0 < d.nextControls.inflation) :
    0 < sourceWorkerEulerGross P d := by
  rw [source_worker_gross_sigma_one P d hsigma hc0 hc1]
  exact div_pos (mul_pos (mul_pos hbeta (div_pos hc0 hc1)) hdeposit) hinfl

/-- The literal source row has the zero set of the Python-style
log Euler equation when all stated economic restrictions hold.
This is an equality of ZERO SETS for identified source coordinates,
not yet a proof of identity with the stored Python input values. -/
theorem source_worker_euler_python_style_log_zero_iff
    (P : Primitives S) (d : LocalPrefixDateData)
    (hsigma : P.workerRiskAversion = 1)
    (hc0 : 0 < d.controls.workerConsumption)
    (hc1 : 0 < d.nextControls.workerConsumption)
    (hbeta : 0 < P.workerDiscount)
    (hdeposit : 0 < d.controls.depositRate)
    (hinfl : 0 < d.nextControls.inflation) :
    Real.log
      ((P.workerDiscount *
          (d.controls.workerConsumption / d.nextControls.workerConsumption)) *
        d.controls.depositRate / d.nextControls.inflation) = 0 ↔
      localReducedRemainingResidual P d (4 : Fin 11) = 0 := by
  have hpos := source_worker_gross_pos_sigma_one
    P d hsigma hc0 hc1 hbeta hdeposit hinfl
  have hzero := source_worker_euler_log_zero_iff P d hpos
  rw [source_worker_gross_sigma_one P d hsigma hc0 hc1] at hzero
  exact hzero

#print axioms source_worker_euler_is_one_sub_gross
#print axioms source_worker_euler_log_zero_iff
#print axioms source_worker_gross_sigma_one
#print axioms source_worker_gross_pos_sigma_one
#print axioms source_worker_euler_python_style_log_zero_iff

end ProposedLocalScalarWorkerEulerLogZero
end Ventura26LiquidityAllocation
