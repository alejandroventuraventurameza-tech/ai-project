import Ventura26LiquidityAllocation.LocalScalarBankFaceLogZeroCandidate

/-!
# Worker labor supply: positive log vs original level residual

EconomicModel.lean writes the labor condition as wage minus a nonlinear
marginal disutility target. The illustrative finite Python solver uses
the logarithm of the ratio wage/target. This module proves the zeros
coincide on the positive economic domain, with all exponents initially
retained exactly as they are in the source.

The additional sigmaW=1 and laborCurvature=1 specialization matches the
illustrative Python parameterization only if those primitive values and
all coordinate data are independently identified. The Jacobians differ.
-/

namespace Ventura26LiquidityAllocation
namespace ProposedLocalScalarWorkerLaborLogZero

open ProposedLocalScalarBankFaceLogZero

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- Exact nonlinear worker labor target in source economic coordinates. -/
noncomputable def sourceWorkerLaborTarget
    (P : Primitives S) (d : LocalPrefixDateData) : ℝ :=
  P.laborScale *
    d.controls.workerConsumption ^ P.workerRiskAversion *
    localPrefixAggregateLabor P d ^ P.laborCurvature

/-- Date-zero worker labor row is a residual in levels. -/
theorem source_worker_labor_is_level_residual
    (P : Primitives S) (d : LocalPrefixDateData) :
    localReducedRemainingResidual P d (3 : Fin 11) =
      d.controls.wage - sourceWorkerLaborTarget P d := by
  rfl

/-- The log labor condition and the original source level row have
the same zeros under strict positivity of wage and target.
The derivative of a log residual is not the derivative of the
level equation even on their common zero set. -/
theorem source_worker_labor_log_zero_iff
    (P : Primitives S) (d : LocalPrefixDateData)
    (hwage : 0 < d.controls.wage)
    (htarget : 0 < sourceWorkerLaborTarget P d) :
    Real.log (d.controls.wage / sourceWorkerLaborTarget P d) = 0 ↔
      localReducedRemainingResidual P d (3 : Fin 11) = 0 := by
  rw [source_worker_labor_is_level_residual]
  exact log_ratio_zero_iff_level_zero _ _ hwage htarget

/-- Under the illustrative worker curvature and labor curvature,
the source target reduces algebraically to laborScale * CW * L. -/
theorem source_worker_labor_target_unit_curvatures
    (P : Primitives S) (d : LocalPrefixDateData)
    (hsigma : P.workerRiskAversion = 1)
    (hphi : P.laborCurvature = 1) :
    sourceWorkerLaborTarget P d =
      P.laborScale * d.controls.workerConsumption *
        localPrefixAggregateLabor P d := by
  simp [sourceWorkerLaborTarget, hsigma, hphi]

/-- Positive wage, labor, worker consumption and scale suffice to
make the log labor residual well defined at unit curvatures. -/
theorem source_worker_labor_target_pos_unit_curvatures
    (P : Primitives S) (d : LocalPrefixDateData)
    (hsigma : P.workerRiskAversion = 1)
    (hphi : P.laborCurvature = 1)
    (hscale : 0 < P.laborScale)
    (hcw : 0 < d.controls.workerConsumption)
    (hlabor : 0 < localPrefixAggregateLabor P d) :
    0 < sourceWorkerLaborTarget P d := by
  rw [source_worker_labor_target_unit_curvatures P d hsigma hphi]
  exact mul_pos (mul_pos hscale hcw) hlabor

/-- The exact source row has the zero set of the Python-style
log wage/(chi*CW*L), provided chi is identified with P.laborScale
and the explicit source conditions hold. No numerical Jacobian
identification is inferred. -/
theorem source_worker_labor_python_style_log_zero_iff
    (P : Primitives S) (d : LocalPrefixDateData)
    (hsigma : P.workerRiskAversion = 1)
    (hphi : P.laborCurvature = 1)
    (hscale : 0 < P.laborScale)
    (hcw : 0 < d.controls.workerConsumption)
    (hlabor : 0 < localPrefixAggregateLabor P d)
    (hwage : 0 < d.controls.wage) :
    Real.log (d.controls.wage /
      (P.laborScale * d.controls.workerConsumption *
        localPrefixAggregateLabor P d)) = 0 ↔
      localReducedRemainingResidual P d (3 : Fin 11) = 0 := by
  have htarget := source_worker_labor_target_pos_unit_curvatures
    P d hsigma hphi hscale hcw hlabor
  have hiff := source_worker_labor_log_zero_iff P d hwage htarget
  rw [source_worker_labor_target_unit_curvatures P d hsigma hphi] at hiff
  exact hiff

#print axioms source_worker_labor_is_level_residual
#print axioms source_worker_labor_log_zero_iff
#print axioms source_worker_labor_target_unit_curvatures
#print axioms source_worker_labor_target_pos_unit_curvatures
#print axioms source_worker_labor_python_style_log_zero_iff

end ProposedLocalScalarWorkerLaborLogZero
end Ventura26LiquidityAllocation
