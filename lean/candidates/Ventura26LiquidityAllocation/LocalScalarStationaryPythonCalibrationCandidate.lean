import Ventura26LiquidityAllocation.StationaryPrimitivesCandidate
import Ventura26LiquidityAllocation.LocalScalarAugmented34MonetaryRowsCandidate
import Ventura26LiquidityAllocation.LocalScalarAugmented34BankFaceRowsCandidate

/-!
# Exact scalar calibration interface: stationary Lean source and Python-style steady formulas

The illustrative producer (verified_linear_operator.py:steady) forms
  v  = 1/(1+sqrt(3/2))
  cm = Delta*(1-aa+aa*v)
  cp = Delta*tight*aa*v
  mean = (cm+cp)/2
  gap = cm-cp
  AR = RD - (1-rho)*mean - rho*zeta*gap/2
  RR = (AR + sqrt(AR^2+2*RD*zeta*gap))/2
  RL = RR + mean
and sets its bank renewal coefficient to aB = 1/RL.
Its illustration uses Delta=1/50, aa=1/2, tight=1/2,
rho=1/10, zeta=1/5 and RD=100/99.

The *literal stationary Lean candidate* defines exactly the same
closed-form scalar rate and sets bankExit=1/10 and bankSeedShare=10/RL-9.
This module verifies the scalar mathematical identities over real
numbers, NOT a new floating-point or interval numerical enclosure,
Python execution semantics, equality of complete 34-row operators,
or an equilibrium following a policy shock.
-/

namespace Ventura26LiquidityAllocation
namespace ProposedLocalScalarStationaryPythonCalibration

open ProposedStationaryPrimitives
open ProposedStationaryReducedSystem
open ProposedStationaryRealScale
open ProposedLocalScalarAugmented34MonetaryRows
open ProposedLocalScalarAugmented34BankFaceRows
open ProposedLocalScalarBankRenewalCalibrationBridge

/-- Python's two OTC slopes, evaluated with its illustrative constants. -/
noncomputable def illustrativeDeficitSlope : ℝ :=
  (1 / 50 : ℝ) *
    (1 - (1 / 2 : ℝ) + (1 / 2 : ℝ) * ProposedStationaryBank.weight)

noncomputable def illustrativeSurplusSlope : ℝ :=
  (1 / 50 : ℝ) * (1 / 2 : ℝ) * (1 / 2 : ℝ) *
    ProposedStationaryBank.weight

noncomputable def illustrativeMeanSlope : ℝ :=
  (illustrativeDeficitSlope + illustrativeSurplusSlope) / 2

noncomputable def illustrativeSlopeGap : ℝ :=
  illustrativeDeficitSlope - illustrativeSurplusSlope

/-- Equality of the Python-style average OTC slope with the exact
stationary source slope; no decimal rounding is introduced. -/
theorem illustrative_mean_slope_eq_source :
    illustrativeMeanSlope = ProposedStationaryBank.meanSlope := by
  unfold illustrativeMeanSlope illustrativeDeficitSlope
    illustrativeSurplusSlope ProposedStationaryBank.meanSlope
  ring

theorem illustrative_slope_gap_eq_source :
    illustrativeSlopeGap = ProposedStationaryBank.slopeGap := by
  unfold illustrativeSlopeGap illustrativeDeficitSlope
    illustrativeSurplusSlope ProposedStationaryBank.slopeGap
  ring

noncomputable def illustrativeRootCoefficient : ℝ :=
  ProposedStationaryBank.depositRate -
    (1 - (1 / 10 : ℝ)) * illustrativeMeanSlope -
    (1 / 10 : ℝ) * (1 / 5 : ℝ) * illustrativeSlopeGap / 2

theorem illustrative_root_coefficient_eq_source :
    illustrativeRootCoefficient = ProposedStationaryBank.rootCoefficient := by
  unfold illustrativeRootCoefficient ProposedStationaryBank.rootCoefficient
  rw [illustrative_mean_slope_eq_source, illustrative_slope_gap_eq_source]
  ring

/-- Closed form used by the Python illustrative central-bank calculation,
with exactly the listed rational parameters and source matching weight. -/
noncomputable def illustrativeReserveRate : ℝ :=
  (illustrativeRootCoefficient +
    Real.sqrt
      (illustrativeRootCoefficient ^ 2 +
        2 * ProposedStationaryBank.depositRate *
          (1 / 5 : ℝ) * illustrativeSlopeGap)) / 2

theorem illustrative_reserve_rate_eq_source :
    illustrativeReserveRate = ProposedStationaryBank.reserveRate := by
  unfold illustrativeReserveRate ProposedStationaryBank.reserveRate
  rw [illustrative_root_coefficient_eq_source,
    illustrative_slope_gap_eq_source]
  congr 1
  congr 1
  ring

noncomputable def illustrativeLoanRate : ℝ :=
  illustrativeReserveRate + illustrativeMeanSlope

theorem illustrative_loan_rate_eq_source :
    illustrativeLoanRate = ProposedStationaryBank.loanRate := by
  unfold illustrativeLoanRate ProposedStationaryBank.loanRate
  rw [illustrative_reserve_rate_eq_source, illustrative_mean_slope_eq_source]

/-- The explicit stationary source *instantiates*, rather than
postulates, every coefficient condition needed by the augmented
remuneration-policy row bridge. -/
theorem stationary_source_rate_calibration (G : ℝ) :
    RateCalibration (primitives G)
      ProposedStationaryBank.reserveRate aggregateOutput := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem stationary_source_quantity_calibration (G : ℝ) :
    QuantityCalibration (primitives G) reservesPre := by
  exact ⟨rfl, rfl⟩

/-- No free bank calibration premise is needed at the stationary
source: the exact seed share was chosen from the loan-rate identity. -/
theorem stationary_source_bank_renewal_compatibility (G : ℝ) :
    (primitives G).bankExit * (1 - (primitives G).bankSeedShare) =
      1 - 1 / illustrativeLoanRate := by
  rw [illustrative_loan_rate_eq_source]
  exact (bankRenewalFactor_eq_inverse_rate_iff
    (primitives G) ProposedStationaryBank.loanRate).mp
      (bankRenewalFactor_eq (primitives G) (stationary_parameters G))

/-- The algebraic bank coefficient of the stationary Lean model is
identical to the Python-style inverse loan rate. This statement is
about exact real scalar expressions, not a machine-checked AD box. -/
theorem stationary_source_bank_factor_eq_illustrative (G : ℝ) :
    bankRenewalFactor (primitives G) = 1 / illustrativeLoanRate := by
  rw [illustrative_loan_rate_eq_source]
  exact bankRenewalFactor_eq (primitives G) (stationary_parameters G)

/-- Exact unit-CRRA entrepreneurship; positive consumption remains
a separate state-domain requirement away from the steady state. -/
theorem stationary_source_entrepreneur_sigma_one (G : ℝ) :
    (primitives G).entrepreneurRiskAversion = 1 := rfl

/-- Reference reserve remuneration, stock of prepayment reserves and
aggregate output are positive for the stationary source instance. -/
theorem stationary_source_reference_positive (G : ℝ) :
    0 < (primitives G).reserveRateSteady ∧
    0 < (primitives G).reserveQuantitySteady ∧
    0 < (primitives G).outputReference := by
  exact monetary_references_pos (primitives G) (stationary_parameters G)

#print axioms illustrative_mean_slope_eq_source
#print axioms illustrative_slope_gap_eq_source
#print axioms illustrative_root_coefficient_eq_source
#print axioms illustrative_reserve_rate_eq_source
#print axioms illustrative_loan_rate_eq_source
#print axioms stationary_source_rate_calibration
#print axioms stationary_source_quantity_calibration
#print axioms stationary_source_bank_renewal_compatibility
#print axioms stationary_source_bank_factor_eq_illustrative
#print axioms stationary_source_entrepreneur_sigma_one
#print axioms stationary_source_reference_positive

end ProposedLocalScalarStationaryPythonCalibration
end Ventura26LiquidityAllocation
