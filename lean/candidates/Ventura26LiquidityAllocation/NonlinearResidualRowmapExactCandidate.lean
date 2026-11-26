import Ventura26LiquidityAllocation.StationaryFiscalPrimitivesScopeCandidate

/-!
# Exact nonlinear scalar and pledge/Euler residual-coordinate transformations

These are the exact real-algebraic building blocks of the Python
SOURCE-shaped row-map candidate. They do NOT identify its transcriptions
with original SOURCE equations. No inverse of an economic Jacobian is
asserted or constructed.

The denominator must be nonzero for the forward-to-log map; the domain
of the inverse log-to-level map must additionally be strictly positive.
-/

namespace Ventura26LiquidityAllocation

noncomputable def scalarLevelResidual (d p : ℝ) : ℝ :=
  d * (Real.exp p - 1)

noncomputable def scalarLogResidual (d s : ℝ) : ℝ :=
  Real.log (1 + s / d)

/-- Exact roundtrip from a log residual into its level residual and back. -/
theorem scalarLogLevel_roundtrip (d p : ℝ) (hd : d ≠ 0) :
    scalarLogResidual d (scalarLevelResidual d p) = p := by
  unfold scalarLogResidual scalarLevelResidual
  have h : 1 + d * (Real.exp p - 1) / d = Real.exp p := by
    field_simp [hd]
    ring
  rw [h, Real.log_exp]

#print axioms scalarLogLevel_roundtrip

/-- The reverse roundtrip requires the logarithm to be evaluated at a
strictly positive argument. -/
theorem scalarLevelLog_roundtrip (d s : ℝ)
    (hd : d ≠ 0) (hp : 0 < 1 + s / d) :
    scalarLevelResidual d (scalarLogResidual d s) = s := by
  unfold scalarLevelResidual scalarLogResidual
  rw [Real.exp_log hp]
  field_simp [hd]
  ring

#print axioms scalarLevelLog_roundtrip

/-- The signed level residual is the negative of the usual difference,
as in the worker Euler rows with SOURCE 1-r and Python log r. -/
noncomputable def negativeScalarLevelResidual (d p : ℝ) : ℝ :=
  -(d * (Real.exp p - 1))

noncomputable def negativeScalarLogResidual (d s : ℝ) : ℝ :=
  Real.log (1 - s / d)

theorem negativeScalarLogLevel_roundtrip (d p : ℝ) (hd : d ≠ 0) :
    negativeScalarLogResidual d (negativeScalarLevelResidual d p) = p := by
  unfold negativeScalarLogResidual negativeScalarLevelResidual
  have h : 1 - -(d * (Real.exp p - 1)) / d = Real.exp p := by
    field_simp [hd]
    ring
  rw [h, Real.log_exp]

#print axioms negativeScalarLogLevel_roundtrip

/-- The positive-domain condition matters: no global real-log inverse
has been claimed for arbitrary signed level residuals. -/
theorem negativeScalarLevelLog_roundtrip (d s : ℝ)
    (hd : d ≠ 0) (hp : 0 < 1 - s / d) :
    negativeScalarLevelResidual d (negativeScalarLogResidual d s) = s := by
  unfold negativeScalarLevelResidual negativeScalarLogResidual
  rw [Real.exp_log hp]
  field_simp [hd]
  ring

#print axioms negativeScalarLevelLog_roundtrip

/-- A state-dependent coefficient is held fixed *within a fiber at z*:
the firm Euler SOURCE-shaped residual differs from Python's by a
multiple of the common pledge discrepancy. -/
noncomputable def pledgeEulerShearForward (a e pledgeLog : ℝ) : ℝ :=
  e + a * (Real.exp pledgeLog - 1)

noncomputable def pledgeEulerShearBackward
    (a eSource pledgeLog : ℝ) : ℝ :=
  eSource - a * (Real.exp pledgeLog - 1)

/-- Exact inverse of a single Euler shear at an arbitrary residual
and arbitrary real shear coefficient. -/
theorem pledgeEulerShear_roundtrip (a e pledgeLog : ℝ) :
    pledgeEulerShearBackward a (pledgeEulerShearForward a e pledgeLog)
      pledgeLog = e := by
  unfold pledgeEulerShearBackward pledgeEulerShearForward
  ring

#print axioms pledgeEulerShear_roundtrip

theorem pledgeEulerShear_reverse_roundtrip (a eSource pledgeLog : ℝ) :
    pledgeEulerShearForward a
      (pledgeEulerShearBackward a eSource pledgeLog)
      pledgeLog = eSource := by
  unfold pledgeEulerShearBackward pledgeEulerShearForward
  ring

#print axioms pledgeEulerShear_reverse_roundtrip

end Ventura26LiquidityAllocation
