import Ventura26LiquidityAllocation.SourceSixNonlinearLogRowRootTransportCandidate
import Ventura26LiquidityAllocation.SourcePython33RowIndexPermutationCandidate

/-!
# Nonlinear SOURCE normalization followed by exact 33-row Python index order

The original SOURCE and Python 33-equation residual lists have a
PROVED six-index permutation. In addition, six SOURCE level/Euler
rows require NONLINEAR log normalization on the positive chart.

This module composes those TWO exact SOURCE-SIDE operations:
  SOURCE residual v
    -> six-row nonlinear log normalize(v)
    -> reorder to the ORIGINAL Python 33-row index order.

The resulting 33-vector has exactly the same ZERO SET as v on the
strictly positive logarithmic domain. It also specializes to the
ACTUAL stationary pinned reduced33 SOURCE map (32 economic logs + h).

Crucially, "in Python order" means only the index convention:
it does NOT assert equal VALUES to the floating-point original
Python prefix_residual, identify all 33 rows with Python's formulas,
prove a SOURCE root, certify its derivative or full equilibrium.
-/

namespace Ventura26LiquidityAllocation

/-- Permuting arbitrary SOURCE residuals into the original Python
equation-index order does not change whether ALL 33 rows vanish. -/
theorem sourcePythonOrder33_zero_iff (v : Fin 33 → ℝ) :
    sourceRowsInPython33Order v = 0 ↔ v = 0 := by
  constructor
  · intro hv
    funext i
    have hrow := congrFun hv (sourceToPython33Index i)
    simpa [sourceRowsInPython33Order,
      pythonToSource33_sourceToPython33] using hrow
  · intro hv
    rw [hv]
    rfl

#print axioms sourcePythonOrder33_zero_iff

/-- SOURCE real rows in the true original Python index ordering,
after exact six-row nonlinear positive-domain normalization. -/
noncomputable def sourceNonlinearPythonOrder33
    (bank0 labor0 bank1 labor1 : ℝ)
    (v : Fin 33 → ℝ) : Fin 33 → ℝ :=
  sourceRowsInPython33Order
    (sourceSixNonlinearLogRowNormalize
      bank0 labor0 bank1 labor1 v)

/-- The composed transformation is root-set preserving at EVERY
admissible real SOURCE economic point. No root existence is claimed. -/
theorem sourceNonlinearPythonOrder33_zero_iff
    (bank0 labor0 bank1 labor1 : ℝ) (v : Fin 33 → ℝ)
    (hd : SourceSixNonlinearLogDomain
      bank0 labor0 bank1 labor1 v) :
    sourceNonlinearPythonOrder33 bank0 labor0 bank1 labor1 v = 0 ↔
      v = 0 := by
  change
    sourceRowsInPython33Order
      (sourceSixNonlinearLogRowNormalize bank0 labor0 bank1 labor1 v) = 0 ↔
    v = 0
  exact (sourcePythonOrder33_zero_iff _).trans
    (sourceSixNonlinearLogRow_vector_zero_iff
      bank0 labor0 bank1 labor1 v hd)

#print axioms sourceNonlinearPythonOrder33_zero_iff

/-- Exact root-set correspondence on the SAME concrete original
SOURCE reduced33 operator, with the positive domain hypotheses
explicit. No equality to external Python economic functions is used. -/
theorem fullyPinnedSOURCE33_pythonOrderNormalized_zero_iff
    (G : ℝ) (w : (Fin 32 → ℝ) × ℝ)
    (bank0 labor0 bank1 labor1 : ℝ)
    (hd : SourceSixNonlinearLogDomain
      bank0 labor0 bank1 labor1
      (fullyPinnedStationaryP0SOURCE33 G w)) :
    sourceNonlinearPythonOrder33 bank0 labor0 bank1 labor1
      (fullyPinnedStationaryP0SOURCE33 G w) = 0 ↔
    fullyPinnedStationaryP0SOURCE33 G w = 0 := by
  exact sourceNonlinearPythonOrder33_zero_iff
    bank0 labor0 bank1 labor1
    (fullyPinnedStationaryP0SOURCE33 G w) hd

#print axioms fullyPinnedSOURCE33_pythonOrderNormalized_zero_iff

end Ventura26LiquidityAllocation
