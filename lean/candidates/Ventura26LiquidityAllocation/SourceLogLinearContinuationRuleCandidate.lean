import Ventura26LiquidityAllocation.EconomicModel

/-!
# Exact finite-dimensional log-linear continuation, in SOURCE economic types

The frozen Python prefix uses the LAST TEN rows of a 16x6 P0 matrix
to compute date-two controls from the six date-two state log deviations.
The FIRST SIX rows of its 16x6 P0 file are identity and correspond to
the six state coordinates, not to an additional SOURCE policy shock.

Here we give a completely explicit SOURCE-typed continuation rule for
an ARBITRARY 10x6 real matrix C, baseline state x0 and baseline
positive controls u0. We prove its baseline and its exact logarithmic
response. Instantiating C with the separately pinned 60-digit decimal
P0 coefficients, relating SOURCE primitives to Python calibration,
and showing this finite tail is an actual infinite-horizon equilibrium
continuation are separate UNPROVED obligations.

This does NOT assert C is an equilibrium policy matrix P_*.
-/

namespace Ventura26LiquidityAllocation

open scoped BigOperators

/-- An arbitrary 10-by-6 log-control response matrix. -/
abbrev SourceFiniteTailMatrix := Fin 10 → Fin 6 → ℝ

/-- Log-linear control response around an arbitrary positive reference
u0, expressed in the literal ten economic control coordinates. -/
noncomputable def sourceFiniteTailControlVector
    (u0 : LocalPrefixControlsTen) (C : SourceFiniteTailMatrix)
    (z : Fin 6 → ℝ) : Fin 10 → ℝ :=
  fun j => localPrefixControlsTenVector u0 j *
    Real.exp (∑ k : Fin 6, C j k * z k)

/-- The source type LocalPrefixControlsTen is reconstructed explicitly
from all ten vector components, keeping the semantic order intact. -/
noncomputable def sourceFiniteTailControls
    (u0 : LocalPrefixControlsTen) (C : SourceFiniteTailMatrix)
    (z : Fin 6 → ℝ) : LocalPrefixControlsTen :=
  let v := sourceFiniteTailControlVector u0 C z
  { consumptionH := v 0
    consumptionL := v 1
    workerConsumption := v 2
    wage := v 3
    inputPrice := v 4
    inflation := v 5
    capitalPrice := v 6
    depositRate := v 7
    loanRate := v 8
    tightness := v 9 }

/-- Every true SOURCE control coordinate agrees with the intended
log-linear 10-vector expression. -/
theorem sourceFiniteTailControls_vector_eq
    (u0 : LocalPrefixControlsTen) (C : SourceFiniteTailMatrix)
    (z : Fin 6 → ℝ) (j : Fin 10) :
    localPrefixControlsTenVector (sourceFiniteTailControls u0 C z) j =
      sourceFiniteTailControlVector u0 C z j := by
  fin_cases j <;> rfl

#print axioms sourceFiniteTailControls_vector_eq

/-- Zero log-state deviations return the reference ten controls. -/
theorem sourceFiniteTailControls_zero
    (u0 : LocalPrefixControlsTen) (C : SourceFiniteTailMatrix) :
    sourceFiniteTailControls u0 C (0 : Fin 6 → ℝ) = u0 := by
  cases u0
  simp [sourceFiniteTailControls, sourceFiniteTailControlVector,
    localPrefixControlsTenVector]

#print axioms sourceFiniteTailControls_zero

/-- A SOURCE-compatible map from six *level* state coordinates to
ten *level* controls. This is a finite P0-style SURROGATE continuation,
not an economic realization of the infinite-horizon tail. -/
noncomputable def sourceLogLinearContinuation
    (x0 : LocalPrefixStateSix) (u0 : LocalPrefixControlsTen)
    (C : SourceFiniteTailMatrix) : LocalPrefixContinuationRule :=
  fun x => sourceFiniteTailControls u0 C
    (fun k => Real.log
      (localPrefixStateSixVector x k / localPrefixStateSixVector x0 k))

/-- State log-chart coordinates are literally the baseline state
levels times exp(z), in every one of six SOURCE coordinates. -/
theorem sourceStateSix_logChart_vector_eq
    (x0 : LocalPrefixStateSix) (z : Fin 6 → ℝ) (j : Fin 6) :
    localPrefixStateSixVector (localPrefixStateSixLogChart x0 z) j =
      localPrefixStateSixVector x0 j * Real.exp (z j) := by
  fin_cases j <;> rfl

#print axioms sourceStateSix_logChart_vector_eq

/-- In the strictly positive state chart, log(x/x0) exactly recovers
the six original log deviations. No linear approximation is used. -/
theorem sourceStateSix_logDeviation_on_chart
    (x0 : LocalPrefixStateSix)
    (hx0 : LocalPrefixStateSixPositive x0)
    (z : Fin 6 → ℝ) :
    (fun j : Fin 6 => Real.log
      (localPrefixStateSixVector (localPrefixStateSixLogChart x0 z) j /
        localPrefixStateSixVector x0 j)) = z := by
  funext j
  rw [sourceStateSix_logChart_vector_eq]
  have hne : localPrefixStateSixVector x0 j ≠ 0 := ne_of_gt (hx0 j)
  have hratio :
      (localPrefixStateSixVector x0 j * Real.exp (z j)) /
        localPrefixStateSixVector x0 j = Real.exp (z j) := by
    field_simp [hne]
    ring
  rw [hratio, Real.log_exp]

#print axioms sourceStateSix_logDeviation_on_chart

/-- The finite SOURCE-typed continuation is EXACTLY the intended
10-control exponential matrix response at each log-chart state. -/
theorem sourceLogLinearContinuation_on_chart
    (x0 : LocalPrefixStateSix) (u0 : LocalPrefixControlsTen)
    (C : SourceFiniteTailMatrix)
    (hx0 : LocalPrefixStateSixPositive x0)
    (z : Fin 6 → ℝ) :
    sourceLogLinearContinuation x0 u0 C
      (localPrefixStateSixLogChart x0 z) =
    sourceFiniteTailControls u0 C z := by
  change sourceFiniteTailControls u0 C
    (fun j : Fin 6 => Real.log
      (localPrefixStateSixVector (localPrefixStateSixLogChart x0 z) j /
        localPrefixStateSixVector x0 j)) =
    sourceFiniteTailControls u0 C z
  rw [sourceStateSix_logDeviation_on_chart x0 hx0 z]

#print axioms sourceLogLinearContinuation_on_chart

/-- The reference source six-state maps back to exactly the reference
ten control levels, assuming the baseline six states are positive. -/
theorem sourceLogLinearContinuation_at_baseline
    (x0 : LocalPrefixStateSix) (u0 : LocalPrefixControlsTen)
    (C : SourceFiniteTailMatrix)
    (hx0 : LocalPrefixStateSixPositive x0) :
    sourceLogLinearContinuation x0 u0 C x0 = u0 := by
  have hz :
      (fun j : Fin 6 => Real.log
        (localPrefixStateSixVector x0 j / localPrefixStateSixVector x0 j)) =
      (0 : Fin 6 → ℝ) := by
    funext j
    simp [ne_of_gt (hx0 j)]
  change sourceFiniteTailControls u0 C
    (fun j : Fin 6 => Real.log
      (localPrefixStateSixVector x0 j / localPrefixStateSixVector x0 j)) = u0
  rw [hz]
  exact sourceFiniteTailControls_zero u0 C

#print axioms sourceLogLinearContinuation_at_baseline

/-- On the genuine SOURCE state log chart, the log response of the
surrogate continuation equals EXACTLY the specified ten-by-six
real matrix multiplication C*z, not only its derivative at zero.

No statement is made about an actual equilibrium infinite tail. -/
theorem sourceLogLinearContinuation_exact_log_response
    (x0 : LocalPrefixStateSix) (u0 : LocalPrefixControlsTen)
    (C : SourceFiniteTailMatrix)
    (hx0 : LocalPrefixStateSixPositive x0)
    (hu0 : ∀ j : Fin 10, 0 < localPrefixControlsTenVector u0 j)
    (z : Fin 6 → ℝ) (j : Fin 10) :
    localContinuationLogResponse x0
      (sourceLogLinearContinuation x0 u0 C) z j =
    ∑ k : Fin 6, C j k * z k := by
  change Real.log
    (localPrefixControlsTenVector
      (sourceLogLinearContinuation x0 u0 C
        (localPrefixStateSixLogChart x0 z)) j /
      localPrefixControlsTenVector
        (sourceLogLinearContinuation x0 u0 C x0) j) =
    ∑ k : Fin 6, C j k * z k
  rw [sourceLogLinearContinuation_on_chart x0 u0 C hx0 z,
    sourceLogLinearContinuation_at_baseline x0 u0 C hx0,
    sourceFiniteTailControls_vector_eq]
  change Real.log
    ((localPrefixControlsTenVector u0 j *
      Real.exp (∑ k : Fin 6, C j k * z k)) /
      localPrefixControlsTenVector u0 j) =
    ∑ k : Fin 6, C j k * z k
  have hne : localPrefixControlsTenVector u0 j ≠ 0 := ne_of_gt (hu0 j)
  have hratio :
      (localPrefixControlsTenVector u0 j *
        Real.exp (∑ k : Fin 6, C j k * z k)) /
        localPrefixControlsTenVector u0 j =
      Real.exp (∑ k : Fin 6, C j k * z k) := by
    field_simp [hne]
    ring
  rw [hratio, Real.log_exp]

#print axioms sourceLogLinearContinuation_exact_log_response

end Ventura26LiquidityAllocation
