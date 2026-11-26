import Ventura26LiquidityAllocation.LocalScalarPositiveLogChartDomainCandidate

/-!
# Exact 33-coordinate log-chart recentering

A Banach zero of the 34-dimensional system may have z* != 0 and
h* != 0. Recenering the numerical chart at Z* = chart(Z0,z*) is
an exact geometric operation; it is NOT enough to normalize the
economic system unless its policy primitives are also shifted by h*.

The statements here are only coordinate equalities and positivity
transfers. They do not construct the 34-dimensional Banach zero or
show that the re-intervened economic residual is identical to the
original residual after a policy shift. Those are separate tasks.
-/

namespace Ventura26LiquidityAllocation
namespace ProposedLocalScalarAugmented34LogRecenter

open ProposedLocalScalarPositiveLogChartDomain

/-- Adding a new log perturbation around the shifted center is
coordinate-by-coordinate identical to adding both log perturbations
around the old reference. -/
theorem source_log_chart_recenter_coordinate
    (Z0 : LocalPrefixCoordinates)
    (zc u : Fin 33 → ℝ) (j : Fin 33) :
    localPrefixCoordinatesVector
      (localPrefixLogChart (localPrefixLogChart Z0 zc) u) j =
    localPrefixCoordinatesVector
      (localPrefixLogChart Z0 (zc + u)) j := by
  simp only [localPrefixLogChart, localPrefixCoordinatesVector_ofVector_at,
    Pi.add_apply, Real.exp_add]
  ring

/-- Zero new log coordinates recover the shifted reference, with
no approximation, at every one of the 33 original economic levels. -/
theorem source_recentered_zero_is_shifted_reference
    (Z0 : LocalPrefixCoordinates)
    (zc : Fin 33 → ℝ) (j : Fin 33) :
    localPrefixCoordinatesVector
      (localPrefixLogChart (localPrefixLogChart Z0 zc) 0) j =
    localPrefixCoordinatesVector
      (localPrefixLogChart Z0 zc) j := by
  simp [localPrefixLogChart, localPrefixCoordinatesVector_ofVector_at]

/-- Positivity of the original 33 levels carries to the shifted
reference regardless of zc. This does NOT prove that the original
economic initial reference was positive; that remains a premise. -/
theorem source_recentered_reference_positive
    (Z0 : LocalPrefixCoordinates)
    (hbase : LocalPrefixCoordinatesPositive Z0)
    (zc : Fin 33 → ℝ) :
    LocalPrefixCoordinatesPositive (localPrefixLogChart Z0 zc) :=
  localPrefixLogChart_positive Z0 hbase zc

#print axioms source_log_chart_recenter_coordinate
#print axioms source_recentered_zero_is_shifted_reference
#print axioms source_recentered_reference_positive

end ProposedLocalScalarAugmented34LogRecenter
end Ventura26LiquidityAllocation
