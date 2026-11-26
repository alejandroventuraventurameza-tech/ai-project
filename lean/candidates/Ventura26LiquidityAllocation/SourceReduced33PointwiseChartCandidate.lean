import Ventura26LiquidityAllocation.SourceReduced33ActualEconomicMapCandidate

/-!
# Pointwise reconstruction of the genuine SOURCE 34 residual from 33 variables

The exact stationary funding-dual chart embeds 32 free economic log
coordinates plus reserve-remuneration innovation h in the ORIGINAL
34-equation SOURCE residual. At EVERY point of that chart, the final
funding-dual equation is zero, while the first 33 equations are
literally the reduced SOURCE economic map.

This is a pointwise identity and a left-inverse property, stronger than
an existential root-set equivalence. It does not assert a zero exists,
that the 33x33 derivative is invertible, or that a full dynamic
competitive equilibrium has been constructed.
-/

namespace Ventura26LiquidityAllocation

open ProposedLocalScalarAugmented34Source
open ProposedLocalScalarEconomicSlice

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- The exact 32-log lift deletes back to the supplied free coordinates. -/
theorem sourceFundingDualLift32_removeNth_leftInverse
    (P : Primitives S) (Z0 : LocalPrefixCoordinates)
    (u : Fin 32 → ℝ) :
    (15 : Fin 33).removeNth (sourceFundingDualLift32 P Z0 u) = u := by
  funext i
  exact sourceFundingDualLift32_other P Z0 u i

/-- Consequently no two distinct reduced log vectors are identified. -/
theorem sourceFundingDualLift32_injective
    (P : Primitives S) (Z0 : LocalPrefixCoordinates) :
    Function.Injective (sourceFundingDualLift32 P Z0) := by
  intro u v huv
  have hu := sourceFundingDualLift32_removeNth_leftInverse P Z0 u
  have hv := sourceFundingDualLift32_removeNth_leftInverse P Z0 v
  calc
    u = (15 : Fin 33).removeNth (sourceFundingDualLift32 P Z0 u) := hu.symm
    _ = (15 : Fin 33).removeNth (sourceFundingDualLift32 P Z0 v) := by rw [huv]
    _ = v := hv

/-- The ORIGINAL funding dual is identically zero over the exact
stationary reduced chart, not merely at a candidate economic root. -/
theorem sourceFundingDualLift32_dual_zero
    (P : Primitives S) (Z0 : LocalPrefixCoordinates)
    (u : Fin 32 → ℝ)
    (hsigma : P.entrepreneurRiskAversion = 1)
    (hc_same : Z0.controlsZero.consumptionL = Z0.controlsOne.consumptionL)
    (hc_positive : 0 < Z0.controlsZero.consumptionL)
    (hpi : Z0.controlsOne.inflation = 1)
    (hr : 0 < Z0.controlsZero.loanRate)
    (hbeta : 0 < P.entrepreneurDiscount) :
    localNormalizedCollateralDualL P
      (localPrefixLogChart Z0 (sourceFundingDualLift32 P Z0 u)) = 0 := by
  change localNormalizedCollateralDualL P
    (localPrefixLogChart Z0 (sourceDualLoanLogEliminate
      P Z0 ((15 : Fin 33).insertNth (0 : ℝ) u))) = 0
  exact sourceDualLoanLogEliminate_dual_zero
    P Z0 ((15 : Fin 33).insertNth (0 : ℝ) u)
    hsigma hc_same hc_positive hpi hr hbeta

/-- Exact pointwise SOURCE identity: F(L(u),h)=(G(u,h),0).
This equality concerns the genuine SOURCE equations, not Python rows. -/
theorem sourceReduced33_pointwise_reconstruction
    (P : Primitives S) (I : InheritedState)
    (Z0 : LocalPrefixCoordinates) (dateOne recurrent : S)
    (tail : LocalPrefixContinuationRule)
    (u : Fin 32 → ℝ) (h : ℝ)
    (hsigma : P.entrepreneurRiskAversion = 1)
    (hc_same : Z0.controlsZero.consumptionL = Z0.controlsOne.consumptionL)
    (hc_positive : 0 < Z0.controlsZero.consumptionL)
    (hpi : Z0.controlsOne.inflation = 1)
    (hr : 0 < Z0.controlsZero.loanRate)
    (hbeta : 0 < P.entrepreneurDiscount) :
    augmentedBoundaryZeroResidual P I Z0 dateOne recurrent tail
      (sourceFundingDualLift32 P Z0 u) h =
    (sourceReduced33EconomicMap P I Z0 dateOne recurrent tail (u, h), 0) := by
  apply Prod.ext
  · rfl
  · exact sourceFundingDualLift32_dual_zero P Z0 u
      hsigma hc_same hc_positive hpi hr hbeta

/-- A reduced zero is equivalent, at the SAME lifted variables, to
a genuine SOURCE 34-equation zero. This does not prove existence. -/
theorem sourceReduced33_pointwise_root_iff
    (P : Primitives S) (I : InheritedState)
    (Z0 : LocalPrefixCoordinates) (dateOne recurrent : S)
    (tail : LocalPrefixContinuationRule)
    (u : Fin 32 → ℝ) (h : ℝ)
    (hsigma : P.entrepreneurRiskAversion = 1)
    (hc_same : Z0.controlsZero.consumptionL = Z0.controlsOne.consumptionL)
    (hc_positive : 0 < Z0.controlsZero.consumptionL)
    (hpi : Z0.controlsOne.inflation = 1)
    (hr : 0 < Z0.controlsZero.loanRate)
    (hbeta : 0 < P.entrepreneurDiscount) :
    sourceReduced33EconomicMap P I Z0 dateOne recurrent tail (u, h) = 0 ↔
    augmentedBoundaryZeroResidual P I Z0 dateOne recurrent tail
      (sourceFundingDualLift32 P Z0 u) h = (0, 0) := by
  rw [sourceReduced33_pointwise_reconstruction
    P I Z0 dateOne recurrent tail u h
    hsigma hc_same hc_positive hpi hr hbeta]
  simp

#print axioms sourceFundingDualLift32_removeNth_leftInverse
#print axioms sourceFundingDualLift32_injective
#print axioms sourceFundingDualLift32_dual_zero
#print axioms sourceReduced33_pointwise_reconstruction
#print axioms sourceReduced33_pointwise_root_iff

end Ventura26LiquidityAllocation
