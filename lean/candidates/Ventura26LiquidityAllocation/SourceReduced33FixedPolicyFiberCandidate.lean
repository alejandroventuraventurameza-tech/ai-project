import Ventura26LiquidityAllocation.SourceReduced33RootEquivCandidate

/-!
# Fixed-policy fibers of the genuine 34-to-33 SOURCE root chart

The 34x34 augmented SOURCE exercise solves for BOTH 33 economic logs
and the reserve-remuneration innovation h. Eliminating its stationarity
funding-dual equation produces 33 equations in 32 free logs PLUS h.
Consequently a root with an ENDOGENOUSLY solved h does not automatically
certify a root at the externally prescribed IRF shock h_target.

For each separately FIXED reserve-remuneration innovation h, define the
genuine SOURCE fixed-policy problem as 33 economic residuals in only
32 free logs. Its zero set is equivalent to the original 34 SOURCE
equations with h fixed, under the stated stationary assumptions.

This is a precise mathematical distinction between the boundary
root search and a fixed-shock structural IRF. It does NOT say the
fixed-policy problem has a root, nor does it assert nonexistence.
-/

namespace Ventura26LiquidityAllocation

open ProposedLocalScalarAugmented34Source
open ProposedLocalScalarEconomicSlice

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- For a prescribed h, the actual SOURCE economic map has
32 endogenous log inputs and 33 original SOURCE residual outputs. -/
noncomputable def sourceReduced33AtFixedRemuneration
    (P : Primitives S) (I : InheritedState)
    (Z0 : LocalPrefixCoordinates) (dateOne recurrent : S)
    (tail : LocalPrefixContinuationRule) (h : ℝ) :
    (Fin 32 → ℝ) → (Fin 33 → ℝ) :=
  fun u => sourceReduced33EconomicMap
    P I Z0 dateOne recurrent tail (u, h)

/-- Root-set equivalence with policy FIXED at the same h on each
side. An augmented root at an unknown hStar alone is insufficient
to instantiate this theorem at a different shock hTarget. -/
theorem sourceReduced33_fixedRemuneration_root_exists_iff
    (P : Primitives S) (I : InheritedState)
    (Z0 : LocalPrefixCoordinates) (dateOne recurrent : S)
    (tail : LocalPrefixContinuationRule) (h : ℝ)
    (hsigma : P.entrepreneurRiskAversion = 1)
    (hc_same : Z0.controlsZero.consumptionL = Z0.controlsOne.consumptionL)
    (hc_positive : 0 < Z0.controlsZero.consumptionL)
    (hpi : Z0.controlsOne.inflation = 1)
    (hr : 0 < Z0.controlsZero.loanRate)
    (hbeta : 0 < P.entrepreneurDiscount) :
    (∃ u : Fin 32 → ℝ,
      sourceReduced33AtFixedRemuneration
        P I Z0 dateOne recurrent tail h u = 0) ↔
    (∃ z : Fin 33 → ℝ,
      augmentedBoundaryZeroResidual
        P I Z0 dateOne recurrent tail z h = (0, 0)) := by
  constructor
  · rintro ⟨u, hu⟩
    refine ⟨sourceFundingDualLift32 P Z0 u, ?_⟩
    exact (sourceReduced33_pointwise_root_iff
      P I Z0 dateOne recurrent tail u h
      hsigma hc_same hc_positive hpi hr hbeta).mp hu
  · rintro ⟨z, hz⟩
    refine ⟨(15 : Fin 33).removeNth z, ?_⟩
    exact sourceReduced33_root_from_original
      P I Z0 dateOne recurrent tail z h
      hsigma hc_same hc_positive hpi hr hbeta hz

#print axioms sourceReduced33_fixedRemuneration_root_exists_iff

/-- The exact SOURCE root sets of the fixed-policy 32-to-33
and original fixed-h 33-to-34 systems are bijective. -/
noncomputable def sourceReduced33_fixedRemuneration_root_equiv
    (P : Primitives S) (I : InheritedState)
    (Z0 : LocalPrefixCoordinates) (dateOne recurrent : S)
    (tail : LocalPrefixContinuationRule) (h : ℝ)
    (hsigma : P.entrepreneurRiskAversion = 1)
    (hc_same : Z0.controlsZero.consumptionL = Z0.controlsOne.consumptionL)
    (hc_positive : 0 < Z0.controlsZero.consumptionL)
    (hpi : Z0.controlsOne.inflation = 1)
    (hr : 0 < Z0.controlsZero.loanRate)
    (hbeta : 0 < P.entrepreneurDiscount) :
    {u : Fin 32 → ℝ //
      sourceReduced33AtFixedRemuneration
        P I Z0 dateOne recurrent tail h u = 0} ≃
    {z : Fin 33 → ℝ //
      augmentedBoundaryZeroResidual
        P I Z0 dateOne recurrent tail z h = (0, 0)} where
  toFun := fun u =>
    ⟨sourceFundingDualLift32 P Z0 u.1,
      (sourceReduced33_pointwise_root_iff P I Z0 dateOne recurrent tail
        u.1 h hsigma hc_same hc_positive hpi hr hbeta).mp u.2⟩
  invFun := fun z =>
    ⟨(15 : Fin 33).removeNth z.1,
      sourceReduced33_root_from_original
        P I Z0 dateOne recurrent tail z.1 h
        hsigma hc_same hc_positive hpi hr hbeta z.2⟩
  left_inv := by
    intro u
    apply Subtype.ext
    exact sourceFundingDualLift32_removeNth_leftInverse P Z0 u.1
  right_inv := by
    intro z
    apply Subtype.ext
    exact sourceFundingDualLift32_recovers_original_root
      P I Z0 dateOne recurrent tail z.1 h
      hsigma hc_same hc_positive hpi hr hbeta z.2

#print axioms sourceReduced33_fixedRemuneration_root_equiv

end Ventura26LiquidityAllocation
