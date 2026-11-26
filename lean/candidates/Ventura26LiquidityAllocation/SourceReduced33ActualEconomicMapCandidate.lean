import Ventura26LiquidityAllocation.SourceFundingDualExact33FreeCoordinatesCandidate

/-!
# A concrete 33-unknown / 33-equation SOURCE reduced economic operator

This definition, unlike an existential claim with a redundant z15,
has exactly 32 genuine free economic log coordinates and one
reserve-remuneration policy innovation as its INPUT. Its 33 residual
rows are evaluated from the ORIGINAL SOURCE economy after exact
analytic elimination of the L funding-dual equation.

Under the stationary unit-CRRA, positive rate/discount conditions,
the existence of a root of this reduced map is logically equivalent
to the existence of a 34-equation SOURCE augmented root.

This is NOT a numerical interval certificate, SOURCE/Python semantic
identity, derivative-rank proof, or existence of an economic root.
-/

namespace Ventura26LiquidityAllocation

open ProposedLocalScalarAugmented34Source
open ProposedLocalScalarEconomicSlice

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- Exactly 33 economic equations in a 33-dimensional real domain:
32 free log coordinates plus the reserve-remuneration innovation h. -/
noncomputable def sourceReduced33EconomicMap
    (P : Primitives S) (I : InheritedState)
    (Z0 : LocalPrefixCoordinates) (dateOne recurrent : S)
    (tail : LocalPrefixContinuationRule)
    (w : (Fin 32 → ℝ) × ℝ) : Fin 33 → ℝ :=
  localBindingResidualWithSlack P I Z0 dateOne recurrent tail
    (reserveRemunerationSlice 0 w.2)
    (sourceFundingDualLift32 P Z0 w.1)

/-- The exact SOURCE 34-equation boundary-root problem reduces to
the zero set of the 33x33 true economic map, conditionally on the
displayed positive stationary assumptions. -/
theorem source34_root_exists_iff_sourceReduced33EconomicMap_zero
    (P : Primitives S) (I : InheritedState)
    (Z0 : LocalPrefixCoordinates) (dateOne recurrent : S)
    (tail : LocalPrefixContinuationRule)
    (hsigma : P.entrepreneurRiskAversion = 1)
    (hc_same : Z0.controlsZero.consumptionL = Z0.controlsOne.consumptionL)
    (hc_positive : 0 < Z0.controlsZero.consumptionL)
    (hpi : Z0.controlsOne.inflation = 1)
    (hr : 0 < Z0.controlsZero.loanRate)
    (hbeta : 0 < P.entrepreneurDiscount) :
    (∃ (z : Fin 33 → ℝ) (h : ℝ),
      augmentedBoundaryZeroResidual
        P I Z0 dateOne recurrent tail z h = (0, 0)) ↔
    (∃ w : (Fin 32 → ℝ) × ℝ,
      sourceReduced33EconomicMap
        P I Z0 dateOne recurrent tail w = 0) := by
  rw [source34_root_exists_iff_exact_32logs_plus_policy
    P I Z0 dateOne recurrent tail
    hsigma hc_same hc_positive hpi hr hbeta]
  constructor
  · rintro ⟨u, h, hrows⟩
    refine ⟨(u, h), ?_⟩
    funext row
    exact hrows row
  · rintro ⟨⟨u, h⟩, hzero⟩
    refine ⟨u, h, ?_⟩
    intro row
    have hr := congrFun hzero row
    simpa only [sourceReduced33EconomicMap] using hr

#print axioms source34_root_exists_iff_sourceReduced33EconomicMap_zero

end Ventura26LiquidityAllocation
