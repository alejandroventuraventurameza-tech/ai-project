import Ventura26LiquidityAllocation.SourceAugmented34SchurBlockCandidate
import Mathlib.Analysis.Calculus.FDeriv.Prod

/-!
# Actual SOURCE 34-row boundary Jacobian: exact block decomposition

The 34-equation SOURCE augmented boundary map is the *literal* one
defined in LocalScalarAugmented34SourceCandidate.lean, uncurried as a map
from (33 log coordinates, remuneration innovation) to 33 economic rows
and the normalized L funding dual.

We assemble the full Frechet derivative from explicit economic
differentiability assumptions. Its lower-right derivative is literally
zero because the last SOURCE row depends only on the 33 log coordinates.
If the 33x33 derivative block A is already supplied as a linear
equivalence, the abstract Schur theorem applies to the ACTUAL SOURCE
Jacobian with b and c identified as genuine derivatives.

This file does not establish those differentiability hypotheses,
actual A-invertibility, nonzero Schur scalar, existence or dynamics.
-/

namespace Ventura26LiquidityAllocation
namespace ProposedLocalScalarAugmented34Source

variable {S : Type*} [Fintype S] [DecidableEq S]

private abbrev Economic33 := Fin 33 → ℝ

/-- The literal SOURCE augmented 34-residual as a map of a product
of the original positive-log coordinates and reserve-rate innovation. -/
noncomputable def sourceAugmented34Map
    (P : Primitives S) (I : InheritedState) (Z0 : LocalPrefixCoordinates)
    (dateOne recurrent : S) (tail : LocalPrefixContinuationRule) :
    (Economic33 × ℝ) → (Economic33 × ℝ) :=
  fun zh => augmentedBoundaryZeroResidual P I Z0 dateOne recurrent tail zh.1 zh.2

/-- The literal 33 SOURCE modified binding-prefix rows. -/
noncomputable def sourceAugmented34Rows
    (P : Primitives S) (I : InheritedState) (Z0 : LocalPrefixCoordinates)
    (dateOne recurrent : S) (tail : LocalPrefixContinuationRule) :
    (Economic33 × ℝ) → Economic33 :=
  fun zh row => localBindingResidualWithSlack P I Z0 dateOne recurrent tail
    (reserveRemunerationSlice 0 zh.2) zh.1 row

/-- The literal SOURCE normalized funding dual of firm L, on the same
33 original economic log coordinates. No h argument appears. -/
noncomputable def sourceAugmented34Dual
    (P : Primitives S) (Z0 : LocalPrefixCoordinates) : Economic33 → ℝ :=
  fun z => localNormalizedCollateralDualL P (localPrefixLogChart Z0 z)

/-- Identify the exact source map with the product of the 33 economic
rows and the scalar L funding-dual row, with no new surrogate residual. -/
theorem sourceAugmented34Map_eq_pair
    (P : Primitives S) (I : InheritedState) (Z0 : LocalPrefixCoordinates)
    (dateOne recurrent : S) (tail : LocalPrefixContinuationRule)
    (zh : Economic33 × ℝ) :
    sourceAugmented34Map P I Z0 dateOne recurrent tail zh =
      (sourceAugmented34Rows P I Z0 dateOne recurrent tail zh,
       sourceAugmented34Dual P Z0 zh.1) := by
  rfl

#print axioms sourceAugmented34Map_eq_pair

/-- Assemble the derivative of the genuine 34 SOURCE equations.
The lower-right block vanishes: the derivative of the last residual
in direction (0,t) is identically zero, at fixed log coordinates. -/
theorem sourceAugmented34Map_hasFDerivAt
    (P : Primitives S) (I : InheritedState) (Z0 : LocalPrefixCoordinates)
    (dateOne recurrent : S) (tail : LocalPrefixContinuationRule)
    (zstar : Economic33) (hstar : ℝ)
    (dB : (Economic33 × ℝ) →L[ℝ] Economic33)
    (dc : Economic33 →L[ℝ] ℝ)
    (hB : HasFDerivAt (sourceAugmented34Rows P I Z0 dateOne recurrent tail)
      dB (zstar, hstar))
    (hc : HasFDerivAt (sourceAugmented34Dual P Z0) dc zstar) :
    HasFDerivAt (sourceAugmented34Map P I Z0 dateOne recurrent tail)
      (dB.prod (dc.comp (ContinuousLinearMap.fst ℝ Economic33 ℝ)))
      (zstar, hstar) := by
  have hdual : HasFDerivAt
      (fun zh : Economic33 × ℝ => sourceAugmented34Dual P Z0 zh.1)
      (dc.comp (ContinuousLinearMap.fst ℝ Economic33 ℝ))
      (zstar, hstar) :=
    hc.comp (zstar, hstar) hasFDerivAt_fst
  have hpair := hB.prodMk hdual
  have hfun : sourceAugmented34Map P I Z0 dateOne recurrent tail =
      (fun zh => (sourceAugmented34Rows P I Z0 dateOne recurrent tail zh,
         sourceAugmented34Dual P Z0 zh.1)) := by
    funext zh
    exact sourceAugmented34Map_eq_pair P I Z0 dateOne recurrent tail zh
  rw [hfun]
  exact hpair

#print axioms sourceAugmented34Map_hasFDerivAt

/-- Any continuously linear derivative of a 33-row map on 33+1
coordinates decomposes exactly into its 33-coordinate and scalar
innovation components, without finite-difference approximations. -/
theorem sourceAugmented34_linear_split
    (dB : (Economic33 × ℝ) →L[ℝ] Economic33)
    (u : Economic33) (t : ℝ) :
    dB (u, t) = dB (u, (0 : ℝ)) + t • dB ((0 : Economic33), (1 : ℝ)) := by
  have hp : (u, t) =
      (u, (0 : ℝ)) + t • ((0 : Economic33), (1 : ℝ)) := by
    apply Prod.ext
    · simp
    · simp
  rw [hp, map_add, map_smul]

#print axioms sourceAugmented34_linear_split

/-- Conditional exact SOURCE 34-by-34 rank gate:
If the genuine 33-row economic derivative block has a supplied
linear equivalence A, then the FULL genuine augmented Frechet
Jacobian is bijective iff the exact transversality scalar
dc(A^-1 * d_h B) differs from zero.

The premise hA identifies A with the actual 33-coordinate SOURCE
derivative, and is NOT derived here. -/
theorem sourceAugmented34_actualJacobian_bijective_iff_schur
    (P : Primitives S) (I : InheritedState) (Z0 : LocalPrefixCoordinates)
    (dateOne recurrent : S) (tail : LocalPrefixContinuationRule)
    (zstar : Economic33) (hstar : ℝ)
    (dB : (Economic33 × ℝ) →L[ℝ] Economic33)
    (dc : Economic33 →L[ℝ] ℝ)
    (A : Economic33 ≃ₗ[ℝ] Economic33)
    (hB : HasFDerivAt (sourceAugmented34Rows P I Z0 dateOne recurrent tail)
      dB (zstar, hstar))
    (hc : HasFDerivAt (sourceAugmented34Dual P Z0) dc zstar)
    (hA : ∀ u : Economic33, dB (u, (0 : ℝ)) = A u) :
    Function.Bijective (fderiv ℝ
      (sourceAugmented34Map P I Z0 dateOne recurrent tail) (zstar, hstar)) ↔
      dc (A.symm (dB ((0 : Economic33), (1 : ℝ)))) ≠ 0 := by
  have hfull := sourceAugmented34Map_hasFDerivAt P I Z0 dateOne recurrent tail
    zstar hstar dB dc hB hc
  have hfun :
      (fun v : Economic33 × ℝ =>
        (fderiv ℝ (sourceAugmented34Map P I Z0 dateOne recurrent tail)
          (zstar, hstar)) v) =
      sourceAugmentedSchurBlock A
        (dB ((0 : Economic33), (1 : ℝ))) dc.toLinearMap := by
    funext v
    rcases v with ⟨u, t⟩
    rw [hfull.fderiv]
    change (dB (u, t), dc u) =
      (A u + t • dB ((0 : Economic33), (1 : ℝ)), dc u)
    rw [sourceAugmented34_linear_split, hA u]
  change Function.Bijective
    (fun v : Economic33 × ℝ =>
      (fderiv ℝ (sourceAugmented34Map P I Z0 dateOne recurrent tail)
        (zstar, hstar)) v) ↔ _
  rw [hfun]
  exact sourceAugmentedSchurBlock_bijective_iff
    A (dB ((0 : Economic33), (1 : ℝ))) dc.toLinearMap

#print axioms sourceAugmented34_actualJacobian_bijective_iff_schur

end ProposedLocalScalarAugmented34Source
end Ventura26LiquidityAllocation
