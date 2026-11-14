import Ventura26LiquidityAllocation.SourceAugmented34PositiveLogSchurCandidate

/-!
# Exact SOURCE 34x34 linearized funding multiplier and Schur transversality

This module identifies the economic meaning of the Schur scalar.
Given an invertible genuine SOURCE 33-row derivative block A, a
linearized response to the reserve-remuneration policy innovation
satisfies A*u + b = 0. Its normalized firm-L funding-dual change is
-c(A.symm b), the same scalar as the augmented Jacobian Schur gate.

The results are **conditional** on the SOURCE 33-row differentiability
and A's actual invertibility; neither is proven by this candidate.
No equilibrium branch, dynamic IRF, or policy growth effect follows.
-/

namespace Ventura26LiquidityAllocation
namespace ProposedLocalScalarAugmented34Source

private abbrev Economic33 := Fin 33 → ℝ

/-- A SOURCE-shaped 33-row linearized equilibrium response has
exactly the Schur scalar as its normalized L funding-dual derivative. -/
theorem sourceAugmented34_linearizedDual_identity
    (dB : (Economic33 × ℝ) →L[ℝ] Economic33)
    (dc : Economic33 →L[ℝ] ℝ)
    (A : Economic33 ≃ₗ[ℝ] Economic33)
    (u : Economic33)
    (hA : ∀ x : Economic33, dB (x, (0 : ℝ)) = A x)
    (hlin : dB (u, (1 : ℝ)) = 0) :
    dc u = -(dc (A.symm (dB ((0 : Economic33), (1 : ℝ))))) := by
  have hs : dB (u, (1 : ℝ)) =
      A u + dB ((0 : Economic33), (1 : ℝ)) := by
    simpa only [one_smul, hA u] using
      (sourceAugmented34_linear_split dB u (1 : ℝ))
  have hsum : A u + dB ((0 : Economic33), (1 : ℝ)) = 0 := by
    calc
      A u + dB ((0 : Economic33), (1 : ℝ)) = dB (u, (1 : ℝ)) := hs.symm
      _ = 0 := hlin
  have hu : u = -(A.symm (dB ((0 : Economic33), (1 : ℝ)))) := by
    have hp := congrArg A.symm (eq_neg_of_add_eq_zero_left hsum)
    simpa [map_neg] using hp
  rw [hu, map_neg]

#print axioms sourceAugmented34_linearizedDual_identity

/-- The TRUE SOURCE 34-equation Jacobian is bijective exactly when
the genuine normalized firm-L funding multiplier responds nontrivially
along a solution to the linearized 33-row remuneration experiment.

All economic regularity assumptions and invertibility of the
genuine 33-row A are explicit premises, not numerical certificates.
The direction u must satisfy all 33 first-order SOURCE equations. -/
theorem sourceAugmented34_actualJacobian_bijective_iff_linearizedDual_ne
    {S : Type*} [Fintype S] [DecidableEq S]
    (P : Primitives S) (I : InheritedState)
    (Z0 : LocalPrefixCoordinates)
    (dateOne recurrent : S) (tail : LocalPrefixContinuationRule)
    (hZ0 : LocalPrefixCoordinatesPositive Z0)
    (zstar : Economic33) (hstar : ℝ)
    (A : Economic33 ≃ₗ[ℝ] Economic33)
    (hB : DifferentiableAt ℝ
      (sourceAugmented34Rows P I Z0 dateOne recurrent tail)
      (zstar, hstar))
    (hA : ∀ x : Economic33,
      (fderiv ℝ
        (sourceAugmented34Rows P I Z0 dateOne recurrent tail)
        (zstar, hstar)) (x, (0 : ℝ)) = A x)
    (u : Economic33)
    (hu : (fderiv ℝ
      (sourceAugmented34Rows P I Z0 dateOne recurrent tail)
      (zstar, hstar)) (u, (1 : ℝ)) = 0) :
    Function.Bijective
      (fderiv ℝ
        (sourceAugmented34Map P I Z0 dateOne recurrent tail)
        (zstar, hstar)) ↔
      (fderiv ℝ (sourceAugmented34Dual P Z0) zstar) u ≠ 0 := by
  let dB : (Economic33 × ℝ) →L[ℝ] Economic33 :=
    fderiv ℝ (sourceAugmented34Rows P I Z0 dateOne recurrent tail)
      (zstar, hstar)
  let dc : Economic33 →L[ℝ] ℝ :=
    fderiv ℝ (sourceAugmented34Dual P Z0) zstar
  have hidentity : dc u = -(dc (A.symm (dB ((0 : Economic33), (1 : ℝ))))) :=
    sourceAugmented34_linearizedDual_identity dB dc A u hA hu
  have hschur :=
    sourceAugmented34_actualJacobian_bijective_iff_of_positive_log
      P I Z0 dateOne recurrent tail hZ0
      zstar hstar A hB hA
  change Function.Bijective
      (fderiv ℝ (sourceAugmented34Map P I Z0 dateOne recurrent tail)
        (zstar, hstar)) ↔ dc u ≠ 0
  rw [hidentity]
  simpa only [neg_ne_zero] using hschur

#print axioms sourceAugmented34_actualJacobian_bijective_iff_linearizedDual_ne

end ProposedLocalScalarAugmented34Source
end Ventura26LiquidityAllocation
