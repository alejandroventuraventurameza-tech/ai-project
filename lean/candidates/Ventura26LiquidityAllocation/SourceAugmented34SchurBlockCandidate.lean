import Ventura26LiquidityAllocation.SourceEulerLogLinearizedResponseCandidate
import Ventura26LiquidityAllocation.LocalScalarAugmented34SourceCandidate

/-!
# Abstract 33+1 SOURCE block-algebra gate for augmented boundary Jacobian

The SOURCE 34th funding-dual residual is independent of h at fixed z.
Consequently, once all SOURCE Frechet derivatives and the actual block
identifications are established, the full 34x34 Jacobian must have the
shape (A x + h*b, c x).

This file proves the Schur-transversality gate algebraically assuming
an invertible 33x33 block A. It does NOT provide that economic inverse,
or the required differentiability, or a numerical source certificate.
-/

namespace Ventura26LiquidityAllocation

private abbrev Source33 := Fin 33 → ℝ

/-- Abstract 34-by-34 block action with lower-right block structurally
zero, matching the genuine SOURCE augmented funding-dual experiment. -/
noncomputable def sourceAugmentedSchurBlock
    (A : Source33 ≃ₗ[ℝ] Source33)
    (b : Source33) (c : Source33 →ₗ[ℝ] ℝ) :
    (Source33 × ℝ) → (Source33 × ℝ) :=
  fun p => (A p.1 + p.2 • b, c p.1)

/-- Explicit inverse of the SOURCE-shaped Schur block, defined when
c(A^-1 b) is nonzero. -/
private noncomputable def sourceAugmentedSchurBlockInverse
    (A : Source33 ≃ₗ[ℝ] Source33)
    (b : Source33) (c : Source33 →ₗ[ℝ] ℝ) :
    (Source33 × ℝ) → (Source33 × ℝ) :=
  fun p =>
    let q := (c (A.symm p.1) - p.2) / c (A.symm b)
    (A.symm p.1 - q • A.symm b, q)

/-- A square SOURCE-shaped 34-system with a *known invertible* 33-block
is bijective exactly when its funding-dual transversality scalar
c(A^-1 b) is nonzero. No such condition is assumed for the genuine
economic SOURCE derivatives in this purely algebraic theorem. -/
theorem sourceAugmentedSchurBlock_bijective_iff
    (A : Source33 ≃ₗ[ℝ] Source33)
    (b : Source33) (c : Source33 →ₗ[ℝ] ℝ) :
    Function.Bijective (sourceAugmentedSchurBlock A b c) ↔
      c (A.symm b) ≠ 0 := by
  constructor
  · intro hbij
    intro hd
    have hf :
        sourceAugmentedSchurBlock A b c (-(A.symm b), (1 : ℝ)) =
          sourceAugmentedSchurBlock A b c (0, (0 : ℝ)) := by
      apply Prod.ext
      · simp [sourceAugmentedSchurBlock, map_neg]
      · simp [sourceAugmentedSchurBlock, hd]
    have hpair := hbij.1 hf
    have hbad := congrArg Prod.snd hpair
    norm_num at hbad
  · intro hd
    have hleft : Function.LeftInverse
        (sourceAugmentedSchurBlockInverse A b c)
        (sourceAugmentedSchurBlock A b c) := by
      intro p
      rcases p with ⟨x,t⟩
      have hq :
          (c (A.symm (A x + t • b)) - c x) / c (A.symm b) = t := by
        simp only [map_add, map_smul, A.symm_apply_apply, smul_eq_mul]
        field_simp [hd]
        ring
      apply Prod.ext
      · change
          A.symm (A x + t • b) -
            ((c (A.symm (A x + t • b)) - c x) /
              c (A.symm b)) • A.symm b = x
        rw [hq]
        simp [map_add, map_smul, sub_add_cancel]
      · exact hq
    have hright : Function.RightInverse
        (sourceAugmentedSchurBlockInverse A b c)
        (sourceAugmentedSchurBlock A b c) := by
      intro p
      rcases p with ⟨y,s⟩
      let q : ℝ := (c (A.symm y) - s) / c (A.symm b)
      have hqd : q * c (A.symm b) = c (A.symm y) - s := by
        dsimp [q]
        field_simp [hd]
      apply Prod.ext
      · change
          A (A.symm y - q • A.symm b) + q • b = y
        simp [map_sub, map_smul, sub_add_cancel]
      · change c (A.symm y - q • A.symm b) = s
        rw [map_sub, map_smul]
        change c (A.symm y) - q * c (A.symm b) = s
        rw [hqd]
        ring
    exact ⟨hleft.injective, hright.surjective⟩

#print axioms sourceAugmentedSchurBlock_bijective_iff

end Ventura26LiquidityAllocation
