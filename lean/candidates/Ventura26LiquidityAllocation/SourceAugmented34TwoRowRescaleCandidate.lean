import Ventura26LiquidityAllocation.SourceCanonicalTwoPledgeLogBoundaryCandidate

/-!
# SOURCE augmented 34: abstract two-row invertible rescaling

Both collateral row normalizations have POSITIVE scaling factors at
a genuine positive binding root. This module proves only the
algebraic transport of bijectivity for the 33-vector plus scalar
dual output, with row indices 5 and 21. It assumes no economic
root or derivative equality.

The additional SOURCE-specific derivative bridge from original
rows to the scaled rows is a separate required theorem.
-/

namespace Ventura26LiquidityAllocation
namespace ProposedLocalScalarAugmented34Source

noncomputable def source34TwoRowRescale
    (k5 k21 : ℝ) (v : (Fin 33 → ℝ) × ℝ) :
    (Fin 33 → ℝ) × ℝ :=
  (fun row =>
      if row = (5 : Fin 33) then k5 * v.1 row
      else if row = (21 : Fin 33) then k21 * v.1 row
      else v.1 row,
   v.2)

/-- Applying reciprocal row scaling twice recovers every 34-output vector. -/
theorem source34TwoRowRescale_inverse
    (k5 k21 : ℝ) (hk5 : k5 ≠ 0) (hk21 : k21 ≠ 0)
    (v : (Fin 33 → ℝ) × ℝ) :
    source34TwoRowRescale k5⁻¹ k21⁻¹
      (source34TwoRowRescale k5 k21 v) = v := by
  apply Prod.ext
  · funext row
    by_cases h5 : row = (5 : Fin 33)
    · subst row
      simp [source34TwoRowRescale, hk5]
    · by_cases h21 : row = (21 : Fin 33)
      · subst row
        simp [source34TwoRowRescale, hk21]
      · simp [source34TwoRowRescale, h5, h21]
  · rfl

#print axioms source34TwoRowRescale_inverse

/-- Two nonzero economic collateral scalings preserve and reflect
bijectivity for ANY 34-output Jacobian map, independently of
linear coordinate representation. -/
theorem source34TwoRowRescale_comp_bijective_iff
    {E : Type*} (J : E → (Fin 33 → ℝ) × ℝ)
    (k5 k21 : ℝ) (hk5 : k5 ≠ 0) (hk21 : k21 ≠ 0) :
    Function.Bijective (fun x => source34TwoRowRescale k5 k21 (J x)) ↔
      Function.Bijective J := by
  have hleft : Function.LeftInverse
      (source34TwoRowRescale k5⁻¹ k21⁻¹)
      (source34TwoRowRescale k5 k21) :=
    source34TwoRowRescale_inverse k5 k21 hk5 hk21
  have hright : Function.RightInverse
      (source34TwoRowRescale k5⁻¹ k21⁻¹)
      (source34TwoRowRescale k5 k21) := by
    intro v
    simpa only [inv_inv] using
      (source34TwoRowRescale_inverse k5⁻¹ k21⁻¹
        (inv_ne_zero hk5) (inv_ne_zero hk21) v)
  have hb : Function.Bijective (source34TwoRowRescale k5 k21) :=
    ⟨hleft.injective, hright.surjective⟩
  constructor
  · intro h
    constructor
    · intro x y hxy
      exact h.1 (congrArg (source34TwoRowRescale k5 k21) hxy)
    · intro v
      obtain ⟨x, hx⟩ := h.2 (source34TwoRowRescale k5 k21 v)
      exact ⟨x, hb.1 hx⟩
  · intro h
    constructor
    · intro x y hxy
      exact h.1 (hb.1 hxy)
    · intro v
      obtain ⟨w, hw⟩ := hb.2 v
      obtain ⟨x, hx⟩ := h.2 w
      exact ⟨x, by simpa only [hx] using hw⟩

#print axioms source34TwoRowRescale_comp_bijective_iff

end ProposedLocalScalarAugmented34Source
end Ventura26LiquidityAllocation
