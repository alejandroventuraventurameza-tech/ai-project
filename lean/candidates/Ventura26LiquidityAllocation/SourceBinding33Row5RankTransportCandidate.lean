import Ventura26LiquidityAllocation.SourceBindingSlackRowScalingCandidate

/-!
# Exact 33-row invertibility transport under normalized binding-L row scaling

A single nonzero scalar rescaling of the SOURCE binding-L row
cannot alter injectivity, surjectivity, or bijectivity of any
33-output Jacobian. This general finite-dimensional result is
intended for the economic SOURCE original-to-modified binding
bridge.

The separately proposed SourceBindingSlackRowFrechetCandidate
will prove the exact row-5 derivative scaling at a genuine
binding root. An identification of the other 32 genuine SOURCE
rows and the zero-policy primitive intervention is still needed
before claiming a full economic Jacobian factorization.
-/

namespace Ventura26LiquidityAllocation

/-- Rescale only the actual binding-L output row (index 5) in
the 33-equation SOURCE log-coordinate order. -/
noncomputable def sourceBindingRow5Rescale
    (k : ℝ) (v : Fin 33 → ℝ) : Fin 33 → ℝ :=
  fun row => if row = (5 : Fin 33) then k * v row else v row

/-- The inverse row rescaling exactly cancels the forward map
whenever the scalar factor is nonzero. -/
theorem sourceBindingRow5Rescale_leftInverse
    (k : ℝ) (hk : k ≠ 0) :
    Function.LeftInverse
      (sourceBindingRow5Rescale k⁻¹)
      (sourceBindingRow5Rescale k) := by
  intro v
  funext row
  by_cases hrow : row = (5 : Fin 33)
  · subst row
    simp [sourceBindingRow5Rescale, hk, mul_assoc]
  · simp [sourceBindingRow5Rescale, hrow]

#print axioms sourceBindingRow5Rescale_leftInverse

/-- The same inverse works in the opposite order. -/
theorem sourceBindingRow5Rescale_rightInverse
    (k : ℝ) (hk : k ≠ 0) :
    Function.RightInverse
      (sourceBindingRow5Rescale k⁻¹)
      (sourceBindingRow5Rescale k) := by
  intro v
  funext row
  by_cases hrow : row = (5 : Fin 33)
  · subst row
    simp [sourceBindingRow5Rescale, hk, mul_assoc]
  · simp [sourceBindingRow5Rescale, hrow]

#print axioms sourceBindingRow5Rescale_rightInverse

/-- A single nonzero SOURCE row-5 scaling is a bijection of the
whole 33-dimensional residual-output space. -/
theorem sourceBindingRow5Rescale_bijective
    (k : ℝ) (hk : k ≠ 0) :
    Function.Bijective (sourceBindingRow5Rescale k) :=
  ⟨(sourceBindingRow5Rescale_leftInverse k hk).injective,
   (sourceBindingRow5Rescale_rightInverse k hk).surjective⟩

#print axioms sourceBindingRow5Rescale_bijective

/-- The exact set of possible 33-row output Jacobians retains
bijectivity after a single nonzero row rescaling, for arbitrary
source domain E. No finite-difference matrices are assumed. -/
theorem sourceBindingRow5Rescale_comp_bijective_iff
    {E : Type*} (k : ℝ) (hk : k ≠ 0)
    (J : E → Fin 33 → ℝ) :
    Function.Bijective (fun x => sourceBindingRow5Rescale k (J x)) ↔
      Function.Bijective J := by
  have hscale := sourceBindingRow5Rescale_bijective k hk
  constructor
  · intro h
    constructor
    · intro x y hxy
      apply h.1
      exact congrArg (sourceBindingRow5Rescale k) hxy
    · intro v
      obtain ⟨x, hx⟩ := h.2 (sourceBindingRow5Rescale k v)
      exact ⟨x, hscale.1 hx⟩
  · intro h
    constructor
    · intro x y hxy
      exact h.1 (hscale.1 hxy)
    · intro v
      obtain ⟨w, hw⟩ := hscale.2 v
      obtain ⟨x, hx⟩ := h.2 w
      refine ⟨x, ?_⟩
      simpa only [hx] using hw

#print axioms sourceBindingRow5Rescale_comp_bijective_iff

/-- A conditional 33x33 SOURCE rank transport gate. Once the
actual original and modified economic Jacobian actions are shown
to differ ONLY by the row-5 rescaling at a genuine binding root,
their bijectivity is equivalent. The row action equality hrow
is a SOURCE semantic obligation, NOT a numerical surrogate. -/
theorem sourceBinding33Jacobian_bijective_iff_of_exact_row5
    (Joriginal Jmodified : (Fin 33 → ℝ) → Fin 33 → ℝ)
    (GammaL : ℝ) (hGamma : GammaL ≠ 0)
    (hrow : ∀ direction : Fin 33 → ℝ,
      Jmodified direction =
        sourceBindingRow5Rescale (-(GammaL⁻¹)) (Joriginal direction)) :
    Function.Bijective Jmodified ↔ Function.Bijective Joriginal := by
  have hscale : -(GammaL⁻¹) ≠ 0 := by simp [hGamma]
  have heq : Jmodified =
      (fun direction => sourceBindingRow5Rescale (-(GammaL⁻¹))
        (Joriginal direction)) := by
    funext direction
    exact hrow direction
  rw [heq]
  exact sourceBindingRow5Rescale_comp_bijective_iff
    (-(GammaL⁻¹)) hscale Joriginal

#print axioms sourceBinding33Jacobian_bijective_iff_of_exact_row5

end Ventura26LiquidityAllocation
