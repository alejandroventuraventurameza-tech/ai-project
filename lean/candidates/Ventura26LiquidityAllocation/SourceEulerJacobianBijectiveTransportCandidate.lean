import Ventura26LiquidityAllocation.SourceEulerEconomicLinearRowmapCandidate

/-!
# Bijectivity transport for SOURCE-indexed Jacobian rowmaps

The exact 33-row Euler shear has a two-sided inverse for arbitrary real
coefficients aH and aL. This module proves that PRECOMPOSITION ON THE
OUTPUT SIDE of an arbitrary map J by this row shear preserves and
reflects bijectivity. The input type U is kept abstract so the result
is independent of a particular coordinate chart and does not smuggle
in differentiability of the economic primitives.

Applied to economic Jacobians, an additional independent proof is
required that Jtilde = (sourceEulerRowsForward aH aL) ∘ J with aH,aL
evaluated at a SOURCE root. This module does not establish that
hypothesis or actual invertibility of the SOURCE economic Jacobian.
-/

namespace Ventura26LiquidityAllocation

/-- Explicitly: the exact real SOURCE Euler row shear is bijective. -/
theorem sourceEulerRowsForward_bijective (aH aL : ℝ) :
    Function.Bijective (sourceEulerRowsForward aH aL) := by
  constructor
  · intro u v h
    have hb := congrArg (sourceEulerRowsBackward aH aL) h
    simpa only [sourceEulerRows_backward_forward] using hb
  · intro v
    exact ⟨sourceEulerRowsBackward aH aL v,
      sourceEulerRows_forward_backward aH aL v⟩

#print axioms sourceEulerRowsForward_bijective

/-- Applying the proven invertible SOURCE row operation to the output
of ANY map preserves and reflects bijectivity. In particular this
applies to a candidate 33-by-33 Jacobian map once identified. -/
theorem sourceEulerRowsForward_comp_bijective_iff
    {U : Type*} (J : U → (LocalPrefixEquation → ℝ))
    (aH aL : ℝ) :
    Function.Bijective
      (fun u => sourceEulerRowsForward aH aL (J u)) ↔
      Function.Bijective J := by
  constructor
  · intro h
    constructor
    · intro u v huv
      apply h.1
      exact congrArg (sourceEulerRowsForward aH aL) huv
    · intro v
      obtain ⟨u, hu⟩ := h.2 (sourceEulerRowsForward aH aL v)
      refine ⟨u, ?_⟩
      have hb := congrArg (sourceEulerRowsBackward aH aL) hu
      simpa only [sourceEulerRows_backward_forward] using hb
  · intro h
    constructor
    · intro u v huv
      apply h.1
      have hb := congrArg (sourceEulerRowsBackward aH aL) huv
      simpa only [sourceEulerRows_backward_forward] using hb
    · intro v
      obtain ⟨u, hu⟩ := h.2 (sourceEulerRowsBackward aH aL v)
      refine ⟨u, ?_⟩
      change sourceEulerRowsForward aH aL (J u) = v
      rw [hu, sourceEulerRows_forward_backward]

#print axioms sourceEulerRowsForward_comp_bijective_iff

/-- Conditional transport between TWO given operators: the rowmap
identity is supplied as an explicit premise. A user can instantiate
J and Jtilde with genuine SOURCE Fréchet Jacobians only after proving
that premise from the actual economic derivatives. -/
theorem sourceEulerJacobian_bijective_iff_of_rowmap
    {U : Type*}
    (J Jtilde : U → (LocalPrefixEquation → ℝ))
    (aH aL : ℝ)
    (hrow : ∀ u, Jtilde u = sourceEulerRowsForward aH aL (J u)) :
    Function.Bijective Jtilde ↔ Function.Bijective J := by
  have hf : Jtilde = (fun u => sourceEulerRowsForward aH aL (J u)) :=
    funext hrow
  rw [hf]
  exact sourceEulerRowsForward_comp_bijective_iff J aH aL

#print axioms sourceEulerJacobian_bijective_iff_of_rowmap

end Ventura26LiquidityAllocation
