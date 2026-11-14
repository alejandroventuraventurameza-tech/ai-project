import Ventura26LiquidityAllocation.SourcePythonLogResidualDirectionalJacobianCandidate

/-!
# Rank preservation under the SIX required SOURCE -> Python row scalings

Original Python 33-row prefixes place their date-zero bank/labor/Euler
remaining residuals at zero-based positions 6,9,10 and the date-one
counterparts at 22,25,26. Their original SOURCE counterparts use
level/one-minus-ratio normalizations, so at an economically common
positive root the required directional Jacobian row multipliers are

  6  -> 1 / bankRolloverTargetAtDateZero
  9  -> 1 / laborSupplyTargetAtDateZero
  10 -> -1
  22 -> 1 / bankRolloverTargetAtDateOne
  25 -> 1 / laborSupplyTargetAtDateOne
  26 -> -1

and the multiplier of each other row is one IF that other row is
algebraically identified between the ORIGINAL economic operators.

This module demonstrates that all six row scalings are nonzero on
the explicit positive economic chart, hence cannot change the
injectivity (full column rank) of ANY 33-output Jacobian map.
It does NOT prove the other 27 row identities or show that the
whole Python 33x33 derivative is the six-row scaled SOURCE Jacobian,
nor prove existence of any true SOURCE root.
-/

namespace Ventura26LiquidityAllocation

/-- Zero-based positions of the six genuine SOURCE/Python
row-normalization differences at the two finite-prefix dates. -/
noncomputable def sourceSixLogRowScale
    (bank0 labor0 bank1 labor1 : ℝ) (i : Fin 33) : ℝ :=
  if i = 6 then (bank0)⁻¹
  else if i = 9 then (labor0)⁻¹
  else if i = 10 then -1
  else if i = 22 then (bank1)⁻¹
  else if i = 25 then (labor1)⁻¹
  else if i = 26 then -1
  else 1

/-- Diagonal row action on a 33-dimensional residual or on one
directional Jacobian column. -/
noncomputable def sourceSixLogRowReweight
    (bank0 labor0 bank1 labor1 : ℝ)
    (v : Fin 33 → ℝ) : Fin 33 → ℝ :=
  fun i => sourceSixLogRowScale bank0 labor0 bank1 labor1 i * v i

/-- The row multiplier is never zero under the economic domain
positivity assumptions of all four level denominators. -/
theorem sourceSixLogRowScale_ne_zero
    (bank0 labor0 bank1 labor1 : ℝ)
    (hbank0 : 0 < bank0) (hlabor0 : 0 < labor0)
    (hbank1 : 0 < bank1) (hlabor1 : 0 < labor1)
    (i : Fin 33) :
    sourceSixLogRowScale bank0 labor0 bank1 labor1 i ≠ 0 := by
  classical
  unfold sourceSixLogRowScale
  split_ifs <;> (first | positivity | norm_num)

#print axioms sourceSixLogRowScale_ne_zero

/-- A nonzero diagonal reweighting is injective, regardless of the
numeric value of the underlying actual economic Jacobian. -/
theorem sourceSixLogRowReweight_injective
    (bank0 labor0 bank1 labor1 : ℝ)
    (hbank0 : 0 < bank0) (hlabor0 : 0 < labor0)
    (hbank1 : 0 < bank1) (hlabor1 : 0 < labor1) :
    Function.Injective
      (sourceSixLogRowReweight bank0 labor0 bank1 labor1) := by
  intro v w hvw
  funext i
  have hi := congrFun hvw i
  change sourceSixLogRowScale bank0 labor0 bank1 labor1 i * v i =
    sourceSixLogRowScale bank0 labor0 bank1 labor1 i * w i at hi
  exact mul_left_cancel₀
    (sourceSixLogRowScale_ne_zero bank0 labor0 bank1 labor1
      hbank0 hlabor0 hbank1 hlabor1 i) hi

#print axioms sourceSixLogRowReweight_injective

/-- The full-column-rank condition is invariant to all SIX
identified positive-domain SOURCE/Python normalizations, provided
that the full economic Jacobian relation is independently established.
The theorem is valid for any input type and any 33-output map. -/
theorem sourceSixLogRowReweight_injective_iff
    {X : Type*} (J : X → (Fin 33 → ℝ))
    (bank0 labor0 bank1 labor1 : ℝ)
    (hbank0 : 0 < bank0) (hlabor0 : 0 < labor0)
    (hbank1 : 0 < bank1) (hlabor1 : 0 < labor1) :
    Function.Injective
      (fun x => sourceSixLogRowReweight
        bank0 labor0 bank1 labor1 (J x)) ↔
    Function.Injective J := by
  constructor
  · intro hJ a b hab
    apply hJ
    rw [hab]
  · intro hJ a b hab
    apply hJ
    exact (sourceSixLogRowReweight_injective
      bank0 labor0 bank1 labor1
      hbank0 hlabor0 hbank1 hlabor1) hab

#print axioms sourceSixLogRowReweight_injective_iff

end Ventura26LiquidityAllocation
