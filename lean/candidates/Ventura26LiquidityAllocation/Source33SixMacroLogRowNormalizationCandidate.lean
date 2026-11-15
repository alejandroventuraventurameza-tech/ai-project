import Ventura26LiquidityAllocation.Source33CombinedBankFirmEulerShearCandidate

/-!
# Six SOURCE-level to Python-log Jacobian row scalings

SOURCE bank-face renewal, worker-labor, and household Euler
conditions are expressed in LEVEL form; the original Python 33-row
system uses logarithmic ratios for each of these three equations at
both dates. Their Jacobians at a COMMON POSITIVE ROOT differ by
nonzero diagonal coefficients. Those coefficients are supplied as
parameters, NOT silently inferred from primitive/source equality.

This module formalizes the exact six-row diagonal linear map, its
nonzero coefficients condition, its preservation of the zero vector,
and its injectivity. The Lean statement is genuine linear algebra
on 33 source-labelled economic residual coordinates, not an
assertion that the full Python evaluator equals transformed SOURCE.
-/

namespace Ventura26LiquidityAllocation

/-- Six economic normalizations (indices in original Python order).
At dates zero and one respectively: bank equity, worker labor,
household Euler. All other rows are unchanged. -/
def source33MacroNormalizationCoefficient
    (b0 w0 e0 b1 w1 e1 : ℝ) (i : Fin 33) : ℝ :=
  if i = 6 then b0 else
  if i = 9 then w0 else
  if i = 10 then e0 else
  if i = 22 then b1 else
  if i = 25 then w1 else
  if i = 26 then e1 else 1

def source33SixMacroNormalization
    (b0 w0 e0 b1 w1 e1 : ℝ)
    (v : Fin 33 → ℝ) : Fin 33 → ℝ :=
  fun i => source33MacroNormalizationCoefficient
    b0 w0 e0 b1 w1 e1 i * v i

theorem source33MacroNormalizationCoefficient_ne_zero
    (b0 w0 e0 b1 w1 e1 : ℝ)
    (hb0 : b0 ≠ 0) (hw0 : w0 ≠ 0) (he0 : e0 ≠ 0)
    (hb1 : b1 ≠ 0) (hw1 : w1 ≠ 0) (he1 : e1 ≠ 0)
    (i : Fin 33) :
    source33MacroNormalizationCoefficient b0 w0 e0 b1 w1 e1 i ≠ 0 := by
  fin_cases i <;>
    simp [source33MacroNormalizationCoefficient,
      hb0, hw0, he0, hb1, hw1, he1]

/-- The six macroscale map cannot create spurious roots as long as
all six economically determined diagonal coefficients are nonzero. -/
theorem source33SixMacroNormalization_zero_iff
    (b0 w0 e0 b1 w1 e1 : ℝ)
    (hb0 : b0 ≠ 0) (hw0 : w0 ≠ 0) (he0 : e0 ≠ 0)
    (hb1 : b1 ≠ 0) (hw1 : w1 ≠ 0) (he1 : e1 ≠ 0)
    (v : Fin 33 → ℝ) :
    source33SixMacroNormalization b0 w0 e0 b1 w1 e1 v = 0 ↔
      v = 0 := by
  constructor
  · intro h
    funext i
    have hi := congrFun h i
    change source33MacroNormalizationCoefficient
      b0 w0 e0 b1 w1 e1 i * v i = 0 at hi
    exact (mul_eq_zero.mp hi).resolve_left
      (source33MacroNormalizationCoefficient_ne_zero
        b0 w0 e0 b1 w1 e1 hb0 hw0 he0 hb1 hw1 he1 i)
  · intro h
    subst v
    funext i
    simp [source33SixMacroNormalization]

#print axioms source33SixMacroNormalization_zero_iff

/-- Each macro row scaling is also injective on arbitrary 33
residual vectors, not merely on the zero set. -/
theorem source33SixMacroNormalization_injective
    (b0 w0 e0 b1 w1 e1 : ℝ)
    (hb0 : b0 ≠ 0) (hw0 : w0 ≠ 0) (he0 : e0 ≠ 0)
    (hb1 : b1 ≠ 0) (hw1 : w1 ≠ 0) (he1 : e1 ≠ 0) :
    Function.Injective
      (source33SixMacroNormalization b0 w0 e0 b1 w1 e1) := by
  intro v w h
  funext i
  have hi := congrFun h i
  change source33MacroNormalizationCoefficient
    b0 w0 e0 b1 w1 e1 i * v i =
    source33MacroNormalizationCoefficient
      b0 w0 e0 b1 w1 e1 i * w i at hi
  have hz : source33MacroNormalizationCoefficient
      b0 w0 e0 b1 w1 e1 i * (v i - w i) = 0 := by
    calc
      source33MacroNormalizationCoefficient
        b0 w0 e0 b1 w1 e1 i * (v i - w i) =
          source33MacroNormalizationCoefficient
            b0 w0 e0 b1 w1 e1 i * v i -
          source33MacroNormalizationCoefficient
            b0 w0 e0 b1 w1 e1 i * w i := by ring
      _ = 0 := sub_eq_zero.mpr hi
  exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left
    (source33MacroNormalizationCoefficient_ne_zero
      b0 w0 e0 b1 w1 e1 hb0 hw0 he0 hb1 hw1 he1 i))

#print axioms source33SixMacroNormalization_injective

end Ventura26LiquidityAllocation
