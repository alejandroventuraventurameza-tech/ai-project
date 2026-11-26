import Ventura26LiquidityAllocation.SourceEconomic33PythonRowPermutationShearCandidate
import Ventura26LiquidityAllocation.SourceActualDateOneCommonPledgeCollateralFactorCandidate

/-!
# Certified exact two-firm Euler row shear on all 33 SOURCE rows

At a common-pledge root the original SOURCE date-one Euler rows
differ from the Python-coordinate rows by multiples of the common
pledge row. This module encodes that pure algebraic output
transformation for arbitrary REAL shear factors, and proves it
invertible without any numerical Jacobian assumption.

Combining it with the previously certified two-date bank row shear
gives an injective SOURCE output coordinate transformation. This is
a theorem about 33-row maps on genuine SOURCE residual vectors; it
does NOT assert that the actual Python residual or Jacobian equals
the transformed SOURCE object. Six SOURCE-level-to-Python-log
normalizations also remain for the complete coordinate certificate.
-/

namespace Ventura26LiquidityAllocation

/-- The two date-one firm Euler rows (original Python row order)
are updated by the common terminal pledge equation at index 21. -/
def source33TwoFirmEulerShear
    (coeffH coeffL : ℝ) (v : Fin 33 → ℝ) : Fin 33 → ℝ :=
  fun i =>
    if i = 18 then v i + coeffH * v 21
    else if i = 20 then v i + coeffL * v 21
    else v i

/-- Firm shear is inverted exactly by negating both coefficients. -/
theorem source33TwoFirmEulerShear_undo
    (coeffH coeffL : ℝ) (v : Fin 33 → ℝ) :
    source33TwoFirmEulerShear (-coeffH) (-coeffL)
      (source33TwoFirmEulerShear coeffH coeffL v) = v := by
  funext i
  fin_cases i <;> simp [source33TwoFirmEulerShear] <;> ring

#print axioms source33TwoFirmEulerShear_undo

theorem source33TwoFirmEulerShear_injective
    (coeffH coeffL : ℝ) :
    Function.Injective (source33TwoFirmEulerShear coeffH coeffL) := by
  intro v w heq
  have h := congrArg
    (source33TwoFirmEulerShear (-coeffH) (-coeffL)) heq
  simpa only [source33TwoFirmEulerShear_undo] using h

/-- The actual already-certified bank output shear composed with
the two-firm pledge-coordinate shear: both act on all 33 rows. -/
def source33BankAndFirmOutputShear
    (loan0 deposit0 loan1 deposit1
      rate0 quantity0 rate1 quantity1 : ℝ)
    (coeffH coeffL : ℝ)
    (v : Fin 33 → ℝ) : Fin 33 → ℝ :=
  source33TwoFirmEulerShear coeffH coeffL
    (sourceTwoDateBankFiveRowShear
      loan0 deposit0 loan1 deposit1
      rate0 quantity0 rate1 quantity1 v)

/-- A genuine combined banking and enterprise output shear is
injective for all coefficients, without nonsingularity assumptions
on the economic 33-dimensional derivative itself. -/
theorem source33BankAndFirmOutputShear_injective
    (loan0 deposit0 loan1 deposit1
      rate0 quantity0 rate1 quantity1 : ℝ)
    (coeffH coeffL : ℝ) :
    Function.Injective
      (source33BankAndFirmOutputShear
        loan0 deposit0 loan1 deposit1
        rate0 quantity0 rate1 quantity1 coeffH coeffL) := by
  intro v w h
  apply sourceTwoDateBankFullRowShear_injective
    loan0 deposit0 loan1 deposit1 rate0 quantity0 rate1 quantity1
  exact source33TwoFirmEulerShear_injective coeffH coeffL h

#print axioms source33BankAndFirmOutputShear_injective

end Ventura26LiquidityAllocation
