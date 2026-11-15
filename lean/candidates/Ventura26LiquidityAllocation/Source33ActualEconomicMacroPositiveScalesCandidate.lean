import Ventura26LiquidityAllocation.Source33SixMacroLogRowNormalizationCandidate

/-!
# Economic sufficient conditions for six genuine SOURCE macro row multipliers

Python's level-to-log normalizations have derivative coefficients
  1/nextBankFace, 1/currentWage, -1
at each date of the reduced prefix root. This module uses ACTUAL
EconomicModel.localPrefixDateZeroData / localPrefixDateOneData objects
rather than unrelated symbolic positive numbers.

Strictly positive nominal bank faces and wages at both dates suffice
to prove all six coefficient nonzero conditions and hence injectivity
of the composed 33-dimensional output transformation, for any
bank and firm row-shear coefficients.

This DOES NOT establish source/Python residual identity or existence
of an allocation with those positive positions.
-/

namespace Ventura26LiquidityAllocation

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- The economics-based six Jacobian row scales at the genuine two-date
SOURCE prefix, in the order bank face / wage / household Euler. -/
noncomputable def source33MacroRowScalesOfActualDates
    (P : Primitives S) (I : InheritedState)
    (Z : LocalPrefixCoordinates) (dateOne recurrent : S)
    (tail : LocalPrefixContinuationRule) : Fin 6 → ℝ
  | 0 => 1 / (localPrefixDateZeroData P I Z dateOne).nextBankFace
  | 1 => 1 / (localPrefixDateZeroData P I Z dateOne).controls.wage
  | 2 => -1
  | 3 => 1 / (localPrefixDateOneData P Z dateOne recurrent tail).nextBankFace
  | 4 => 1 / (localPrefixDateOneData P Z dateOne recurrent tail).controls.wage
  | 5 => -1

/-- Original SOURCE positive nominal bank faces and wages imply no
degenerate macro row scales at either date. -/
theorem source33ActualDateMacroScales_all_ne_zero
    (P : Primitives S) (I : InheritedState)
    (Z : LocalPrefixCoordinates) (dateOne recurrent : S)
    (tail : LocalPrefixContinuationRule)
    (hbank0 : 0 < (localPrefixDateZeroData P I Z dateOne).nextBankFace)
    (hwage0 : 0 < (localPrefixDateZeroData P I Z dateOne).controls.wage)
    (hbank1 : 0 <
      (localPrefixDateOneData P Z dateOne recurrent tail).nextBankFace)
    (hwage1 : 0 <
      (localPrefixDateOneData P Z dateOne recurrent tail).controls.wage) :
    ∀ i : Fin 6,
      source33MacroRowScalesOfActualDates P I Z dateOne recurrent tail i ≠ 0 := by
  intro i
  fin_cases i
  · exact div_ne_zero (by norm_num) (ne_of_gt hbank0)
  · exact div_ne_zero (by norm_num) (ne_of_gt hwage0)
  · norm_num [source33MacroRowScalesOfActualDates]
  · exact div_ne_zero (by norm_num) (ne_of_gt hbank1)
  · exact div_ne_zero (by norm_num) (ne_of_gt hwage1)
  · norm_num [source33MacroRowScalesOfActualDates]

#print axioms source33ActualDateMacroScales_all_ne_zero

/-- The entire genuine SOURCE economic output-row map is injective
provided original two-date positive bank faces/wages are supplied. -/
theorem source33ActualDateFullOutputTransform_injective
    (P : Primitives S) (I : InheritedState)
    (Z : LocalPrefixCoordinates) (dateOne recurrent : S)
    (tail : LocalPrefixContinuationRule)
    (loan0 deposit0 loan1 deposit1
      rate0 quantity0 rate1 quantity1 : ℝ)
    (coeffH coeffL : ℝ)
    (hbank0 : 0 < (localPrefixDateZeroData P I Z dateOne).nextBankFace)
    (hwage0 : 0 < (localPrefixDateZeroData P I Z dateOne).controls.wage)
    (hbank1 : 0 <
      (localPrefixDateOneData P Z dateOne recurrent tail).nextBankFace)
    (hwage1 : 0 <
      (localPrefixDateOneData P Z dateOne recurrent tail).controls.wage) :
    Function.Injective
      (source33FullBankFirmMacroOutputTransform
        loan0 deposit0 loan1 deposit1
        rate0 quantity0 rate1 quantity1
        coeffH coeffL
        (source33MacroRowScalesOfActualDates P I Z dateOne recurrent tail 0)
        (source33MacroRowScalesOfActualDates P I Z dateOne recurrent tail 1)
        (source33MacroRowScalesOfActualDates P I Z dateOne recurrent tail 2)
        (source33MacroRowScalesOfActualDates P I Z dateOne recurrent tail 3)
        (source33MacroRowScalesOfActualDates P I Z dateOne recurrent tail 4)
        (source33MacroRowScalesOfActualDates P I Z dateOne recurrent tail 5)) := by
  have hn := source33ActualDateMacroScales_all_ne_zero
    P I Z dateOne recurrent tail hbank0 hwage0 hbank1 hwage1
  exact source33FullBankFirmMacroOutputTransform_injective
    loan0 deposit0 loan1 deposit1
    rate0 quantity0 rate1 quantity1 coeffH coeffL
    _ _ _ _ _ _
    (hn 0) (hn 1) (hn 2) (hn 3) (hn 4) (hn 5)

#print axioms source33ActualDateFullOutputTransform_injective

end Ventura26LiquidityAllocation
