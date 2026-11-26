import Ventura26LiquidityAllocation.SourceInstalledPythonBankEconomicExposureCandidate

/-!
# Genuine SOURCE 33-coordinate two-date stock/flow timing identities

The reduced 33-dimensional coordinates are not arbitrary rows. The
original EconomicModel.localPrefixDateZeroData and
EconomicModel.localPrefixDateOneData carry the SAME physical
capital, firm nominal face, bank nominal face, reserve-rate and
reserve-quantity state from the end of date zero to the beginning
of date one. The next controls at date zero are exactly the current
controls at date one.

These are literal definitional equalities of the actual SOURCE model,
valid for all admissible Primitives, inherited states, prefix charts
and continuation rules. They are a necessary but not sufficient
element of a SOURCE/Python economic coordinate equivalence.
-/

namespace Ventura26LiquidityAllocation

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- The seven state coordinates in the original SOURCE prefix have
consistent date-zero/date-one handoff: two capitals, two nominal
faces, one bank face, realized reserve rate and reserves quantity. -/
theorem sourceActualPrefix_7state_twoDateTiming
    (P : Primitives S) (I : InheritedState)
    (Z : LocalPrefixCoordinates) (dateOne recurrent : S)
    (tail : LocalPrefixContinuationRule) :
    (∀ i : FirmType,
      (localPrefixDateZeroData P I Z dateOne).nextCapital i =
        (localPrefixDateOneData P Z dateOne recurrent tail).currentCapital i) ∧
    (∀ i : FirmType,
      (localPrefixDateZeroData P I Z dateOne).nextFace i =
        (localPrefixDateOneData P Z dateOne recurrent tail).inheritedFace i) ∧
    (localPrefixDateZeroData P I Z dateOne).nextBankFace =
      (localPrefixDateOneData P Z dateOne recurrent tail).currentBankFace ∧
    (localPrefixDateZeroData P I Z dateOne).currentReserveRate =
      (localPrefixDateOneData P Z dateOne recurrent tail).lagReserveRate ∧
    (localPrefixDateZeroData P I Z dateOne).currentReservesPre =
      (localPrefixDateOneData P Z dateOne recurrent tail).lagReservesPre ∧
    (localPrefixDateZeroData P I Z dateOne).nextControls =
      (localPrefixDateOneData P Z dateOne recurrent tail).controls := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    cases i <;> rfl
  · intro i
    cases i <;> rfl
  · rfl
  · rfl
  · rfl
  · rfl

#print axioms sourceActualPrefix_7state_twoDateTiming

end Ventura26LiquidityAllocation
