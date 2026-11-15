import Ventura26LiquidityAllocation.SourceBankTwoPolicyResidualsCandidate

/-!
# Concrete SOURCE reserve/deposit-ratio identification

This file connects the abstract bank multiplier candidate with the
literal SOURCE EconomicModel reserve/deposit ratio. No Python formula
identification, numerical root, or structural IRF is asserted.
-/

namespace Ventura26LiquidityAllocation

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- The rate-dependent abstract ratio evaluated at the REALIZED
SOURCE reserve rate is definitionally equal to the ORIGINAL SOURCE
reserve/deposit ratio (no economic approximation). -/
theorem sourceBankRatioAtRealized_eq_SOURCE
    (P : Primitives S) (data : LocalPrefixDateData) :
    sourceBankRatioAtRate
        data.reserveRequirement
        data.controls.depositRate
        (localPrefixMeanAbsolutePaymentShock P *
          (1 - data.controls.tightness) /
            (1 + data.controls.tightness))
        data.currentReserveRate =
      localPrefixReserveDepositRatio P data := by
  unfold sourceBankRatioAtRate localPrefixReserveDepositRatio
  ring

#print axioms sourceBankRatioAtRealized_eq_SOURCE

/-- The same exact identification holds for the inverse-ratio
bank multiplier; SOURCE division is not assumed to be economically
valid without a separate nonzero/positive-ratio hypothesis. -/
theorem sourceBankMultiplierAtRealized_eq_SOURCE
    (P : Primitives S) (data : LocalPrefixDateData) :
    sourceBankMultiplierAtRate
        data.reserveRequirement
        data.controls.depositRate
        (localPrefixMeanAbsolutePaymentShock P *
          (1 - data.controls.tightness) /
            (1 + data.controls.tightness))
        data.currentReserveRate =
      1 / localPrefixReserveDepositRatio P data - 1 := by
  unfold sourceBankMultiplierAtRate
  rw [sourceBankRatioAtRealized_eq_SOURCE P data]

#print axioms sourceBankMultiplierAtRealized_eq_SOURCE

end Ventura26LiquidityAllocation
