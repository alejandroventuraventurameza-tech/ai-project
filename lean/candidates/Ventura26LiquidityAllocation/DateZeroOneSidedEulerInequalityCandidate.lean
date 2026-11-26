import Ventura26LiquidityAllocation.DateZeroOneSidedFeasibilityCandidate
import Ventura26LiquidityAllocation.RightSidedFermatCandidate
import Ventura26LiquidityAllocation.DateZeroCapitalExpectedEulerCandidate

/-!
# Source optimality implies an expected Euler INEQUALITY at binding collateral

The deviation raises current investment and reduces current consumption,
without changing loans, deposits or nominal faces. A one-sided feasible
radius follows from the robust collateral inequality with nonnegative pledge
payoff. Fermat on the positive ray gives a weak (not zero) gradient.
No structural collateralDual is assumed or identified here.
-/

namespace Ventura26LiquidityAllocation
namespace ProposedDateZeroOneSidedEulerInequality

open ProposedDateZeroCapitalDeviation
open ProposedDateZeroCapitalUtility
open ProposedDateZeroCapitalEulerDerivative
open ProposedDateZeroCapitalExpectedEuler
open ProposedDateZeroOneSidedFeasibility
open ProposedRightSidedFermat

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- The signed source first-order directional derivative is nonpositive for
    any firm whose pledge payoff does not decline with additional capital. -/
theorem firmOptimal_expectedCapitalEuler_gradient_nonpos
    (P : Primitives S) (I : InheritedState)
    (X : Allocation S) (i : FirmType)
    (hopt : FirmOptimal P I X i)
    (hcapital : ∀ h : History S 0,
      FirmHistoryAdmissible P 0 h → 0 < X.capital i 0 h)
    (hcoeff : ∀ h : History S 0,
      FirmHistoryAdmissible P 0 h → ∀ s : S,
      0 < P.tree.transition (currentState h) s →
      0 ≤ P.pledgeability i * (1 - P.depreciation) *
        (X.inflation 1 (childHistory h s) *
          X.capitalPrice 1 (childHistory h s))) :
    expectedCapitalEulerGradient P X i (firmPlanOfAllocation X i) ≤ 0 := by
  let p := firmPlanOfAllocation X i
  let f : ℝ → ℝ := fun epsilon =>
    discountedFirmUtility P (capitalDateZeroVariation P X i p epsilon)
  have hderiv : HasDerivAt f (expectedCapitalEulerGradient P X i p) 0 :=
    discountedFirmUtility_dateZeroCapital_hasDerivAt
      P I X i p hopt.1 hopt.2.1 hcapital
  obtain ⟨radius, hradius, hbound⟩ :=
    exists_right_feasible_optimality_radius
      P I X i hopt hcapital hcoeff
  have hcons0 :
      (capitalDateZeroVariation P X i p 0).consumption 0 =
        p.consumption 0 := by
    funext h
    simp
  have hcons1 :
      (capitalDateZeroVariation P X i p 0).consumption 1 =
        p.consumption 1 := by
    funext h
    simp [dateOneCapitalGain]
  have hterm0 :
      firmUtilityTerm P (capitalDateZeroVariation P X i p 0) 0 =
        firmUtilityTerm P p 0 := by
    unfold firmUtilityTerm
    rw [hcons0]
  have hterm1 :
      firmUtilityTerm P (capitalDateZeroVariation P X i p 0) 1 =
        firmUtilityTerm P p 1 := by
    unfold firmUtilityTerm
    rw [hcons1]
  have hvalue0 : f 0 = discountedFirmUtility P p := by
    have hdelta := discountedFirmUtility_capitalVariation_delta_eq
      P X i p 0 hopt.2.1
    change f 0 - discountedFirmUtility P p =
      (firmUtilityTerm P (capitalDateZeroVariation P X i p 0) 0 -
        firmUtilityTerm P p 0) +
      (firmUtilityTerm P (capitalDateZeroVariation P X i p 0) 1 -
        firmUtilityTerm P p 1) at hdelta
    rw [hterm0, hterm1] at hdelta
    linarith
  apply hasDerivAt_nonpos_of_local_right_max f
    (expectedCapitalEulerGradient P X i p) hderiv
  refine ⟨radius, hradius, ?_⟩
  intro epsilon heps hsmall
  change discountedFirmUtility P
    (capitalDateZeroVariation P X i p epsilon) ≤ f 0
  rw [hvalue0]
  exact (hbound epsilon heps hsmall).2.2

end ProposedDateZeroOneSidedEulerInequality
end Ventura26LiquidityAllocation
