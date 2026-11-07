import Ventura26LiquidityAllocation.DateZeroJointBindingNeighborhoodCandidate
import Ventura26LiquidityAllocation.DateZeroJointTangentExpectedDerivativeCandidate

/-!
# Genuine binding joint capital-loan stationarity from source FirmOptimal

For the deterministic source calendar with an active date-zero collateral
constraint, the true joint plan dk=R*epsilon, db=Gamma*epsilon is feasible
for all sufficiently small positive AND negative epsilon. The original
infinite-horizon objective is exactly differentiable along this direction.
Fermat therefore forces its EXPECTED marginal gradient to zero.

This derives the shared capital-loan tangent first-order condition FROM
FirmOptimal, not as a KKT assumption. The final interface identifying a
specific original Allocation.collateralDual remains a separate obligation.
-/

namespace Ventura26LiquidityAllocation
namespace ProposedDateZeroJointBindingFermat

open Filter Topology
open ProposedDateZeroJointCapitalLoanDeviation
open ProposedDateZeroJointCapitalLoanDelta
open ProposedDateZeroJointCapitalLoanUtility
open ProposedDateZeroJointBindingNeighborhood
open ProposedDateZeroJointTangentExpectedDerivative
open ProposedProposition42KKTIdentification

variable {S : Type*} [Fintype S] [DecidableEq S]

theorem firmOptimal_sourceCalendar_binding_jointTangent_gradient_zero
    (P : Primitives S) (I : InheritedState)
    (X : Allocation S) (i : FirmType)
    (dateOne recurrent : S)
    (hcalendar : DeterministicBridgeCalendar P dateOne recurrent)
    (hopt : FirmOptimal P I X i)
    (hbinding : DateZeroBindingBorrower P X i)
    (hcapital : ∀ h : History S 0,
      FirmHistoryAdmissible P 0 h → 0 < X.capital i 0 h) :
    jointTangentExpectedGradient P X i (firmPlanOfAllocation X i)
      (X.loanRate 0 (rootHistory P.tree))
      (capitalEulerCollateralUnit P X i 0
        (rootHistory P.tree) dateOne) = 0 := by
  let p : FirmPlan S := firmPlanOfAllocation X i
  let R : ℝ := X.loanRate 0 (rootHistory P.tree)
  let Gamma : ℝ := capitalEulerCollateralUnit P X i 0
    (rootHistory P.tree) dateOne
  have hderiv :
      HasDerivAt
        (fun epsilon : ℝ =>
          discountedFirmUtility P
            (jointDateZeroVariation P X i p
              (R * epsilon) (Gamma * epsilon)))
        (jointTangentExpectedGradient P X i p R Gamma) 0 :=
    discountedFirmUtility_jointTangent_hasDerivAt
      P I X i p R Gamma hopt.1 hopt.2.1 hcapital
  obtain ⟨radius, hradius, hbound⟩ :=
    exists_twoSided_binding_jointTangent_radius
      P I X i dateOne recurrent hcalendar hopt hbinding hcapital
  have hcons0 :
      (jointDateZeroVariation P X i p
        (R * (0 : ℝ)) (Gamma * 0)).consumption 0 =
          p.consumption 0 := by
    funext h
    simp
  have hcons1 :
      (jointDateZeroVariation P X i p
        (R * (0 : ℝ)) (Gamma * 0)).consumption 1 =
          p.consumption 1 := by
    funext h
    simp [dateOneJointGain, ProposedDateZeroCapitalDeviation.dateOneCapitalGain]
  have hterm0 :
      firmUtilityTerm P (jointDateZeroVariation P X i p
        (R * (0 : ℝ)) (Gamma * 0)) 0 = firmUtilityTerm P p 0 := by
    unfold firmUtilityTerm
    rw [hcons0]
  have hterm1 :
      firmUtilityTerm P (jointDateZeroVariation P X i p
        (R * (0 : ℝ)) (Gamma * 0)) 1 = firmUtilityTerm P p 1 := by
    unfold firmUtilityTerm
    rw [hcons1]
  have hvalue0 :
      discountedFirmUtility P
        (jointDateZeroVariation P X i p
          (R * (0 : ℝ)) (Gamma * 0)) =
      discountedFirmUtility P p := by
    have hdelta := discountedFirmUtility_jointVariation_delta_eq
      P X i p (R * (0 : ℝ)) (Gamma * 0) hopt.2.1
    rw [hterm0, hterm1] at hdelta
    linarith
  have hball : Set.Ioo (-radius) radius ∈ 𝓝 (0 : ℝ) := by
    exact isOpen_Ioo.mem_nhds ⟨by linarith, by linarith⟩
  have hmax : IsLocalMax (fun epsilon : ℝ =>
      discountedFirmUtility P
        (jointDateZeroVariation P X i p
          (R * epsilon) (Gamma * epsilon))) 0 := by
    change ∀ᶠ epsilon : ℝ in 𝓝 (0 : ℝ),
      discountedFirmUtility P
        (jointDateZeroVariation P X i p
          (R * epsilon) (Gamma * epsilon)) ≤
      discountedFirmUtility P
        (jointDateZeroVariation P X i p
          (R * (0 : ℝ)) (Gamma * 0))
    filter_upwards [hball] with epsilon hepsilon
    rw [hvalue0]
    have hlocal : JointCapitalLoanVariationLocalBounds P X i p
        (R * epsilon) (Gamma * epsilon) := by
      exact hbound epsilon (abs_lt.mpr hepsilon)
    exact firmOptimal_dominates_jointDeviation
      P I X i (R * epsilon) (Gamma * epsilon) hopt hlocal
  exact hmax.hasDerivAt_eq_zero hderiv

end ProposedDateZeroJointBindingFermat
end Ventura26LiquidityAllocation
