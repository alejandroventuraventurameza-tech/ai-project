import Ventura26LiquidityAllocation.Proposition42PrimalSeparationCandidate

/-!
# Structural collateral multiplier identification given a capital Euler KKT row

Economic role:
  q_t - M_{t,t+1} (MPK_{t+1}+(1-delta)q_{t+1})
  - mu_t theta_i (1-delta) Pi_{t+1} q_{t+1} = 0.

When the collateral coefficient is nonzero, this equation determines
the structural collateralDual uniquely FROM THE SAME PRIMAL DATA.

Caveat: CompetitiveEquilibrium does not require localFirmCapitalEulerResidual=0.
Theorems here are conditional on the actual Euler residual equations. They DO
NOT derive KKT from infinite-horizon optimality or establish source existence.
They provide the precise missing interface for that future proof.

No source/checkpoint edits, no sorry/admit or added axioms.
-/

namespace Ventura26LiquidityAllocation
namespace ProposedProposition42KKTIdentification

open ProposedContinuationContractAudit

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- The collateral unit appearing in the literal source capital Euler row. -/
noncomputable def capitalEulerCollateralUnit
    (P : Primitives S) (X : Allocation S) (i : FirmType)
    (t : ℕ) (h : History S t) (s : S) : ℝ :=
  P.pledgeability i * (1 - P.depreciation) *
    X.inflation (t + 1) (childHistory h s) *
    X.capitalPrice (t + 1) (childHistory h s)

/-- All terms of the capital Euler row that are independent of collateralDual. -/
noncomputable def capitalEulerPrimalGap
    (P : Primitives S) (X : Allocation S) (i : FirmType)
    (t : ℕ) (h : History S t) (s : S) : ℝ :=
  let hnext := childHistory h s
  let sdf := P.entrepreneurDiscount *
    crraMarginal P.entrepreneurRiskAversion (X.firmConsumption i (t + 1) hnext) /
      crraMarginal P.entrepreneurRiskAversion (X.firmConsumption i t h)
  let marginalProduct := X.inputPrice (t + 1) hnext *
    (P.aggregateProductivity s * P.productivity i) * P.alpha *
    (X.capital i t h) ^ (P.alpha - 1) *
    (X.labor i (t + 1) hnext) ^ P.beta
  X.capitalPrice t h -
    sdf * (marginalProduct + (1 - P.depreciation) * X.capitalPrice (t + 1) hnext)

/-- Exact decomposition of the source row, without any economic assumption. -/
theorem capitalEulerResidual_eq_primalGap_sub_dual
    (P : Primitives S) (X : Allocation S) (i : FirmType)
    (t : ℕ) (h : History S t) (s : S) :
    localFirmCapitalEulerResidual P X i t h s =
      capitalEulerPrimalGap P X i t h s -
        X.collateralDual i t h * capitalEulerCollateralUnit P X i t h s := by
  rfl

/-- Changing ONLY the multiplier does not change the left-hand primal gap. -/
theorem capitalEulerPrimalGap_replaceDual
    (P : Primitives S) (X : Allocation S)
    (dual : FirmType → AdaptedProcess S)
    (i : FirmType) (t : ℕ) (h : History S t) (s : S) :
    capitalEulerPrimalGap P (replaceCollateralDual X dual) i t h s =
      capitalEulerPrimalGap P X i t h s := by
  rfl

theorem capitalEulerCollateralUnit_replaceDual
    (P : Primitives S) (X : Allocation S)
    (dual : FirmType → AdaptedProcess S)
    (i : FirmType) (t : ℕ) (h : History S t) (s : S) :
    capitalEulerCollateralUnit P (replaceCollateralDual X dual) i t h s =
      capitalEulerCollateralUnit P X i t h s := by
  rfl

/-- Standard economic positivity implies a strictly positive collateral unit. -/
theorem capitalEulerCollateralUnit_pos
    (P : Primitives S) (X : Allocation S) (i : FirmType)
    (t : ℕ) (h : History S t) (s : S)
    (htheta : 0 < P.pledgeability i)
    (hdelta : P.depreciation < 1)
    (hinfl : 0 < X.inflation (t + 1) (childHistory h s))
    (hq : 0 < X.capitalPrice (t + 1) (childHistory h s)) :
    0 < capitalEulerCollateralUnit P X i t h s := by
  unfold capitalEulerCollateralUnit
  exact mul_pos (mul_pos (mul_pos htheta (sub_pos.mpr hdelta)) hinfl) hq

private theorem linear_multiplier_unique
    (A c x y : ℝ) (hc : c ≠ 0)
    (hx : A - x * c = 0) (hy : A - y * c = 0) :
    x = y := by
  have hprod : (x - y) * c = 0 := by nlinarith [hx, hy]
  rcases mul_eq_zero.mp hprod with hxy | hc0
  · linarith
  · exact (hc hc0).elim

/-- If the ORIGINAL source capital Euler row holds for two different
    multiplier carriers with identical primals, they must agree at this node. -/
theorem capitalEuler_dual_unique_of_same_primal
    (P : Primitives S) (X : Allocation S)
    (dual : FirmType → AdaptedProcess S)
    (i : FirmType) (t : ℕ) (h : History S t) (s : S)
    (horiginal : localFirmCapitalEulerResidual P X i t h s = 0)
    (hmodified : localFirmCapitalEulerResidual P
      (replaceCollateralDual X dual) i t h s = 0)
    (hunit : capitalEulerCollateralUnit P X i t h s ≠ 0) :
    X.collateralDual i t h = dual i t h := by
  have h0 : capitalEulerPrimalGap P X i t h s -
    X.collateralDual i t h * capitalEulerCollateralUnit P X i t h s = 0 := by
    rw [capitalEulerResidual_eq_primalGap_sub_dual] at horiginal
    exact horiginal
  have h1 : capitalEulerPrimalGap P X i t h s -
    dual i t h * capitalEulerCollateralUnit P X i t h s = 0 := by
    rw [capitalEulerResidual_eq_primalGap_sub_dual] at hmodified
    change capitalEulerPrimalGap P X i t h s -
      dual i t h * capitalEulerCollateralUnit P X i t h s = 0 at hmodified
    exact hmodified
  exact linear_multiplier_unique _ _ _ _ hunit h0 h1

/-- The structural field is fully identified if both candidates satisfy
    their source capital Euler row at every node and the collateral coefficient
    is nonzero at the selected successor. NO such KKT hypothesis is derived
    from CompetitiveEquilibrium here. -/
theorem entire_collateralDual_identified_of_euler
    (P : Primitives S) (X : Allocation S)
    (dual : FirmType → AdaptedProcess S)
    (hX : ∀ i t h,
      localFirmCapitalEulerResidual P X i t h P.tree.initial = 0)
    (hY : ∀ i t h,
      localFirmCapitalEulerResidual P (replaceCollateralDual X dual)
        i t h P.tree.initial = 0)
    (hunit : ∀ i t h,
      capitalEulerCollateralUnit P X i t h P.tree.initial ≠ 0) :
    replaceCollateralDual X dual = X := by
  have heq : dual = X.collateralDual := by
    funext i t h
    exact (capitalEuler_dual_unique_of_same_primal P X dual i t h P.tree.initial
      (hX i t h) (hY i t h) (hunit i t h)).symm
  rw [heq]
  rfl

end ProposedProposition42KKTIdentification
end Ventura26LiquidityAllocation
