import Ventura26LiquidityAllocation.SourceFundingDualStationaryScalarZeroCandidate

/-!
# SOURCE 34 boundary: exact elimination of the L funding dual

On the explicit stationary sigmaE=1 positive domain, the final SOURCE
funding-dual equation has a UNIQUE value of loan-rate log-coordinate
15 given the other log coordinates. Substituting this analytic value
eliminates the 34th equation exactly.

The existential full SOURCE 34-root problem is therefore equivalent
to a 33-row economic residual problem evaluated on this dual-zero
surface. This is an algebraic dimension reduction and does NOT assert
that the reduced 33-row problem has a root or that the resulting point
satisfies full dynamic KKT equilibrium.
-/

namespace Ventura26LiquidityAllocation

open ProposedLocalScalarAugmented34Source
open ProposedLocalScalarEconomicSlice

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- Unique loan-rate coordinate solving a reciprocal-exponential scalar. -/
theorem sourceDual_loanLog_scalar_zero_iff
    (R rhs t : ℝ) (hR : 0 < R) (hrhs : 0 < rhs) :
    1 / (R * Real.exp t) - rhs = 0 ↔
      t = Real.log (1 / (R * rhs)) := by
  have hRne : R ≠ 0 := ne_of_gt hR
  have hrhsne : rhs ≠ 0 := ne_of_gt hrhs
  have he : Real.exp t ≠ 0 := Real.exp_ne_zero _
  constructor
  · intro hz
    have hpoint : 1 / (R * Real.exp t) = rhs := sub_eq_zero.mp hz
    have hprod : R * Real.exp t ≠ 0 := mul_ne_zero hRne he
    have heq : 1 = rhs * (R * Real.exp t) :=
      (div_eq_iff hprod).mp hpoint
    have hexp : Real.exp t = 1 / (R * rhs) := by
      apply (eq_div_iff (mul_ne_zero hRne hrhsne)).2
      calc
        Real.exp t * (R * rhs) = rhs * (R * Real.exp t) := by ring
        _ = 1 := heq.symm
    calc
      t = Real.log (Real.exp t) := (Real.log_exp t).symm
      _ = Real.log (1 / (R * rhs)) := by rw [hexp]
  · intro ht
    rw [ht, Real.exp_log (one_div_pos.mpr (mul_pos hR hrhs))]
    field_simp [hRne, hrhsne] <;> ring

#print axioms sourceDual_loanLog_scalar_zero_iff

/-- Closed-form SOURCE loan-rate log coordinate, conditional on
stationary entrepreneurial CRRA=1 and strictly positive parameters. -/
noncomputable def sourceDualLoanLogTarget (P : Primitives S)
    (Z0 : LocalPrefixCoordinates) (z : Fin 33 → ℝ) : ℝ :=
  Real.log (1 /
    (Z0.controlsZero.loanRate *
      (P.entrepreneurDiscount * Real.exp (z (8 : Fin 33)) /
        (Real.exp (z (24 : Fin 33)) * Real.exp (z (28 : Fin 33))))))

theorem sourceFundingDual_zero_iff_loanLog_target
    (P : Primitives S) (Z0 : LocalPrefixCoordinates)
    (z : Fin 33 → ℝ)
    (hsigma : P.entrepreneurRiskAversion = 1)
    (hc_same : Z0.controlsZero.consumptionL = Z0.controlsOne.consumptionL)
    (hc_positive : 0 < Z0.controlsZero.consumptionL)
    (hpi : Z0.controlsOne.inflation = 1)
    (hr : 0 < Z0.controlsZero.loanRate)
    (hbeta : 0 < P.entrepreneurDiscount) :
    localNormalizedCollateralDualL P (localPrefixLogChart Z0 z) = 0 ↔
      z (15 : Fin 33) = sourceDualLoanLogTarget P Z0 z := by
  rw [sourceFundingDual_sigmaOne_stationary_fourLog
        P Z0 z hsigma hc_same hc_positive hpi]
  let rhs : ℝ := P.entrepreneurDiscount * Real.exp (z (8 : Fin 33)) /
    (Real.exp (z (24 : Fin 33)) * Real.exp (z (28 : Fin 33)))
  have hrhs : 0 < rhs := by
    dsimp [rhs]
    positivity
  change 1 / (Z0.controlsZero.loanRate * Real.exp (z (15 : Fin 33))) -
    rhs = 0 ↔
    z (15 : Fin 33) =
      Real.log (1 / (Z0.controlsZero.loanRate * rhs))
  exact sourceDual_loanLog_scalar_zero_iff
    Z0.controlsZero.loanRate rhs (z (15 : Fin 33)) hr hrhs

#print axioms sourceFundingDual_zero_iff_loanLog_target

/-- Elimination map: the other 32 endogenous log coordinates are held
fixed while the lender rate coordinate is solved in closed form. -/
noncomputable def sourceDualLoanLogEliminate
    (P : Primitives S) (Z0 : LocalPrefixCoordinates)
    (z : Fin 33 → ℝ) : Fin 33 → ℝ :=
  Function.update z (15 : Fin 33) (sourceDualLoanLogTarget P Z0 z)

theorem sourceDualLoanLogEliminate_other
    (P : Primitives S) (Z0 : LocalPrefixCoordinates)
    (z : Fin 33 → ℝ) (i : Fin 33)
    (hi : i ≠ (15 : Fin 33)) :
    sourceDualLoanLogEliminate P Z0 z i = z i := by
  exact Function.update_of_ne hi _ _

theorem sourceDualLoanLogEliminate_target_invariant
    (P : Primitives S) (Z0 : LocalPrefixCoordinates)
    (z : Fin 33 → ℝ) :
    sourceDualLoanLogTarget P Z0 (sourceDualLoanLogEliminate P Z0 z) =
      sourceDualLoanLogTarget P Z0 z := by
  simp [sourceDualLoanLogTarget, sourceDualLoanLogEliminate]

#print axioms sourceDualLoanLogEliminate_target_invariant

theorem sourceDualLoanLogEliminate_dual_zero
    (P : Primitives S) (Z0 : LocalPrefixCoordinates)
    (z : Fin 33 → ℝ)
    (hsigma : P.entrepreneurRiskAversion = 1)
    (hc_same : Z0.controlsZero.consumptionL = Z0.controlsOne.consumptionL)
    (hc_positive : 0 < Z0.controlsZero.consumptionL)
    (hpi : Z0.controlsOne.inflation = 1)
    (hr : 0 < Z0.controlsZero.loanRate)
    (hbeta : 0 < P.entrepreneurDiscount) :
    localNormalizedCollateralDualL P
      (localPrefixLogChart Z0 (sourceDualLoanLogEliminate P Z0 z)) = 0 := by
  apply (sourceFundingDual_zero_iff_loanLog_target
    P Z0 (sourceDualLoanLogEliminate P Z0 z)
    hsigma hc_same hc_positive hpi hr hbeta).2
  rw [sourceDualLoanLogEliminate_target_invariant]
  simp [sourceDualLoanLogEliminate]

#print axioms sourceDualLoanLogEliminate_dual_zero

/-- A true 34-source zero already lies on the exact eliminated
funding-dual surface. -/
theorem sourceDualLoanLogEliminate_eq_self_of_source_root
    (P : Primitives S) (I : InheritedState)
    (Z0 : LocalPrefixCoordinates) (dateOne recurrent : S)
    (tail : LocalPrefixContinuationRule)
    (z : Fin 33 → ℝ) (h : ℝ)
    (hsigma : P.entrepreneurRiskAversion = 1)
    (hc_same : Z0.controlsZero.consumptionL = Z0.controlsOne.consumptionL)
    (hc_positive : 0 < Z0.controlsZero.consumptionL)
    (hpi : Z0.controlsOne.inflation = 1)
    (hr : 0 < Z0.controlsZero.loanRate)
    (hbeta : 0 < P.entrepreneurDiscount)
    (hroot : augmentedBoundaryZeroResidual
        P I Z0 dateOne recurrent tail z h = (0, 0)) :
    sourceDualLoanLogEliminate P Z0 z = z := by
  have hdual :
      localNormalizedCollateralDualL P (localPrefixLogChart Z0 z) = 0 :=
    (augmentedBoundaryZeroResidual_eq_zero_iff
      P I Z0 dateOne recurrent tail z h).mp hroot |>.2
  have htarget := (sourceFundingDual_zero_iff_loanLog_target
    P Z0 z hsigma hc_same hc_positive hpi hr hbeta).mp hdual
  change Function.update z (15 : Fin 33)
    (sourceDualLoanLogTarget P Z0 z) = z
  rw [← htarget]
  exact Function.update_eq_self (15 : Fin 33) z

#print axioms sourceDualLoanLogEliminate_eq_self_of_source_root

/-- The 34-equation SOURCE zero set is equivalent to the 33 ORIGINAL
binding-prefix rows on the analytic funding-dual-zero surface. -/
theorem source34_root_exists_iff_33rows_on_eliminated_loanLog
    (P : Primitives S) (I : InheritedState)
    (Z0 : LocalPrefixCoordinates) (dateOne recurrent : S)
    (tail : LocalPrefixContinuationRule)
    (hsigma : P.entrepreneurRiskAversion = 1)
    (hc_same : Z0.controlsZero.consumptionL = Z0.controlsOne.consumptionL)
    (hc_positive : 0 < Z0.controlsZero.consumptionL)
    (hpi : Z0.controlsOne.inflation = 1)
    (hr : 0 < Z0.controlsZero.loanRate)
    (hbeta : 0 < P.entrepreneurDiscount) :
    (∃ (z : Fin 33 → ℝ) (h : ℝ),
      augmentedBoundaryZeroResidual P I Z0 dateOne recurrent tail z h =
        (0, 0)) ↔
    (∃ (z : Fin 33 → ℝ) (h : ℝ),
      ∀ row : Fin 33,
        localBindingResidualWithSlack P I Z0 dateOne recurrent tail
          (reserveRemunerationSlice 0 h)
          (sourceDualLoanLogEliminate P Z0 z) row = 0) := by
  constructor
  · rintro ⟨z, h, hroot⟩
    refine ⟨z, h, ?_⟩
    rw [sourceDualLoanLogEliminate_eq_self_of_source_root
      P I Z0 dateOne recurrent tail z h
      hsigma hc_same hc_positive hpi hr hbeta hroot]
    exact (augmentedBoundaryZeroResidual_eq_zero_iff
      P I Z0 dateOne recurrent tail z h).mp hroot |>.1
  · rintro ⟨z, h, hrows⟩
    refine ⟨sourceDualLoanLogEliminate P Z0 z, h, ?_⟩
    apply (augmentedBoundaryZeroResidual_eq_zero_iff
      P I Z0 dateOne recurrent tail
        (sourceDualLoanLogEliminate P Z0 z) h).mpr
    exact ⟨hrows, sourceDualLoanLogEliminate_dual_zero
      P Z0 z hsigma hc_same hc_positive hpi hr hbeta⟩

#print axioms source34_root_exists_iff_33rows_on_eliminated_loanLog

end Ventura26LiquidityAllocation
