import Ventura26LiquidityAllocation.CurrentSourceContinuousRowShear
import Ventura26LiquidityAllocation.CurrentSourceTwoDateFDerivTransport
import Mathlib.Analysis.Calculus.FDeriv.Prod

/-!
# SOURCE 33-row Frechet transport with continuous economic coefficients

This algebraic theorem uses the EXACT SOURCE two-date row order:
  date zero: policy rate 12, quantity 13, loan 14, deposit 15, balance 16
  date one:  policy rate 28, quantity 29, loan 30, deposit 31, balance 32.

At a common root F(x)=0, the 33-dimensional derivative of the
state-dependent bank-row shear is the FROZEN shear E(x) composed
with the original 33-by-33 derivative J, when the eight cross
coefficients are merely continuous at x.

The theorem assumes differentiability of F and continuity of all
eight coefficient functions, and proves a generic operator identity
with the exact SOURCE row indexing. It does not verify those economic
hypotheses for the concrete stationary chart, calculate an inverse
Jacobian, or prove a dynamic equilibrium.
-/

namespace Ventura26LiquidityAllocation
namespace CurrentSourceContinuous33Shear

open CurrentSourceFullFDeriv
open CurrentSourceTwoDateBank
open CurrentSourceContinuousRowShear
open scoped Topology

set_option maxHeartbeats 800000

/-- Coordinatewise realization of the EXACT two-date banking shear. -/
noncomputable def dynamicBankShear33
    (a0 b0 a1 b1 r0 q0 r1 q1 : Row33 → ℝ)
    (F : Row33 → Row33) (z : Row33) : Row33 :=
  fun i =>
    if i = 14 then F z 14 + a0 z * F z 12
    else if i = 15 then F z 15 + b0 z * F z 12
    else if i = 16 then
      (F z 16 + r0 z * F z 12) + q0 z * F z 13
    else if i = 30 then F z 30 + a1 z * F z 28
    else if i = 31 then F z 31 + b1 z * F z 28
    else if i = 32 then
      (F z 32 + r1 z * F z 28) + q1 z * F z 29
    else F z i

/-- The derivative is a continuous linear map on the REAL 33-vector. -/
noncomputable def frozenBankShearDerivative33
    (a0 b0 a1 b1 r0 q0 r1 q1 : Row33 → ℝ)
    (x : Row33) (J : Row33 →L[ℝ] Row33) :
    Row33 →L[ℝ] Row33 :=
  ContinuousLinearMap.pi (fun i =>
    if i = 14 then
      ((rowCoord 14).comp J) + (a0 x) • ((rowCoord 12).comp J)
    else if i = 15 then
      ((rowCoord 15).comp J) + (b0 x) • ((rowCoord 12).comp J)
    else if i = 16 then
      (((rowCoord 16).comp J) + (r0 x) • ((rowCoord 12).comp J)) +
        (q0 x) • ((rowCoord 13).comp J)
    else if i = 30 then
      ((rowCoord 30).comp J) + (a1 x) • ((rowCoord 28).comp J)
    else if i = 31 then
      ((rowCoord 31).comp J) + (b1 x) • ((rowCoord 28).comp J)
    else if i = 32 then
      (((rowCoord 32).comp J) + (r1 x) • ((rowCoord 28).comp J)) +
        (q1 x) • ((rowCoord 29).comp J)
    else (rowCoord i).comp J)

/-- The coordinatewise implementation agrees EXACTLY with the
existing SOURCE triangular row operator at every log state. -/
theorem dynamicBankShear33_eq_source
    (a0 b0 a1 b1 r0 q0 r1 q1 : Row33 → ℝ)
    (F : Row33 → Row33) (z : Row33) :
    dynamicBankShear33 a0 b0 a1 b1 r0 q0 r1 q1 F z =
      sourceTwoDateBankFiveRowShear
        (a0 z) (b0 z) (a1 z) (b1 z)
        (r0 z) (q0 z) (r1 z) (q1 z) (F z) := by
  funext i
  fin_cases i <;>
    simp [dynamicBankShear33, sourceTwoDateBankFiveRowShear,
      sourceTwoDateBankPricingRowShear,
      sourceTwoDateMonetaryBankRowShear,
      sourceDateOneMonetaryBankRowShear,
      sourceMonetaryBankRowShear] <;> ring

#print axioms dynamicBankShear33_eq_source

/-- The assembled 33-dimensional derivative is the pre-existing
bank-row CLM E(x) composed with J, not a new matrix convention. -/
theorem frozenBankShearDerivative33_eq_sourceCLM
    (a0 b0 a1 b1 r0 q0 r1 q1 : Row33 → ℝ)
    (x : Row33) (J : Row33 →L[ℝ] Row33) :
    frozenBankShearDerivative33 a0 b0 a1 b1 r0 q0 r1 q1 x J =
      (sourceShearCLM
        (a0 x) (b0 x) (a1 x) (b1 x)
        (r0 x) (q0 x) (r1 x) (q1 x)).comp J := by
  ext v i
  fin_cases i <;>
    simp [frozenBankShearDerivative33, sourceShearCLM, rowCoord,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.pi_apply] <;>
    ring

#print axioms frozenBankShearDerivative33_eq_sourceCLM

/-- Main Fréchet transport under EIGHT continuity assumptions rather
than a derivative assumption on the full state-dependent bank shear. -/
theorem dynamicBankShear33_hasFDerivAt_at_commonRoot
    (a0 b0 a1 b1 r0 q0 r1 q1 : Row33 → ℝ)
    (F : Row33 → Row33) (x : Row33)
    (J : Row33 →L[ℝ] Row33)
    (ha0 : ContinuousAt a0 x)
    (hb0 : ContinuousAt b0 x)
    (ha1 : ContinuousAt a1 x)
    (hb1 : ContinuousAt b1 x)
    (hr0 : ContinuousAt r0 x)
    (hq0 : ContinuousAt q0 x)
    (hr1 : ContinuousAt r1 x)
    (hq1 : ContinuousAt q1 x)
    (hF : HasFDerivAt F J x)
    (hroot : F x = 0) :
    HasFDerivAt
      (fun z => sourceTwoDateBankFiveRowShear
        (a0 z) (b0 z) (a1 z) (b1 z)
        (r0 z) (q0 z) (r1 z) (q1 z) (F z))
      ((sourceShearCLM
        (a0 x) (b0 x) (a1 x) (b1 x)
        (r0 x) (q0 x) (r1 x) (q1 x)).comp J) x := by
  classical
  have hcoord (i : Fin 33) :
      HasFDerivAt (fun z : Row33 => F z i)
        ((rowCoord i).comp J) x := by
    simpa only [rowCoord, ContinuousLinearMap.proj_apply] using
      ((rowCoord i).hasFDerivAt.comp x hF)
  have hzero (i : Fin 33) : F x i = 0 := by
    rw [hroot]
    rfl
  have hLoan0 :=
    continuous_one_donor_row_hasFDerivAt
      a0 (fun z => F z 12) (fun z => F z 14) x
      ((rowCoord 12).comp J) ((rowCoord 14).comp J)
      ha0 (hcoord 12) (hcoord 14) (hzero 12)
  have hDeposit0 :=
    continuous_one_donor_row_hasFDerivAt
      b0 (fun z => F z 12) (fun z => F z 15) x
      ((rowCoord 12).comp J) ((rowCoord 15).comp J)
      hb0 (hcoord 12) (hcoord 15) (hzero 12)
  have hBalance0 :=
    continuous_two_donor_row_hasFDerivAt
      r0 q0 (fun z => F z 12) (fun z => F z 13)
      (fun z => F z 16) x
      ((rowCoord 12).comp J) ((rowCoord 13).comp J)
      ((rowCoord 16).comp J)
      hr0 hq0 (hcoord 12) (hcoord 13) (hcoord 16)
      (hzero 12) (hzero 13)
  have hLoan1 :=
    continuous_one_donor_row_hasFDerivAt
      a1 (fun z => F z 28) (fun z => F z 30) x
      ((rowCoord 28).comp J) ((rowCoord 30).comp J)
      ha1 (hcoord 28) (hcoord 30) (hzero 28)
  have hDeposit1 :=
    continuous_one_donor_row_hasFDerivAt
      b1 (fun z => F z 28) (fun z => F z 31) x
      ((rowCoord 28).comp J) ((rowCoord 31).comp J)
      hb1 (hcoord 28) (hcoord 31) (hzero 28)
  have hBalance1 :=
    continuous_two_donor_row_hasFDerivAt
      r1 q1 (fun z => F z 28) (fun z => F z 29)
      (fun z => F z 32) x
      ((rowCoord 28).comp J) ((rowCoord 29).comp J)
      ((rowCoord 32).comp J)
      hr1 hq1 (hcoord 28) (hcoord 29) (hcoord 32)
      (hzero 28) (hzero 29)
  have hpi :
      HasFDerivAt
        (dynamicBankShear33 a0 b0 a1 b1 r0 q0 r1 q1 F)
        (frozenBankShearDerivative33
          a0 b0 a1 b1 r0 q0 r1 q1 x J) x := by
    change HasFDerivAt
      (fun z i => dynamicBankShear33
        a0 b0 a1 b1 r0 q0 r1 q1 F z i)
      (ContinuousLinearMap.pi (fun i =>
        if i = 14 then
          ((rowCoord 14).comp J) + (a0 x) • ((rowCoord 12).comp J)
        else if i = 15 then
          ((rowCoord 15).comp J) + (b0 x) • ((rowCoord 12).comp J)
        else if i = 16 then
          (((rowCoord 16).comp J) + (r0 x) • ((rowCoord 12).comp J)) +
            (q0 x) • ((rowCoord 13).comp J)
        else if i = 30 then
          ((rowCoord 30).comp J) + (a1 x) • ((rowCoord 28).comp J)
        else if i = 31 then
          ((rowCoord 31).comp J) + (b1 x) • ((rowCoord 28).comp J)
        else if i = 32 then
          (((rowCoord 32).comp J) + (r1 x) • ((rowCoord 28).comp J)) +
            (q1 x) • ((rowCoord 29).comp J)
        else (rowCoord i).comp J)) x
    apply (hasFDerivAt_pi).2
    intro i
    by_cases hi14 : i = 14
    · subst i
      simpa [dynamicBankShear33] using hLoan0
    by_cases hi15 : i = 15
    · subst i
      simpa [dynamicBankShear33] using hDeposit0
    by_cases hi16 : i = 16
    · subst i
      simpa [dynamicBankShear33] using hBalance0
    by_cases hi30 : i = 30
    · subst i
      simpa [dynamicBankShear33] using hLoan1
    by_cases hi31 : i = 31
    · subst i
      simpa [dynamicBankShear33] using hDeposit1
    by_cases hi32 : i = 32
    · subst i
      simpa [dynamicBankShear33] using hBalance1
    · simpa [dynamicBankShear33, hi14, hi15, hi16, hi30, hi31, hi32]
        using hcoord i
  rw [show (fun z => sourceTwoDateBankFiveRowShear
        (a0 z) (b0 z) (a1 z) (b1 z) (r0 z) (q0 z)
        (r1 z) (q1 z) (F z)) =
        dynamicBankShear33 a0 b0 a1 b1 r0 q0 r1 q1 F from
      funext (fun z => (dynamicBankShear33_eq_source
        a0 b0 a1 b1 r0 q0 r1 q1 F z).symm)]
  rw [← frozenBankShearDerivative33_eq_sourceCLM]
  exact hpi

#print axioms dynamicBankShear33_hasFDerivAt_at_commonRoot

end CurrentSourceContinuous33Shear
end Ventura26LiquidityAllocation
