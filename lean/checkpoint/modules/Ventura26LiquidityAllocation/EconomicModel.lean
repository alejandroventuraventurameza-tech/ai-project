import Ventura26LiquidityAllocation.FinancialCore
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Topology.Algebra.InfiniteSum.Module
import Mathlib.Topology.Algebra.InfiniteSum.Ring

/-!
# Source model for Ventura (2026), V0-M

This module encodes the economic objects that govern the paper's numbered
results.  In particular, an equilibrium is a predicate built from budgets,
balance sheets, settlement, market clearing, and literal optimization over the
source admissible sets.  It is not a field supplied by a candidate record.

Histories are finite and recurrent.  A date-`t` process is indexed only by the
states observed through date `t`, so adaptedness is enforced by its type.  The
transition law generates the finite-history weights used in the infinite
discounted objectives.
-/

open scoped BigOperators
open Filter

namespace Ventura26LiquidityAllocation

inductive FirmType
  | H
  | L
  deriving DecidableEq, Fintype, Repr

/-- Payment realizations use countable labels.  The economically active labels
are selected by `Primitives.paymentSupport`; hence the model represents every
finite distribution without fixing its cardinality or reparametrizing it as a
binary shock. -/
abbrev BankPayment := ℕ

/-- A history is stored newest-state first.  It contains exactly the states
observed through date `t`. -/
abbrev History (S : Type*) (t : ℕ) := Fin (t + 1) → S

/-- A real adapted process on the recurrent finite-support tree. -/
abbrev AdaptedProcess (S : Type*) := (t : ℕ) → History S t → ℝ

def currentState {S : Type*} {t : ℕ} (h : History S t) : S := h 0

/-- Add one newly observed state to a history. -/
def childHistory {S : Type*} {t : ℕ} (h : History S t) (s : S) : History S (t + 1) :=
  Fin.cases s h

/-- Remove the newest state from a noninitial history. -/
def previousHistory {S : Type*} {t : ℕ} (h : History S (t + 1)) : History S t :=
  fun j ↦ h j.succ

theorem childHistory_previousHistory_currentState
    {S : Type*} {t : ℕ} (h : History S (t + 1)) :
    childHistory (previousHistory h) (currentState h) = h := by
  funext j
  refine Fin.cases ?_ (fun i ↦ ?_) j <;> rfl

/-- Finite recurrent Markov support.  The probability axioms are primitive
environment restrictions, not equilibrium or existence certificates. -/
structure FiniteMarkovTree (S : Type*) [Fintype S] where
  initial : S
  transition : S → S → ℝ
  transition_nonneg : ∀ s s', 0 ≤ transition s s'
  transition_sum_one : ∀ s, ∑ s', transition s s' = 1

namespace FiniteMarkovTree

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- Probability of a finite history under the primitive Markov transition.
The initial state is fixed, as in the paper's local experiment. -/
noncomputable def historyWeight (T : FiniteMarkovTree S) :
    (t : ℕ) → History S t → ℝ
  | 0, h => if currentState h = T.initial then 1 else 0
  | t + 1, h =>
      historyWeight T t (previousHistory h) *
        T.transition (currentState (previousHistory h)) (currentState h)

noncomputable def expectationAt (T : FiniteMarkovTree S) (t : ℕ)
    (x : History S t → ℝ) : ℝ :=
  ∑ h, T.historyWeight t h * x h

/-- Conditional one-step expectation at a history. -/
noncomputable def expectationNext (T : FiniteMarkovTree S) {t : ℕ}
    (h : History S t) (x : History S (t + 1) → ℝ) : ℝ :=
  ∑ s, T.transition (currentState h) s * x (childHistory h s)

end FiniteMarkovTree

/-- CRRA utility, including the logarithmic case used by the numerical
witness.  It is evaluated only on positive consumption in admissible plans. -/
noncomputable def crraUtility (sigma c : ℝ) : ℝ :=
  if sigma = 1 then Real.log c else (c ^ (1 - sigma) - 1) / (1 - sigma)

noncomputable def realRepayment (nominalFace inflation : ℝ) : ℝ :=
  nominalFace / inflation

/-- The explicit Leontief/Nash OTC corridor weight from (3.7), with both
positive-tightness branches visible. -/
noncomputable def otcCorridorWeight (matchingIntensity tightness : ℝ) : ℝ :=
  if tightness ≤ 1 then
    1 / (1 + Real.sqrt
      (tightness + (1 - tightness) * Real.exp matchingIntensity))
  else
    let radicand :=
      tightness⁻¹ + (1 - tightness⁻¹) * Real.exp matchingIntensity
    Real.sqrt radicand / (1 + Real.sqrt radicand)

/-- Cumulative Leontief matching intensity `a_λ=1-exp(-λ)`. -/
noncomputable def otcMatchIntensityShare (matchingIntensity : ℝ) : ℝ :=
  1 - Real.exp (-matchingIntensity)

/-- Source fraction `Ψ⁺` of aggregate surplus reserves traded OTC. -/
noncomputable def otcSurplusMatchFraction
    (matchingIntensity tightness : ℝ) : ℝ :=
  if tightness ≤ 1 then
    tightness * otcMatchIntensityShare matchingIntensity
  else
    otcMatchIntensityShare matchingIntensity

/-- Source fraction `Ψ⁻` of aggregate reserve deficits traded OTC. -/
noncomputable def otcDeficitMatchFraction
    (matchingIntensity tightness : ℝ) : ℝ :=
  if tightness ≤ 1 then
    otcMatchIntensityShare matchingIntensity
  else
    otcMatchIntensityShare matchingIntensity / tightness

theorem otcMatchIntensityShare_mem (matchingIntensity : ℝ)
    (hmatching : 0 < matchingIntensity) :
    0 < otcMatchIntensityShare matchingIntensity ∧
      otcMatchIntensityShare matchingIntensity < 1 := by
  unfold otcMatchIntensityShare
  have hexp_pos := Real.exp_pos (-matchingIntensity)
  have hexp_lt_one : Real.exp (-matchingIntensity) < 1 :=
    Real.exp_lt_one_iff.mpr (neg_neg_of_pos hmatching)
  constructor <;> linarith

theorem otcDeficitMatchFraction_mem (matchingIntensity tightness : ℝ)
    (hmatching : 0 < matchingIntensity) (htightness : 0 < tightness) :
    0 ≤ otcDeficitMatchFraction matchingIntensity tightness ∧
      otcDeficitMatchFraction matchingIntensity tightness ≤ 1 := by
  rcases otcMatchIntensityShare_mem matchingIntensity hmatching with ⟨hshare0, hshare1⟩
  unfold otcDeficitMatchFraction
  by_cases hle : tightness ≤ 1
  · simp only [if_pos hle]
    exact ⟨hshare0.le, hshare1.le⟩
  · simp only [if_neg hle]
    have hone : 1 ≤ tightness := (lt_of_not_ge hle).le
    exact ⟨div_nonneg hshare0.le htightness.le,
      le_trans (div_le_self hshare0.le hone) hshare1.le⟩

theorem otcSurplusMatchFraction_mem (matchingIntensity tightness : ℝ)
    (hmatching : 0 < matchingIntensity) (htightness : 0 < tightness) :
    0 ≤ otcSurplusMatchFraction matchingIntensity tightness ∧
      otcSurplusMatchFraction matchingIntensity tightness ≤ 1 := by
  rcases otcMatchIntensityShare_mem matchingIntensity hmatching with ⟨hshare0, hshare1⟩
  unfold otcSurplusMatchFraction
  by_cases hle : tightness ≤ 1
  · simp only [if_pos hle]
    refine ⟨mul_nonneg htightness.le hshare0.le, ?_⟩
    calc
      tightness * otcMatchIntensityShare matchingIntensity ≤
          1 * otcMatchIntensityShare matchingIntensity :=
        mul_le_mul_of_nonneg_right hle hshare0.le
      _ ≤ 1 := by simpa using hshare1.le
  · simp only [if_neg hle]
    exact ⟨hshare0.le, hshare1.le⟩

/-- Corridor rate generated by matching tightness, equation (IBrate). -/
noncomputable def otcNegotiatedRate
    (reserveRate facilityRate matchingIntensity tightness : ℝ) : ℝ :=
  reserveRate + (facilityRate - reserveRate) *
    otcCorridorWeight matchingIntensity tightness

/-- Source slope `χ⁻`, derived from matching fractions and the three settlement
rates rather than supplied as a free scalar. -/
noncomputable def otcDeficitSlope
    (reserveRate interbankRate facilityRate matchingIntensity tightness : ℝ) : ℝ :=
  otcDeficitMatchFraction matchingIntensity tightness *
      (interbankRate - reserveRate) +
    (1 - otcDeficitMatchFraction matchingIntensity tightness) *
      (facilityRate - reserveRate)

/-- Source slope `χ⁺`, derived from matching and corridor rates. -/
noncomputable def otcSurplusSlope
    (reserveRate interbankRate matchingIntensity tightness : ℝ) : ℝ :=
  otcSurplusMatchFraction matchingIntensity tightness *
    (interbankRate - reserveRate)

/-- The Nash-bargaining weight in the source's OTC rate is strictly inside
the corridor whenever market tightness is positive. -/
theorem otcCorridorWeight_mem (matchingIntensity tightness : ℝ)
    (htightness : 0 < tightness) :
    0 < otcCorridorWeight matchingIntensity tightness ∧
      otcCorridorWeight matchingIntensity tightness < 1 := by
  unfold otcCorridorWeight
  by_cases hle : tightness ≤ 1
  · rw [if_pos hle]
    have hradicand :
        0 < tightness + (1 - tightness) * Real.exp matchingIntensity := by
      have hexp : 0 < Real.exp matchingIntensity := Real.exp_pos _
      have hnonneg : 0 ≤ (1 - tightness) * Real.exp matchingIntensity :=
        mul_nonneg (sub_nonneg.mpr hle) hexp.le
      linarith
    have hsqrt : 0 < Real.sqrt
        (tightness + (1 - tightness) * Real.exp matchingIntensity) :=
      Real.sqrt_pos.2 hradicand
    constructor
    · positivity
    · exact (div_lt_one (by linarith)).2 (by linarith)
  · rw [if_neg hle]
    dsimp only
    have hone : 1 < tightness := lt_of_not_ge hle
    have hinvpos : 0 < tightness⁻¹ := inv_pos.mpr htightness
    have hinvlt : tightness⁻¹ < 1 := (inv_lt_one₀ htightness).2 hone
    have hradicand :
        0 < tightness⁻¹ + (1 - tightness⁻¹) * Real.exp matchingIntensity := by
      have hexp : 0 < Real.exp matchingIntensity := Real.exp_pos _
      have hnonneg : 0 ≤ (1 - tightness⁻¹) * Real.exp matchingIntensity :=
        mul_nonneg (sub_nonneg.mpr hinvlt.le) hexp.le
      linarith
    have hsqrt : 0 < Real.sqrt
        (tightness⁻¹ + (1 - tightness⁻¹) * Real.exp matchingIntensity) :=
      Real.sqrt_pos.2 hradicand
    constructor
    · positivity
    · exact (div_lt_one (by linarith)).2 (by linarith)

/-- At a positive-activity OTC market and a strict policy corridor, the source
formulas imply `0 ≤ χ⁺ ≤ χ⁻`.  This is the slope ordering consumed by
the bank's concave kink problem; it is derived rather than assumed. -/
theorem otcSlopes_ordered
    (reserveRate facilityRate matchingIntensity tightness : ℝ)
    (hcorridor : reserveRate < facilityRate)
    (hmatching : 0 < matchingIntensity) (htightness : 0 < tightness) :
    let interbankRate :=
      otcNegotiatedRate reserveRate facilityRate matchingIntensity tightness
    0 ≤ otcSurplusSlope reserveRate interbankRate matchingIntensity tightness ∧
      otcSurplusSlope reserveRate interbankRate matchingIntensity tightness ≤
        otcDeficitSlope reserveRate interbankRate facilityRate matchingIntensity
          tightness := by
  dsimp only
  let interbankRate :=
    otcNegotiatedRate reserveRate facilityRate matchingIntensity tightness
  let deficitFraction := otcDeficitMatchFraction matchingIntensity tightness
  let surplusFraction := otcSurplusMatchFraction matchingIntensity tightness
  have hweight := otcCorridorWeight_mem matchingIntensity tightness htightness
  have hgap : 0 < facilityRate - reserveRate := sub_pos.mpr hcorridor
  have hinterbankGap : 0 < interbankRate - reserveRate := by
    dsimp [interbankRate, otcNegotiatedRate]
    have := mul_pos hgap hweight.1
    linarith
  have hfacilityGap : 0 < facilityRate - interbankRate := by
    dsimp [interbankRate, otcNegotiatedRate]
    have hproduct : (facilityRate - reserveRate) *
        otcCorridorWeight matchingIntensity tightness <
          facilityRate - reserveRate := by
      nlinarith [mul_pos hgap (sub_pos.mpr hweight.2)]
    linarith
  have hdeficitFraction :=
    otcDeficitMatchFraction_mem matchingIntensity tightness hmatching htightness
  have hsurplusFraction :=
    otcSurplusMatchFraction_mem matchingIntensity tightness hmatching htightness
  constructor
  · unfold otcSurplusSlope
    exact mul_nonneg hsurplusFraction.1 hinterbankGap.le
  · change otcSurplusSlope reserveRate interbankRate matchingIntensity tightness ≤
      otcDeficitSlope reserveRate interbankRate facilityRate matchingIntensity tightness
    have hidentity :
        otcDeficitSlope reserveRate interbankRate facilityRate matchingIntensity
              tightness -
            otcSurplusSlope reserveRate interbankRate matchingIntensity tightness =
          (1 - deficitFraction) * (facilityRate - reserveRate) +
            (deficitFraction - surplusFraction) *
              (interbankRate - reserveRate) := by
      dsimp [deficitFraction, surplusFraction]
      unfold otcDeficitSlope otcSurplusSlope
      ring
    by_cases hle : tightness ≤ 1
    · have hshare := otcMatchIntensityShare_mem matchingIntensity hmatching
      have hfractionOrder : surplusFraction ≤ deficitFraction := by
        dsimp [surplusFraction, deficitFraction, otcSurplusMatchFraction,
          otcDeficitMatchFraction]
        rw [if_pos hle, if_pos hle]
        simpa using mul_le_mul_of_nonneg_right hle hshare.1.le
      have hnonneg :
          0 ≤ (1 - deficitFraction) * (facilityRate - reserveRate) +
            (deficitFraction - surplusFraction) *
              (interbankRate - reserveRate) :=
        add_nonneg
          (mul_nonneg (sub_nonneg.mpr hdeficitFraction.2) hgap.le)
          (mul_nonneg (sub_nonneg.mpr hfractionOrder) hinterbankGap.le)
      linarith
    · have hone : 1 < tightness := lt_of_not_ge hle
      have hshare := otcMatchIntensityShare_mem matchingIntensity hmatching
      have hfractionOrder : deficitFraction ≤ surplusFraction := by
        dsimp [surplusFraction, deficitFraction, otcSurplusMatchFraction,
          otcDeficitMatchFraction]
        rw [if_neg hle, if_neg hle]
        exact div_le_self hshare.1.le hone.le
      have hgapOrder : interbankRate - reserveRate ≤
          facilityRate - reserveRate := by linarith
      have hrewrite :
          (1 - deficitFraction) * (facilityRate - reserveRate) +
              (deficitFraction - surplusFraction) *
                (interbankRate - reserveRate) =
            (1 - surplusFraction) * (facilityRate - reserveRate) +
              (surplusFraction - deficitFraction) *
                ((facilityRate - reserveRate) -
                  (interbankRate - reserveRate)) := by ring
      have hnonneg :
          0 ≤ (1 - deficitFraction) * (facilityRate - reserveRate) +
            (deficitFraction - surplusFraction) *
              (interbankRate - reserveRate) := by
        rw [hrewrite]
        exact add_nonneg
          (mul_nonneg (sub_nonneg.mpr hsurplusFraction.2) hgap.le)
          (mul_nonneg (sub_nonneg.mpr hfractionOrder)
            (sub_nonneg.mpr hgapOrder))
      linarith

/-- Bilateral OTC activity and the source definition
`ϑ = S⁻ / S⁺`.  The positivity clauses exclude the no-trade cases in which
the paper does not report an average bilateral transaction rate. -/
def BilateralOTCActivity
    (deficitSupply surplusSupply tightness : ℝ) : Prop :=
  0 < deficitSupply ∧ 0 < surplusSupply ∧
    tightness = deficitSupply / surplusSupply

/-- Finite expectation under the bank-payment distribution used in (3.8). -/
noncomputable def finiteExpectation {W : Type*} [Fintype W]
    (probability : W → ℝ) (value : W → ℝ) : ℝ :=
  ∑ ω, probability ω * value ω

/-- Expectation of a countably-labelled random variable with finite support. -/
noncomputable def finiteSupportExpectation {W : Type*} [DecidableEq W]
    (support : Finset W) (probability : W → ℝ) (value : W → ℝ) : ℝ :=
  ∑ ω ∈ support, probability ω * value ω

theorem finiteSupportExpectation_const_mul {W : Type*} [DecidableEq W]
    (support : Finset W) (probability : W → ℝ) (c : ℝ) (value : W → ℝ) :
    finiteSupportExpectation support probability (fun ω ↦ c * value ω) =
      c * finiteSupportExpectation support probability value := by
  unfold finiteSupportExpectation
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ω _
  ring

theorem finiteSupportExpectation_const {W : Type*} [DecidableEq W]
    (support : Finset W) (probability : W → ℝ)
    (hsum : ∑ ω ∈ support, probability ω = 1) (c : ℝ) :
    finiteSupportExpectation support probability (fun _ω ↦ c) = c := by
  unfold finiteSupportExpectation
  rw [← Finset.sum_mul, hsum]
  ring

theorem finiteSupportExpectation_add {W : Type*} [DecidableEq W]
    (support : Finset W) (probability : W → ℝ) (x y : W → ℝ) :
    finiteSupportExpectation support probability (fun ω ↦ x ω + y ω) =
      finiteSupportExpectation support probability x +
        finiteSupportExpectation support probability y := by
  unfold finiteSupportExpectation
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro ω _
  ring

theorem finiteSupportExpectation_sub {W : Type*} [DecidableEq W]
    (support : Finset W) (probability : W → ℝ) (x y : W → ℝ) :
    finiteSupportExpectation support probability (fun ω ↦ x ω - y ω) =
      finiteSupportExpectation support probability x -
        finiteSupportExpectation support probability y := by
  unfold finiteSupportExpectation
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro ω _
  ring

/-- The firm's normalized marginal discount in Lemma 3.2.  The future
marginal value is converted from nominal to real units state by state and the
Euler equations are divided by the strictly positive current cash
multiplier.  Thus `discount` cannot be supplied as an unrelated scalar. -/
def NormalizedFirmMarginalDiscount {W : Type*} [Fintype W]
    (probability marginalValueNext inflationNext : W → ℝ)
    (entrepreneurDiscount cashMultiplier discount : ℝ) : Prop :=
  (∀ ω, 0 ≤ probability ω) ∧ ∑ ω, probability ω = 1 ∧
  0 < entrepreneurDiscount ∧ 0 < cashMultiplier ∧
  (∀ ω, 0 < marginalValueNext ω) ∧ (∀ ω, 0 < inflationNext ω) ∧
  discount = entrepreneurDiscount *
    finiteExpectation probability (fun ω ↦ marginalValueNext ω / inflationNext ω) /
      cashMultiplier ∧
  0 < discount

/-- Finite covariance, retained explicitly because the source proves the sign
of the spread's shock term through a covariance inequality. -/
noncomputable def finiteCovariance {W : Type*} [Fintype W]
    (probability : W → ℝ) (x y : W → ℝ) : ℝ :=
  finiteExpectation probability (fun ω ↦ x ω * y ω) -
    finiteExpectation probability x * finiteExpectation probability y

noncomputable def finiteSupportCovariance {W : Type*} [DecidableEq W]
    (support : Finset W) (probability : W → ℝ) (x y : W → ℝ) : ℝ :=
  finiteSupportExpectation support probability (fun ω ↦ x ω * y ω) -
    finiteSupportExpectation support probability x *
      finiteSupportExpectation support probability y

/-- Weighted finite Chebyshev inequality in the direction needed by the bank
spread argument.  It is stated for a support finset, so zero-probability labels
outside the economic support play no role. -/
theorem finiteSupportCovariance_nonpos_of_antitone
    {W : Type*} [DecidableEq W] (support : Finset W)
    (probability : W → ℝ) (x y : W → ℝ)
    (hprobability : ∀ ω ∈ support, 0 ≤ probability ω)
    (hsum : ∑ ω ∈ support, probability ω = 1)
    (hantitone : ∀ ω ∈ support, ∀ ω' ∈ support,
      y ω ≤ y ω' → x ω' ≤ x ω) :
    finiteSupportCovariance support probability x y ≤ 0 := by
  let pairSum := ∑ ω ∈ support, ∑ ω' ∈ support,
    probability ω * probability ω' * ((x ω - x ω') * (y ω - y ω'))
  have hpair : ∀ ω ∈ support, ∀ ω' ∈ support,
      probability ω * probability ω' *
          ((x ω - x ω') * (y ω - y ω')) ≤ 0 := by
    intro ω hω ω' hω'
    have hweight : 0 ≤ probability ω * probability ω' :=
      mul_nonneg (hprobability ω hω) (hprobability ω' hω')
    have hproduct : (x ω - x ω') * (y ω - y ω') ≤ 0 := by
      by_cases horder : y ω ≤ y ω'
      · exact mul_nonpos_of_nonneg_of_nonpos
          (sub_nonneg.mpr (hantitone ω hω ω' hω' horder))
          (sub_nonpos.mpr horder)
      · have hreverse : y ω' ≤ y ω := le_of_not_ge horder
        exact mul_nonpos_of_nonpos_of_nonneg
          (sub_nonpos.mpr (hantitone ω' hω' ω hω hreverse))
          (sub_nonneg.mpr hreverse)
    exact mul_nonpos_of_nonneg_of_nonpos hweight hproduct
  have hpairSum : pairSum ≤ 0 := by
    dsimp [pairSum]
    exact Finset.sum_nonpos fun ω hω ↦
      Finset.sum_nonpos fun ω' hω' ↦ hpair ω hω ω' hω'
  have hidentity : pairSum =
      (∑ ω ∈ support, probability ω * x ω * y ω) *
          (∑ ω ∈ support, probability ω) -
        (∑ ω ∈ support, probability ω * x ω) *
          (∑ ω ∈ support, probability ω * y ω) -
        (∑ ω ∈ support, probability ω * y ω) *
          (∑ ω ∈ support, probability ω * x ω) +
        (∑ ω ∈ support, probability ω) *
          (∑ ω ∈ support, probability ω * x ω * y ω) := by
    dsimp [pairSum]
    rw [Finset.sum_mul_sum, Finset.sum_mul_sum, Finset.sum_mul_sum,
      Finset.sum_mul_sum]
    rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib,
      ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro ω hω
    rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib,
      ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro ω' hω'
    ring
  rw [hidentity, hsum] at hpairSum
  unfold finiteSupportCovariance finiteSupportExpectation
  have hxy : (∑ ω ∈ support, probability ω * x ω * y ω) =
      ∑ ω ∈ support, probability ω * (x ω * y ω) := by
    apply Finset.sum_congr rfl
    intro ω _
    ring
  rw [← hxy]
  nlinarith

/-- Excess reserves before OTC settlement after the idiosyncratic deposit
transfer, equation (surplus). -/
def bankSettlementSurplus
    (reservesPre reserveRequirement depositReserveRatio deposits shock : ℝ) : ℝ :=
  reservesPre - reserveRequirement * deposits +
    (depositReserveRatio - reserveRequirement) * shock * deposits

theorem bankSettlementSurplus_mono_in_shock
    {reservesPre reserveRequirement depositReserveRatio deposits firstShock
      secondShock : ℝ}
    (hratio : reserveRequirement < depositReserveRatio)
    (hdeposits : 0 < deposits) (hshock : firstShock ≤ secondShock) :
    bankSettlementSurplus reservesPre reserveRequirement depositReserveRatio
        deposits firstShock ≤
      bankSettlementSurplus reservesPre reserveRequirement depositReserveRatio
        deposits secondShock := by
  unfold bankSettlementSurplus
  have hcoefficient : 0 < (depositReserveRatio - reserveRequirement) * deposits :=
    mul_pos (sub_pos.mpr hratio) hdeposits
  nlinarith [mul_le_mul_of_nonneg_left hshock hcoefficient.le]

/-- The source's piecewise-linear OTC/facility payoff `χ`. -/
noncomputable def otcLiquidityPayoff (deficitSlope surplusSlope surplus : ℝ) : ℝ :=
  if surplus < 0 then deficitSlope * surplus else surplusSlope * surplus

/-- Its classical slope away from the kink at zero. -/
noncomputable def otcLiquidityMarginal (deficitSlope surplusSlope surplus : ℝ) : ℝ :=
  if surplus < 0 then deficitSlope else surplusSlope

/-- A selected supergradient of the concave liquidity payoff.  At `surplus = 0`
this permits the full source interval instead of excluding an atom at the
kink or silently using a classical derivative. -/
def IsOTCLiquiditySupergradient
    (deficitSlope surplusSlope surplus slope : ℝ) : Prop :=
  ∀ alternative,
    otcLiquidityPayoff deficitSlope surplusSlope alternative ≤
      otcLiquidityPayoff deficitSlope surplusSlope surplus +
        slope * (alternative - surplus)

/-- Exact pointwise superdifferential of the source's concave liquidity
payoff, retaining the full interval at a zero-surplus atom. -/
def OTCLiquiditySupergradientCases
    (deficitSlope surplusSlope surplus slope : ℝ) : Prop :=
  (surplus < 0 ∧ slope = deficitSlope) ∨
  (surplus = 0 ∧ surplusSlope ≤ slope ∧ slope ≤ deficitSlope) ∨
  (0 < surplus ∧ slope = surplusSlope)

theorem isOTCLiquiditySupergradient_iff_cases
    {deficitSlope surplusSlope surplus slope : ℝ}
    (hconcave : surplusSlope ≤ deficitSlope) :
    IsOTCLiquiditySupergradient deficitSlope surplusSlope surplus slope ↔
      OTCLiquiditySupergradientCases deficitSlope surplusSlope surplus slope := by
  constructor
  · intro hsuper
    rcases lt_trichotomy surplus 0 with hnegative | hzero | hpositive
    · left
      refine ⟨hnegative, le_antisymm ?_ ?_⟩
      · have htest := hsuper (2 * surplus)
        have htestNegative : 2 * surplus < 0 :=
          mul_neg_of_pos_of_neg (by norm_num) hnegative
        simp [otcLiquidityPayoff, hnegative, htestNegative] at htest
        nlinarith
      · have htest := hsuper (surplus / 2)
        have htestNegative : surplus / 2 < 0 :=
          div_neg_of_neg_of_pos hnegative (by norm_num)
        simp [otcLiquidityPayoff, hnegative, htestNegative] at htest
        nlinarith
    · subst surplus
      right
      left
      refine ⟨rfl, ?_, ?_⟩
      · have htest := hsuper 1
        norm_num [otcLiquidityPayoff] at htest ⊢
        exact htest
      · have htest := hsuper (-1)
        norm_num [otcLiquidityPayoff] at htest ⊢
        linarith
    · right
      right
      refine ⟨hpositive, le_antisymm ?_ ?_⟩
      · have htest := hsuper (surplus / 2)
        have htestPositive : 0 < surplus / 2 :=
          div_pos hpositive (by norm_num)
        simp [otcLiquidityPayoff, not_lt.mpr hpositive.le,
          not_lt.mpr htestPositive.le] at htest
        nlinarith
      · have htest := hsuper (2 * surplus)
        have htestPositive : 0 < 2 * surplus :=
          mul_pos (by norm_num) hpositive
        simp [otcLiquidityPayoff, not_lt.mpr hpositive.le,
          not_lt.mpr htestPositive.le] at htest
        nlinarith
  · intro hcases alternative
    rcases hcases with ⟨hsurplus, hslope⟩ | ⟨hzero, hlower, hupper⟩ |
        ⟨hsurplus, hslope⟩
    · rw [hslope]
      rw [show otcLiquidityPayoff deficitSlope surplusSlope surplus =
          deficitSlope * surplus by simp [otcLiquidityPayoff, hsurplus]]
      by_cases halternative : alternative < 0
      · simp [otcLiquidityPayoff, halternative]
        exact le_of_eq (by ring)
      · have halternativeNonneg : 0 ≤ alternative := le_of_not_gt halternative
        simp [otcLiquidityPayoff, halternative]
        have hmul := mul_le_mul_of_nonneg_left hconcave halternativeNonneg
        nlinarith
    · subst surplus
      simp only [otcLiquidityPayoff, lt_self_iff_false, if_false, mul_zero,
        sub_zero, zero_add]
      by_cases halternative : alternative < 0
      · simp [otcLiquidityPayoff, halternative]
        exact hupper
      · have halternativeNonneg : 0 ≤ alternative := le_of_not_gt halternative
        simp [otcLiquidityPayoff, halternative]
        exact mul_le_mul_of_nonneg_right hlower halternativeNonneg
    · rw [hslope]
      rw [show otcLiquidityPayoff deficitSlope surplusSlope surplus =
          surplusSlope * surplus by
            simp [otcLiquidityPayoff, not_lt.mpr hsurplus.le]]
      by_cases halternative : alternative < 0
      · simp [otcLiquidityPayoff, halternative]
        have hmul := mul_le_mul_of_nonpos_left hconcave halternative.le
        nlinarith
      · simp [otcLiquidityPayoff, halternative]
        exact le_of_eq (by ring)

/-- Supergradients of the concave liquidity payoff are ordered in the reverse
direction at two strictly ordered settlement positions.  Equal-position atoms
still require a common selection, as the source notes. -/
theorem otcLiquiditySupergradient_antitone_of_lt
    {deficitSlope surplusSlope first second firstSlope secondSlope : ℝ}
    (hfirst : IsOTCLiquiditySupergradient deficitSlope surplusSlope
      first firstSlope)
    (hsecond : IsOTCLiquiditySupergradient deficitSlope surplusSlope
      second secondSlope)
    (horder : first < second) :
    secondSlope ≤ firstSlope := by
  have hforward := hfirst second
  have hbackward := hsecond first
  nlinarith

/-- A tie-consistent selector for the liquidity superdifferential. -/
noncomputable def selectedOTCLiquidityMarginal
    (deficitSlope surplusSlope kinkSlope surplus : ℝ) : ℝ :=
  if surplus < 0 then deficitSlope
  else if 0 < surplus then surplusSlope
  else kinkSlope

theorem selectedOTCLiquidityMarginal_isSupergradient
    {deficitSlope surplusSlope kinkSlope surplus : ℝ}
    (hconcave : surplusSlope ≤ deficitSlope)
    (hkinkLower : surplusSlope ≤ kinkSlope)
    (hkinkUpper : kinkSlope ≤ deficitSlope) :
    IsOTCLiquiditySupergradient deficitSlope surplusSlope surplus
      (selectedOTCLiquidityMarginal deficitSlope surplusSlope kinkSlope surplus) := by
  rw [isOTCLiquiditySupergradient_iff_cases hconcave]
  rcases lt_trichotomy surplus 0 with hnegative | hzero | hpositive
  · left
    simp [selectedOTCLiquidityMarginal, hnegative]
  · subst surplus
    right
    left
    simp [selectedOTCLiquidityMarginal, hkinkLower, hkinkUpper]
  · right
    right
    simp [selectedOTCLiquidityMarginal, hpositive, not_lt.mpr hpositive.le]

theorem selectedOTCLiquidityMarginal_antitone
    {deficitSlope surplusSlope kinkSlope first second : ℝ}
    (hconcave : surplusSlope ≤ deficitSlope)
    (hkinkLower : surplusSlope ≤ kinkSlope)
    (hkinkUpper : kinkSlope ≤ deficitSlope)
    (horder : first ≤ second) :
    selectedOTCLiquidityMarginal deficitSlope surplusSlope kinkSlope second ≤
      selectedOTCLiquidityMarginal deficitSlope surplusSlope kinkSlope first := by
  rcases horder.eq_or_lt with hequal | hstrict
  · subst second
    exact le_rfl
  · exact otcLiquiditySupergradient_antitone_of_lt
      (selectedOTCLiquidityMarginal_isSupergradient hconcave hkinkLower hkinkUpper)
      (selectedOTCLiquidityMarginal_isSupergradient hconcave hkinkLower hkinkUpper)
      hstrict

noncomputable def operatingOutput (productivity capital labor alpha beta : ℝ) : ℝ :=
  productivity * capital ^ alpha * labor ^ beta

noncomputable def operatingProfit (inputPrice productivity capital labor alpha beta wage : ℝ) : ℝ :=
  inputPrice * operatingOutput productivity capital labor alpha beta - wage * labor

/-- A value is the endogenous worst-child liquidation value.  Ties are
retained because every minimizing child is allowed. -/
def IsWorstChildValue {S : Type*} [Fintype S] {t : ℕ}
    (liquidation : S → ℝ) (value : ℝ) : Prop :=
  (∀ s, value ≤ liquidation s) ∧ ∃ s, value = liquidation s

/-- Robust collateral as one constraint for every conditionally possible
future child.  This is the statewise form, so changes and ties of the worst
supported child remain endogenous without constraining zero-transition labels. -/
def RobustCollateral {S : Type*} [Fintype S]
    (theta depreciation loanRate loan capitalNext : ℝ)
    (possible : S → Prop)
    (inflationNext capitalPriceNext : S → ℝ) : Prop :=
  ∀ s, possible s →
      loanRate * loan ≤
      theta * (1 - depreciation) *
        (inflationNext s * capitalPriceNext s) * capitalNext

/-- Primitive parameters and functions.  Positivity, discounting, and
decreasing-returns restrictions are recorded here because the source states
them as governing assumptions. -/
structure Primitives (S : Type*) [Fintype S] where
  tree : FiniteMarkovTree S
  mass : FirmType → ℝ
  productivity : FirmType → ℝ
  /-- Common aggregate productivity `z_t`, separated from the permanent
  entrepreneur type shifter `A_i`. -/
  aggregateProductivity : S → ℝ
  pledgeability : FirmType → ℝ
  alpha : ℝ
  beta : ℝ
  depreciation : ℝ
  entrepreneurDiscount : ℝ
  workerDiscount : ℝ
  entrepreneurRiskAversion : ℝ
  workerRiskAversion : ℝ
  laborCurvature : ℝ
  laborScale : ℝ
  priceElasticity : ℝ
  priceAdjustmentCost : ℝ
  capitalAdjustmentCost : ℝ
  bankExit : ℝ
  bankSeedShare : ℝ
  /-- Default bank caps used by the distinguished payment-law type.  A
  heterogeneous population replaces them type by type below. -/
  bankDepositCap : ℝ
  bankLoanCap : ℝ
  matchingIntensity : ℝ
  governmentBondSupply : ℝ
  reserveRatePersistence : ℝ
  reserveQuantityPersistence : ℝ
  reserveRateSteady : ℝ
  reserveQuantitySteady : ℝ
  outputReference : ℝ
  inflationResponse : ℝ
  outputResponse : ℝ
  reserveRateInnovation : S → ℝ
  reserveQuantityInnovation : S → ℝ
  /-- Announced instrument paths held fixed when agents deviate. -/
  reserveRequirementPath : AdaptedProcess S
  corridorWidthPath : AdaptedProcess S
  paymentSupport : Finset BankPayment
  paymentProbability : BankPayment → ℝ
  paymentShock : BankPayment → ℝ
  mass_pos : ∀ i, 0 < mass i
  productivity_pos : ∀ i, 0 < productivity i
  productivity_order : productivity FirmType.L < productivity FirmType.H
  aggregate_productivity_pos : ∀ s, 0 < aggregateProductivity s
  pledgeability_mem : ∀ i, 0 ≤ pledgeability i ∧ pledgeability i < 1
  alpha_pos : 0 < alpha
  beta_pos : 0 < beta
  decreasing_returns : alpha + beta < 1
  price_elasticity_gt_one : 1 < priceElasticity
  capital_adjustment_cost_pos : 0 < capitalAdjustmentCost
  matching_intensity_pos : 0 < matchingIntensity
  depreciation_mem : 0 < depreciation ∧ depreciation < 1
  discount_order : 0 < entrepreneurDiscount ∧
    entrepreneurDiscount < workerDiscount ∧ workerDiscount < 1
  bank_exit_mem : 0 ≤ bankExit ∧ bankExit ≤ 1
  bank_seed_mem : 0 ≤ bankSeedShare ∧ bankSeedShare ≤ 1
  bank_caps_nonneg : 0 ≤ bankDepositCap ∧ 0 ≤ bankLoanCap
  payment_probability_nonneg : ∀ ω, 0 ≤ paymentProbability ω
  /-- `paymentSupport` is the mathematical support, not merely a finite
  summation container: every listed realization has positive mass. -/
  payment_probability_pos_on_support :
    ∀ ω, ω ∈ paymentSupport → 0 < paymentProbability ω
  payment_shock_gt_neg_one_on_support :
    ∀ ω, ω ∈ paymentSupport → -1 < paymentShock ω
  payment_probability_zero_outside : ∀ ω, ω ∉ paymentSupport → paymentProbability ω = 0
  payment_probability_sum_one : ∑ ω ∈ paymentSupport, paymentProbability ω = 1
  payment_shock_mean_zero :
    ∑ ω ∈ paymentSupport, paymentProbability ω * paymentShock ω = 0

/-- A bank type's idiosyncratic payment law.  Aggregate Markov shocks and all
technology/policy primitives remain common across types. -/
structure BankPaymentLaw where
  support : Finset BankPayment
  probability : BankPayment → ℝ
  shock : BankPayment → ℝ
  depositCap : ℝ
  loanCap : ℝ
  probability_nonneg : ∀ ω, 0 ≤ probability ω
  probability_pos_on_support : ∀ ω, ω ∈ support → 0 < probability ω
  shock_gt_neg_one_on_support : ∀ ω, ω ∈ support → -1 < shock ω
  probability_zero_outside : ∀ ω, ω ∉ support → probability ω = 0
  probability_sum_one : ∑ ω ∈ support, probability ω = 1
  shock_mean_zero : ∑ ω ∈ support, probability ω * shock ω = 0
  caps_nonneg : 0 ≤ depositCap ∧ 0 ≤ loanCap

/-- Replace only the idiosyncratic payment law for one bank type. -/
def Primitives.withBankPaymentLaw {S : Type*} [Fintype S]
    (P : Primitives S) (L : BankPaymentLaw) :
    Primitives S :=
  { P with
    paymentSupport := L.support
    paymentProbability := L.probability
    paymentShock := L.shock
    bankDepositCap := L.depositCap
    bankLoanCap := L.loanCap
    payment_probability_nonneg := L.probability_nonneg
    payment_probability_pos_on_support := L.probability_pos_on_support
    payment_shock_gt_neg_one_on_support := L.shock_gt_neg_one_on_support
    payment_probability_zero_outside := L.probability_zero_outside
    payment_probability_sum_one := L.probability_sum_one
    payment_shock_mean_zero := L.shock_mean_zero
    bank_caps_nonneg := L.caps_nonneg }

/-- Replacing a primitive payment law by a bank law with exactly the same
support, probabilities, shocks and caps leaves the primitive economy
unchanged.  Proof fields coincide by proof irrelevance. -/
theorem Primitives.withBankPaymentLaw_eq
    {S : Type*} [Fintype S]
    (P : Primitives S) (L : BankPaymentLaw)
    (hsupport : L.support = P.paymentSupport)
    (hprobability : L.probability = P.paymentProbability)
    (hshock : L.shock = P.paymentShock)
    (hdepositCap : L.depositCap = P.bankDepositCap)
    (hloanCap : L.loanCap = P.bankLoanCap) :
    P.withBankPaymentLaw L = P := by
  cases P
  cases L
  simp_all only [Primitives.withBankPaymentLaw]

/-- The bank payment law already carried by the primitive economy, repackaged
as a type-level law.  This is the common ex-ante law used by the concrete
mass-one bank construction; it adds no distributional assumption. -/
def Primitives.primitiveBankPaymentLaw {S : Type*} [Fintype S]
    (P : Primitives S) : BankPaymentLaw where
  support := P.paymentSupport
  probability := P.paymentProbability
  shock := P.paymentShock
  depositCap := P.bankDepositCap
  loanCap := P.bankLoanCap
  probability_nonneg := P.payment_probability_nonneg
  probability_pos_on_support := P.payment_probability_pos_on_support
  shock_gt_neg_one_on_support := P.payment_shock_gt_neg_one_on_support
  probability_zero_outside := P.payment_probability_zero_outside
  probability_sum_one := P.payment_probability_sum_one
  shock_mean_zero := P.payment_shock_mean_zero
  caps_nonneg := P.bank_caps_nonneg

@[simp] theorem Primitives.with_primitiveBankPaymentLaw
    {S : Type*} [Fintype S] (P : Primitives S) :
    P.withBankPaymentLaw P.primitiveBankPaymentLaw = P := by
  apply Primitives.withBankPaymentLaw_eq <;> rfl

/-- Predetermined positions.  Capital and nominal faces, rather than current
real wealth, are fixed across the paper's local branch comparisons. -/
structure InheritedState where
  capital : FirmType → ℝ
  firmFace : FirmType → ℝ
  bankFace : ℝ
  householdDeposits : ℝ
  householdBonds : ℝ
  depositRateLag : ℝ
  governmentBondRateLag : ℝ
  reserveRateLag : ℝ
  /-- Lagged reserves before payments, which enter the quantity rule. -/
  reservesPreLag : ℝ
  /-- Lagged reserves after payments, which enter the public budget. -/
  reservesLag : ℝ
  facilityRateLag : ℝ
  facilityBorrowingLag : ℝ

/-- Give one bank type its own inherited nominal face without altering the
common physical, household or public inherited state. -/
def InheritedState.withBankFace (I : InheritedState) (face : ℝ) : InheritedState :=
  { I with bankFace := face }

/-- Endogenous plan on the finite-support tree.  Separate before-payment,
OTC-settlement, and after-payment positions make the institutional order
explicit. -/
structure Allocation (S : Type*) where
  firmConsumption : FirmType → AdaptedProcess S
  workerConsumption : AdaptedProcess S
  workerLabor : AdaptedProcess S
  capital : FirmType → AdaptedProcess S
  aggregateCapital : AdaptedProcess S
  labor : FirmType → AdaptedProcess S
  loan : FirmType → AdaptedProcess S
  firmDeposit : FirmType → AdaptedProcess S
  firmFace : FirmType → AdaptedProcess S
  firmWealth : FirmType → AdaptedProcess S
  collateralDual : FirmType → AdaptedProcess S
  inputPrice : AdaptedProcess S
  wage : AdaptedProcess S
  inflation : AdaptedProcess S
  capitalPrice : AdaptedProcess S
  loanRate : AdaptedProcess S
  depositRate : AdaptedProcess S
  reserveRate : AdaptedProcess S
  interbankRate : AdaptedProcess S
  facilityRate : AdaptedProcess S
  bankTightness : AdaptedProcess S
  /-- Market aggregates.  Individual bank-type portfolios used in Bellman and
  KKT arguments live in `BankPlan`/`BankPopulationAt` below. -/
  reservesPrePayment : AdaptedProcess S
  reservesPostPayment : AdaptedProcess S
  bankLoans : AdaptedProcess S
  bankDeposits : AdaptedProcess S
  bankEquity : AdaptedProcess S
  bankRetainedEquity : AdaptedProcess S
  bankDividend : AdaptedProcess S
  bankNetIncome : AdaptedProcess S
  retailerNetIncome : AdaptedProcess S
  capitalProducerNetIncome : AdaptedProcess S
  /-- Net aggregate OTC position (zero in clearing). -/
  interbankPosition : AdaptedProcess S
  /-- Aggregate central-bank facility lending after payments. -/
  facilityBorrowing : AdaptedProcess S
  householdDeposits : AdaptedProcess S
  householdBonds : AdaptedProcess S
  centralBankBonds : AdaptedProcess S
  governmentBondRate : AdaptedProcess S
  tax : AdaptedProcess S
  output : AdaptedProcess S
  investment : AdaptedProcess S
  capitalCreationCost : AdaptedProcess S
  priceAdjustmentResourceCost : AdaptedProcess S
  retailerLogRelativePrice : AdaptedProcess S

variable {S : Type*} [Fintype S] [DecidableEq S]

def signedFace (loanRate loan depositRate deposit : ℝ) : ℝ :=
  loanRate * loan - depositRate * deposit

/-- Backwards-compatible names for the unique signed-position vocabulary owned
by `FinancialCore`.  These are transparent aliases, not parallel definitions. -/
noncomputable abbrev recoveredLoan := signedLoanPosition
noncomputable abbrev recoveredDeposit := signedDepositPosition

/-- A firm plan used for literal individual deviations while aggregate prices
and the inherited position remain fixed. -/
structure FirmPlan (S : Type*) where
  consumption : AdaptedProcess S
  capital : AdaptedProcess S
  labor : AdaptedProcess S
  loan : AdaptedProcess S
  deposit : AdaptedProcess S
  face : AdaptedProcess S
  wealth : AdaptedProcess S

/-- A firm plan in the signed-funding representation of Lemma 3.4.  All
nonfinancial controls and the endogenous wealth process remain visible; only
the redundant gross loan/deposit pair is replaced by its nominal face. -/
structure SignedFirmPlan (S : Type*) where
  consumption : AdaptedProcess S
  capital : AdaptedProcess S
  labor : AdaptedProcess S
  face : AdaptedProcess S
  wealth : AdaptedProcess S

def firmPlanOfAllocation (X : Allocation S) (i : FirmType) : FirmPlan S where
  consumption := X.firmConsumption i
  capital := X.capital i
  labor := X.labor i
  loan := X.loan i
  deposit := X.firmDeposit i
  face := X.firmFace i
  wealth := X.firmWealth i

/-- Fibrewise cash gain obtained by replacing a gross portfolio by the
recovered portfolio with the same nominal face. -/
noncomputable def firmFundingCashGain (X : Allocation S) (p : FirmPlan S)
    (t : ℕ) (h : History S t) : ℝ :=
  fundingCash (X.loanRate t h) (X.depositRate t h) (p.face t h) -
    (p.loan t h - p.deposit t h)

/-- Gross-to-signed transformation in the source proof.  Capital, labour,
prices, the nominal face, and future wealth are unchanged; all extra current
cash is consumed in the same history. -/
noncomputable def signedFirmPlanOfGross (X : Allocation S)
    (p : FirmPlan S) : SignedFirmPlan S where
  consumption := fun t h ↦ p.consumption t h + firmFundingCashGain X p t h
  capital := p.capital
  labor := p.labor
  face := p.face
  wealth := p.wealth

/-- The recovered gross implementation of a gross plan's signed face. -/
noncomputable def recoveredFirmPlan (X : Allocation S) (p : FirmPlan S) : FirmPlan S where
  consumption := fun t h ↦ p.consumption t h + firmFundingCashGain X p t h
  capital := p.capital
  labor := p.labor
  loan := fun t h ↦ signedLoanPosition (X.loanRate t h) (p.face t h)
  deposit := fun t h ↦ signedDepositPosition (X.depositRate t h) (p.face t h)
  face := p.face
  wealth := p.wealth

/-- Inverse implementation of every signed plan by source equation
`(signed_positions_recovery)`. -/
noncomputable def grossFirmPlanOfSigned (X : Allocation S)
    (p : SignedFirmPlan S) : FirmPlan S where
  consumption := p.consumption
  capital := p.capital
  labor := p.labor
  loan := fun t h ↦ signedLoanPosition (X.loanRate t h) (p.face t h)
  deposit := fun t h ↦ signedDepositPosition (X.depositRate t h) (p.face t h)
  face := p.face
  wealth := p.wealth

/-- A history is economically admissible precisely when it has positive
probability under the recurrent tree.  Lemma 3.4's strict-improvement argument
is applied only at such nodes. -/
def FirmHistoryAdmissible (P : Primitives S) (t : ℕ) (h : History S t) : Prop :=
  0 < P.tree.historyWeight t h

/-- Recover the gross loan/deposit portfolio at exactly one date/history,
spending the local cash gain there and leaving every other node unchanged.
This is the source proof's finite perturbation; it does not assume that a
simultaneous transformation at infinitely many nodes preserves the objective
domain. -/
noncomputable def recoveredFirmPlanAt (X : Allocation S) (p : FirmPlan S)
    (t : ℕ) (h : History S t) : FirmPlan S where
  consumption := Function.update p.consumption t <|
    Function.update (p.consumption t) h
      (p.consumption t h + firmFundingCashGain X p t h)
  capital := p.capital
  labor := p.labor
  loan := Function.update p.loan t <|
    Function.update (p.loan t) h
      (signedLoanPosition (X.loanRate t h) (p.face t h))
  deposit := Function.update p.deposit t <|
    Function.update (p.deposit t) h
      (signedDepositPosition (X.depositRate t h) (p.face t h))
  face := p.face
  wealth := p.wealth

/-- Changing one term of a real series preserves summability. -/
theorem summable_iff_of_eq_off_one (f g : ℕ → ℝ) (n : ℕ)
    (hfg : ∀ m, m ≠ n → f m = g m) : Summable f ↔ Summable g := by
  have hdiff : Summable (fun m ↦ f m - g m) :=
    (hasSum_single n (fun m hm ↦ by rw [hfg m hm]; ring)).summable
  constructor
  · intro hf
    have h := hf.sub hdiff
    exact h.congr (fun m ↦ by ring)
  · intro hg
    have hdiff' : Summable (fun m ↦ g m - f m) :=
      (hasSum_single n (fun m hm ↦ by rw [hfg m hm]; ring)).summable
    have h := hg.sub hdiff'
    exact h.congr (fun m ↦ by ring)

noncomputable def firmUtilityTerm (P : Primitives S) (p : FirmPlan S) (t : ℕ) : ℝ :=
  P.entrepreneurDiscount ^ t *
    P.tree.expectationAt t
      (fun h ↦ crraUtility P.entrepreneurRiskAversion (p.consumption t h))

/-- The source compares only plans whose discounted utility is well defined.
This explicit predicate prevents `tsum`'s nonsummable fallback from carrying
economic meaning. -/
def FirmObjectiveWellDefined (P : Primitives S) (p : FirmPlan S) : Prop :=
  Summable (firmUtilityTerm P p)

/-- The one-node recovery avoids the global `Summable` closure problem: its
discounted utility series differs from the original at only one date. -/
theorem recoveredFirmPlanAt_objectiveWellDefined_iff
    (P : Primitives S) (X : Allocation S) (p : FirmPlan S)
    (t : ℕ) (h : History S t) :
    FirmObjectiveWellDefined P (recoveredFirmPlanAt X p t h) ↔
      FirmObjectiveWellDefined P p := by
  apply summable_iff_of_eq_off_one _ _ t
  intro m hm
  unfold firmUtilityTerm recoveredFirmPlanAt
  simp [Function.update_of_ne hm]

noncomputable def discountedFirmUtility (P : Primitives S) (p : FirmPlan S) : ℝ :=
  ∑' t : ℕ, firmUtilityTerm P p t

noncomputable def signedFirmUtilityTerm (P : Primitives S)
    (p : SignedFirmPlan S) (t : ℕ) : ℝ :=
  P.entrepreneurDiscount ^ t *
    P.tree.expectationAt t
      (fun h ↦ crraUtility P.entrepreneurRiskAversion (p.consumption t h))

def SignedFirmObjectiveWellDefined (P : Primitives S) (p : SignedFirmPlan S) : Prop :=
  Summable (signedFirmUtilityTerm P p)

noncomputable def discountedSignedFirmUtility (P : Primitives S)
    (p : SignedFirmPlan S) : ℝ :=
  ∑' t : ℕ, signedFirmUtilityTerm P p t

/-- Uniform price/rate box used only by later sufficient boundedness lemmas.
It is deliberately not part of the economic feasible set of Lemma 3.4. -/
def FirmPriceRateBounds (X : Allocation S) : Prop :=
  ∃ lower upper, 0 < lower ∧ lower ≤ upper ∧
    ∀ t h,
      lower ≤ X.depositRate t h ∧ X.depositRate t h ≤ X.loanRate t h ∧
      X.loanRate t h ≤ upper ∧ lower ≤ X.inflation t h ∧
      X.inflation t h ≤ upper ∧ lower ≤ X.capitalPrice t h ∧
      X.capitalPrice t h ≤ upper

/-- Exact source terminal term `βᵀ λᵀ Aᵀ` for a gross plan.  The
marginal is CRRA marginal utility and the portfolio is valued at current
prices.  This condition is separate from economic feasibility. -/
noncomputable def firmTerminalTerm (P : Primitives S) (X : Allocation S)
    (p : FirmPlan S) (T : ℕ) : ℝ :=
  P.entrepreneurDiscount ^ T * P.tree.expectationAt T (fun h ↦
    p.consumption T h ^ (-P.entrepreneurRiskAversion) *
      (X.capitalPrice T h * p.capital T h - p.loan T h + p.deposit T h))

def FirmSourceTerminalCondition (P : Primitives S) (X : Allocation S)
    (p : FirmPlan S) : Prop :=
  Tendsto (firmTerminalTerm P X p) atTop (nhds 0)

/-- Signed version of the exact source terminal term, using the recovered
deposit represented by the negative face. -/
noncomputable def signedFirmTerminalTerm (P : Primitives S) (X : Allocation S)
    (p : SignedFirmPlan S) (T : ℕ) : ℝ :=
  P.entrepreneurDiscount ^ T * P.tree.expectationAt T (fun h ↦
    p.consumption T h ^ (-P.entrepreneurRiskAversion) *
      (X.capitalPrice T h * p.capital T h +
        signedDepositPosition (X.depositRate T h) (p.face T h) -
        signedLoanPosition (X.loanRate T h) (p.face T h)))

def SignedFirmSourceTerminalCondition (P : Primitives S) (X : Allocation S)
    (p : SignedFirmPlan S) : Prop :=
  Tendsto (signedFirmTerminalTerm P X p) atTop (nhds 0)

/-- The source minimum is taken only over conditionally possible children;
ties are retained. -/
def SupportedWorstChildValue (P : Primitives S) (X : Allocation S)
    (t : ℕ) (h : History S t) (value : ℝ) : Prop :=
  (∀ s, 0 < P.tree.transition (currentState h) s →
    value ≤ X.inflation (t + 1) (childHistory h s) *
      X.capitalPrice (t + 1) (childHistory h s)) ∧
  ∃ s, 0 < P.tree.transition (currentState h) s ∧
    value = X.inflation (t + 1) (childHistory h s) *
      X.capitalPrice (t + 1) (childHistory h s)

/-- Source sufficient bound for the firm terminal term: consumption is
separated from zero and the current-price portfolio is uniformly bounded.
This predicate deliberately does not assume the terminal conclusion. -/
def FirmValuedPortfolioBounds (P : Primitives S) (X : Allocation S)
    (p : FirmPlan S) : Prop :=
  ∃ consumptionFloor portfolioBound, 0 < consumptionFloor ∧
    0 ≤ portfolioBound ∧
    ∀ t h, FirmHistoryAdmissible P t h →
      consumptionFloor ≤ p.consumption t h ∧
      0 ≤ X.capitalPrice t h * p.capital t h + p.deposit t h ∧
      X.capitalPrice t h * p.capital t h + p.deposit t h ≤ portfolioBound

/-- The exact positive net-capital-cost margin `q-H/Rᴸ`, with `H` built from
the endogenous worst supported child rather than from a selected child. -/
def FirmPositiveNetCapitalCost (P : Primitives S) (X : Allocation S)
    (i : FirmType) : Prop :=
  ∀ t h, FirmHistoryAdmissible P t h →
    ∃ liquidation, SupportedWorstChildValue P X t h liquidation ∧
      0 < X.capitalPrice t h -
        P.pledgeability i * (1 - P.depreciation) * liquidation /
          X.loanRate t h

/-- Joint concavity of the source operating-profit technology on nonnegative
capital and labour.  For the stated decreasing-returns Cobb--Douglas primitive
this is a derived technological property, not an optimality certificate. -/
def FirmOperatingProfitConcave (P : Primitives S) (X : Allocation S)
    (i : FirmType) : Prop :=
  ∀ t h, FirmHistoryAdmissible P t h →
    ConcaveOn ℝ (Set.Ici (0 : ℝ) ×ˢ Set.Ici (0 : ℝ))
      (fun kl : ℝ × ℝ ↦ operatingProfit (X.inputPrice t h)
        (P.aggregateProductivity (currentState h) * P.productivity i)
        kl.1 kl.2 P.alpha P.beta (X.wage t h))

/-- Strong bounds sufficient for objective closure and the exact terminal
condition.  They are an auxiliary infinite-horizon class, not the competitors
quantified by `FirmFeasible`. -/
def FirmPlanSourceAdmissible (P : Primitives S) (X : Allocation S)
    (p : FirmPlan S) : Prop :=
  FirmPriceRateBounds X ∧
  ∃ consumptionFloor bound, 0 < consumptionFloor ∧ 0 ≤ bound ∧
    (∀ t h,
      consumptionFloor ≤ p.consumption t h ∧
      |p.consumption t h| ≤ bound ∧ |p.capital t h| ≤ bound ∧
      |p.labor t h| ≤ bound ∧ |p.loan t h| ≤ bound ∧
      |p.deposit t h| ≤ bound ∧ |p.face t h| ≤ bound ∧
      |p.wealth t h| ≤ bound ∧
      0 ≤ X.capitalPrice t h * p.capital t h + p.deposit t h ∧
      X.capitalPrice t h * p.capital t h + p.deposit t h ≤ bound) ∧
    FirmSourceTerminalCondition P X p

/-- Signed strong-bounds class used by later sufficient closure lemmas. -/
def SignedFirmPlanSourceAdmissible (P : Primitives S) (X : Allocation S)
    (p : SignedFirmPlan S) : Prop :=
  FirmPriceRateBounds X ∧
  ∃ consumptionFloor bound, 0 < consumptionFloor ∧ 0 ≤ bound ∧
    (∀ t h,
      consumptionFloor ≤ p.consumption t h ∧
      |p.consumption t h| ≤ bound ∧ |p.capital t h| ≤ bound ∧
      |p.labor t h| ≤ bound ∧ |p.face t h| ≤ bound ∧
      |p.wealth t h| ≤ bound ∧
      0 ≤ X.capitalPrice t h * p.capital t h +
        signedDepositPosition (X.depositRate t h) (p.face t h) ∧
      X.capitalPrice t h * p.capital t h +
        signedDepositPosition (X.depositRate t h) (p.face t h) ≤ bound) ∧
    SignedFirmSourceTerminalCondition P X p

/-- Complete firm admissibility at the prices of `X`.  It includes positivity,
nominal/real timing, budget, signed-face identity, capital transition, and the
robust constraint at every child. -/
def FirmFeasible (P : Primitives S) (I : InheritedState)
    (X : Allocation S) (i : FirmType) (p : FirmPlan S) : Prop :=
  (∀ t h, FirmHistoryAdmissible P t h →
    0 < p.consumption t h ∧ 0 ≤ p.capital t h ∧
    0 ≤ p.labor t h ∧ 0 ≤ p.loan t h ∧ 0 ≤ p.deposit t h) ∧
  (∀ t h, FirmHistoryAdmissible P t h →
    p.face t h = signedFace (X.loanRate t h) (p.loan t h)
      (X.depositRate t h) (p.deposit t h)) ∧
  (∀ t h, FirmHistoryAdmissible P t h →
    p.consumption t h + X.capitalPrice t h * p.capital t h + p.deposit t h =
      p.wealth t h + p.loan t h) ∧
  (∀ t h, FirmHistoryAdmissible P t h →
    RobustCollateral (P.pledgeability i) P.depreciation
      (X.loanRate t h) (p.loan t h) (p.capital t h)
      (fun s ↦ 0 < P.tree.transition (currentState h) s)
      (fun s ↦ X.inflation (t + 1) (childHistory h s))
      (fun s ↦ X.capitalPrice (t + 1) (childHistory h s))) ∧
  (∀ h, FirmHistoryAdmissible P 0 h →
    p.wealth 0 h =
      operatingProfit (X.inputPrice 0 h)
        (P.aggregateProductivity (currentState h) * P.productivity i) (I.capital i)
        (p.labor 0 h) P.alpha P.beta (X.wage 0 h) +
      X.capitalPrice 0 h * (1 - P.depreciation) * I.capital i -
      realRepayment (I.firmFace i) (X.inflation 0 h)) ∧
  (∀ t h s, FirmHistoryAdmissible P (t + 1) (childHistory h s) →
    p.wealth (t + 1) (childHistory h s) =
      operatingProfit (X.inputPrice (t + 1) (childHistory h s))
          (P.aggregateProductivity s * P.productivity i) (p.capital t h)
        (p.labor (t + 1) (childHistory h s)) P.alpha P.beta
        (X.wage (t + 1) (childHistory h s)) +
      X.capitalPrice (t + 1) (childHistory h s) *
        (1 - P.depreciation) * p.capital t h -
      realRepayment (p.face t h)
        (X.inflation (t + 1) (childHistory h s)))

/-- Complete signed-plan admissibility at the same fixed aggregate prices as
`FirmFeasible`.  It retains labour, wealth, robust child-by-child collateral,
and the full intertemporal timing rather than replacing them by a free
continuation-value function.  Positive capital is literal here because Lemma
3.4 explicitly excludes the zero-capital corner. -/
def SignedFirmFeasible (P : Primitives S) (I : InheritedState)
    (X : Allocation S) (i : FirmType) (p : SignedFirmPlan S) : Prop :=
  (∀ t h, FirmHistoryAdmissible P t h →
    0 < p.consumption t h ∧ 0 < p.capital t h ∧ 0 ≤ p.labor t h) ∧
  (∀ t h, FirmHistoryAdmissible P t h →
    p.consumption t h + X.capitalPrice t h * p.capital t h =
      p.wealth t h + fundingCash (X.loanRate t h) (X.depositRate t h) (p.face t h)) ∧
  (∀ t h, FirmHistoryAdmissible P t h → ∀ s,
    0 < P.tree.transition (currentState h) s →
      p.face t h ≤ P.pledgeability i * (1 - P.depreciation) *
      (X.inflation (t + 1) (childHistory h s) *
        X.capitalPrice (t + 1) (childHistory h s)) * p.capital t h) ∧
  (∀ h, FirmHistoryAdmissible P 0 h →
    p.wealth 0 h =
      operatingProfit (X.inputPrice 0 h)
        (P.aggregateProductivity (currentState h) * P.productivity i) (I.capital i)
        (p.labor 0 h) P.alpha P.beta (X.wage 0 h) +
      X.capitalPrice 0 h * (1 - P.depreciation) * I.capital i -
      realRepayment (I.firmFace i) (X.inflation 0 h)) ∧
  (∀ t h s, FirmHistoryAdmissible P (t + 1) (childHistory h s) →
    p.wealth (t + 1) (childHistory h s) =
      operatingProfit (X.inputPrice (t + 1) (childHistory h s))
        (P.aggregateProductivity s * P.productivity i) (p.capital t h)
        (p.labor (t + 1) (childHistory h s)) P.alpha P.beta
        (X.wage (t + 1) (childHistory h s)) +
      X.capitalPrice (t + 1) (childHistory h s) *
        (1 - P.depreciation) * p.capital t h -
      realRepayment (p.face t h)
        (X.inflation (t + 1) (childHistory h s)))

def FirmPlanOptimal (P : Primitives S) (I : InheritedState)
    (X : Allocation S) (i : FirmType) (p : FirmPlan S) : Prop :=
  FirmFeasible P I X i p ∧ FirmObjectiveWellDefined P p ∧
    ∀ q, FirmFeasible P I X i q → FirmObjectiveWellDefined P q →
      discountedFirmUtility P q ≤ discountedFirmUtility P p

def SignedFirmPlanOptimal (P : Primitives S) (I : InheritedState)
    (X : Allocation S) (i : FirmType) (p : SignedFirmPlan S) : Prop :=
  SignedFirmFeasible P I X i p ∧ SignedFirmObjectiveWellDefined P p ∧
    ∀ q, SignedFirmFeasible P I X i q → SignedFirmObjectiveWellDefined P q →
      discountedSignedFirmUtility P q ≤ discountedSignedFirmUtility P p

/-- The gross problem in source Lemma 3.4 explicitly excludes the zero-capital
corner.  This predicate therefore uses exactly the positive-capital admissible
set on both the candidate and every competitor, rather than silently appealing
to the wider `FirmPlanOptimal` domain. -/
def PositiveCapitalFirmPlanOptimal (P : Primitives S) (I : InheritedState)
    (X : Allocation S) (i : FirmType) (p : FirmPlan S) : Prop :=
  FirmFeasible P I X i p ∧ (∀ t h, 0 < p.capital t h) ∧
    FirmObjectiveWellDefined P p ∧
    ∀ q, FirmFeasible P I X i q → (∀ t h, 0 < q.capital t h) →
      FirmObjectiveWellDefined P q →
      discountedFirmUtility P q ≤ discountedFirmUtility P p

def FirmOptimal (P : Primitives S) (I : InheritedState)
    (X : Allocation S) (i : FirmType) : Prop :=
  FirmFeasible P I X i (firmPlanOfAllocation X i) ∧
    FirmObjectiveWellDefined P (firmPlanOfAllocation X i) ∧
    FirmSourceTerminalCondition P X (firmPlanOfAllocation X i) ∧
    ∀ p, FirmFeasible P I X i p → FirmObjectiveWellDefined P p →
      discountedFirmUtility P p ≤
        discountedFirmUtility P (firmPlanOfAllocation X i)

/-- Household choices. Prices, taxes, and the three ownership-income streams
are deliberately absent: an individual deviation takes them from `X`. -/
structure HouseholdPlan (S : Type*) where
  consumption : AdaptedProcess S
  labor : AdaptedProcess S
  deposits : AdaptedProcess S
  bonds : AdaptedProcess S

def householdPlanOfAllocation (X : Allocation S) : HouseholdPlan S where
  consumption := X.workerConsumption
  labor := X.workerLabor
  deposits := X.householdDeposits
  bonds := X.householdBonds

noncomputable def householdUtilityTerm (P : Primitives S)
    (p : HouseholdPlan S) (t : ℕ) : ℝ :=
  P.workerDiscount ^ t * P.tree.expectationAt t (fun h ↦
    crraUtility P.workerRiskAversion (p.consumption t h) -
      P.laborScale * p.labor t h ^ (1 + P.laborCurvature) /
        (1 + P.laborCurvature))

def HouseholdObjectiveWellDefined (P : Primitives S) (p : HouseholdPlan S) : Prop :=
  Summable (householdUtilityTerm P p)

noncomputable def discountedHouseholdUtility (P : Primitives S)
    (p : HouseholdPlan S) : ℝ :=
  ∑' t : ℕ, householdUtilityTerm P p t

/-- Source household terminal term
`β_W^T u'_W(C_T)(D^W_T+G^H_T)`, in expectation on the recurrent tree. -/
noncomputable def householdTerminalTerm (P : Primitives S)
    (p : HouseholdPlan S) (T : ℕ) : ℝ :=
  P.workerDiscount ^ T * P.tree.expectationAt T (fun h ↦
    p.consumption T h ^ (-P.workerRiskAversion) *
      (p.deposits T h + p.bonds T h))

def HouseholdSourceTerminalCondition (P : Primitives S)
    (p : HouseholdPlan S) : Prop :=
  Tendsto (householdTerminalTerm P p) atTop (nhds 0)

/-- Exact household budget timing from (household): inherited nominal deposits
and bonds repay at date zero; thereafter the plan's preceding holdings repay.
Retail, capital-producer, and bank net income remain distinct and fixed under
an individual deviation. -/
def HouseholdFeasible (P : Primitives S) (I : InheritedState) (X : Allocation S)
    (p : HouseholdPlan S) : Prop :=
  (∀ t h, FirmHistoryAdmissible P t h →
    0 < p.consumption t h ∧ 0 ≤ p.labor t h ∧
    0 ≤ p.deposits t h ∧ 0 ≤ p.bonds t h) ∧
  (∀ h, FirmHistoryAdmissible P 0 h →
    p.consumption 0 h + p.deposits 0 h + p.bonds 0 h =
      X.wage 0 h * p.labor 0 h +
      (I.depositRateLag * I.householdDeposits +
        I.governmentBondRateLag * I.householdBonds) / X.inflation 0 h +
      X.retailerNetIncome 0 h + X.capitalProducerNetIncome 0 h +
      X.bankNetIncome 0 h - X.tax 0 h) ∧
  (∀ t h s, FirmHistoryAdmissible P (t + 1) (childHistory h s) →
    p.consumption (t + 1) (childHistory h s) +
        p.deposits (t + 1) (childHistory h s) +
        p.bonds (t + 1) (childHistory h s) =
      X.wage (t + 1) (childHistory h s) * p.labor (t + 1) (childHistory h s) +
      (X.depositRate t h * p.deposits t h +
        X.governmentBondRate t h * p.bonds t h) /
          X.inflation (t + 1) (childHistory h s) +
      X.retailerNetIncome (t + 1) (childHistory h s) +
      X.capitalProducerNetIncome (t + 1) (childHistory h s) +
      X.bankNetIncome (t + 1) (childHistory h s) -
      X.tax (t + 1) (childHistory h s))

/-- Commercial-bank balance sheet before the payment shock. -/
def BankBalance (P : Primitives S) (X : Allocation S) : Prop :=
  ∀ t h, FirmHistoryAdmissible P t h →
    X.bankLoans t h + X.reservesPrePayment t h =
      X.bankDeposits t h + X.bankRetainedEquity t h

/-- Central-bank to OTC to facility settlement.  Deposit transfers first
change reserves by `(R_D/R_R) ω D`; OTC positions clear in the payment
distribution before the residual facility changes post-payment reserves. -/
def SettlementClears (P : Primitives S) (X : Allocation S) : Prop :=
  ∀ t h, FirmHistoryAdmissible P t h →
    X.interbankPosition t h = 0 ∧ 0 ≤ X.facilityBorrowing t h ∧
    X.reservesPostPayment t h = X.reservesPrePayment t h +
      X.interbankPosition t h + X.facilityBorrowing t h

/-- The source payment/OTC settlement identities used by aggregate-flow
consolidation.  Deposit transfers change reserves by
`(R_D/R_R) ω D`; interbank positions then cancel in probability-weighted
aggregate, while the facility supplies the residual. -/
def ExactSettlementFlows (P : Primitives S) (X : Allocation S) : Prop :=
  SettlementClears P X

def CreditClears (P : Primitives S) (X : Allocation S) : Prop :=
  ∀ t h, FirmHistoryAdmissible P t h →
    X.bankLoans t h = ∑ i, P.mass i * X.loan i t h

def DepositsClear (P : Primitives S) (X : Allocation S) : Prop :=
  ∀ t h, FirmHistoryAdmissible P t h →
    X.bankDeposits t h = X.householdDeposits t h +
      ∑ i, P.mass i * X.firmDeposit i t h

def CapitalClears (P : Primitives S) (I : InheritedState) (X : Allocation S) : Prop :=
  (∀ h, FirmHistoryAdmissible P 0 h →
    X.aggregateCapital 0 h = ∑ i, P.mass i * I.capital i) ∧
  (∀ t h s, FirmHistoryAdmissible P (t + 1) (childHistory h s) →
    X.aggregateCapital (t + 1) (childHistory h s) =
      ∑ i, P.mass i * X.capital i t h) ∧
  (∀ t h, FirmHistoryAdmissible P t h →
    ∑ i, P.mass i * X.capital i t h =
      (1 - P.depreciation) * X.aggregateCapital t h + X.investment t h)

def LaborClears (P : Primitives S) (X : Allocation S) : Prop :=
  ∀ t h, FirmHistoryAdmissible P t h →
    X.workerLabor t h = ∑ i, P.mass i * X.labor i t h

def ResourceClears (P : Primitives S) (X : Allocation S) : Prop :=
  ∀ t h, FirmHistoryAdmissible P t h →
    X.workerConsumption t h +
        ∑ i, P.mass i * X.firmConsumption i t h +
        X.capitalCreationCost t h + X.priceAdjustmentResourceCost t h =
      X.output t h

noncomputable def expectedPostReserves (P : Primitives S) (X : Allocation S)
    (t : ℕ) (h : History S t) : ℝ :=
  X.reservesPostPayment t h

noncomputable def expectedFacilityBorrowing (P : Primitives S) (X : Allocation S)
    (t : ℕ) (h : History S t) : ℝ :=
  X.facilityBorrowing t h

/-- Consolidated Treasury--central-bank budget, including gross inherited
nominal claims and the facility repayment with its source sign. -/
def FiscalClosure (P : Primitives S) (I : InheritedState) (X : Allocation S) : Prop :=
  (∀ t h, FirmHistoryAdmissible P t h →
    X.householdBonds t h + X.centralBankBonds t h = P.governmentBondSupply) ∧
  (∀ t h, FirmHistoryAdmissible P t h →
    X.centralBankBonds t h = X.reservesPrePayment t h) ∧
  (∀ t h, FirmHistoryAdmissible P t h →
    X.centralBankBonds t h + expectedFacilityBorrowing P X t h =
    expectedPostReserves P X t h) ∧
  (∀ h, FirmHistoryAdmissible P 0 h →
    X.tax 0 h + X.householdBonds 0 h + expectedPostReserves P X 0 h -
        expectedFacilityBorrowing P X 0 h =
      (I.governmentBondRateLag * I.householdBonds +
        I.reserveRateLag * I.reservesLag -
        I.facilityRateLag * I.facilityBorrowingLag) / X.inflation 0 h) ∧
  (∀ t h s, FirmHistoryAdmissible P (t + 1) (childHistory h s) →
    X.tax (t + 1) (childHistory h s) +
        X.householdBonds (t + 1) (childHistory h s) +
        expectedPostReserves P X (t + 1) (childHistory h s) -
        expectedFacilityBorrowing P X (t + 1) (childHistory h s) =
      (X.governmentBondRate t h * X.householdBonds t h +
        X.reserveRate t h * expectedPostReserves P X t h -
        X.facilityRate t h * expectedFacilityBorrowing P X t h) /
          X.inflation (t + 1) (childHistory h s))

def PositiveDomain (P : Primitives S) (X : Allocation S) : Prop :=
  ∀ t h, FirmHistoryAdmissible P t h →
    0 < X.workerConsumption t h ∧
      (∀ i, 0 < X.firmConsumption i t h ∧ 0 < X.capital i t h) ∧
      0 < X.aggregateCapital t h ∧ 0 < X.output t h ∧
      0 < X.inputPrice t h ∧ 0 < X.wage t h ∧
      0 < X.inflation t h ∧ 0 < X.capitalPrice t h ∧
      0 < X.reserveRate t h ∧ 0 < X.depositRate t h ∧ 0 < X.loanRate t h ∧
      0 < P.corridorWidthPath t h ∧
      X.facilityRate t h = X.reserveRate t h + P.corridorWidthPath t h ∧
      0 ≤ (P.reserveRequirementPath t h) ∧ (P.reserveRequirementPath t h) < 1 ∧
      0 < X.reservesPrePayment t h

def HouseholdOptimal (P : Primitives S) (I : InheritedState) (X : Allocation S) : Prop :=
  let x := householdPlanOfAllocation X
  HouseholdFeasible P I X x ∧ HouseholdObjectiveWellDefined P x ∧
    HouseholdSourceTerminalCondition P x ∧
    ∀ p, HouseholdFeasible P I X p → HouseholdObjectiveWellDefined P p →
      discountedHouseholdUtility P p ≤ discountedHouseholdUtility P x

/-- A commercial bank's own controls. Aggregate prices and settlement rates
remain those of `X` under a deviation. -/
structure BankPlan (S : Type*) where
  equity : AdaptedProcess S
  dividend : AdaptedProcess S
  retainedEquity : AdaptedProcess S
  loans : AdaptedProcess S
  reservesPre : AdaptedProcess S
  deposits : AdaptedProcess S
  reservesPost : BankPayment → AdaptedProcess S
  interbank : BankPayment → AdaptedProcess S
  facility : BankPayment → AdaptedProcess S

def bankGrossReturn (P : Primitives S) (X : Allocation S) (p : BankPlan S)
    (ω : BankPayment)
    (t : ℕ) (h : History S t) : ℝ :=
  X.loanRate t h * p.loans t h + X.reserveRate t h * p.reservesPost ω t h -
    X.depositRate t h * p.deposits t h * (1 + P.paymentShock ω) -
    X.interbankRate t h * p.interbank ω t h -
    X.facilityRate t h * p.facility ω t h

noncomputable def expectedBankGrossReturn (P : Primitives S) (X : Allocation S)
    (p : BankPlan S) (t : ℕ) (h : History S t) : ℝ :=
  ∑ ω ∈ P.paymentSupport,
    P.paymentProbability ω * bankGrossReturn P X p ω t h

/-- Aggregate counterpart used only in aggregate renewal accounts.  This is
not an individual `BankPlan`: the three portfolio fields of `Allocation` are
market totals and are never fed to the individual Bellman/KKT problem. -/
noncomputable def aggregateBankGrossReturn (P : Primitives S) (X : Allocation S)
    (t : ℕ) (h : History S t) : ℝ :=
  X.loanRate t h * X.bankLoans t h +
    X.reserveRate t h * X.reservesPostPayment t h -
    X.depositRate t h * X.bankDeposits t h -
    X.interbankRate t h * X.interbankPosition t h -
    X.facilityRate t h * X.facilityBorrowing t h

noncomputable def expectedAggregateBankGrossReturn
    (P : Primitives S) (X : Allocation S) (t : ℕ) (h : History S t) : ℝ :=
  aggregateBankGrossReturn P X t h

/-- Equity-retention factor `a_B = 1-η_B+η_Bψ_B`. -/
def bankRenewalFactor (P : Primitives S) : ℝ :=
  1 - P.bankExit + P.bankExit * P.bankSeedShare

/-- Pre-exit bank equity, including the inherited nominal face at date zero and
the real repayment of the preceding portfolio thereafter. -/
noncomputable def bankPreExitEquity (P : Primitives S) (I : InheritedState)
    (X : Allocation S) : AdaptedProcess S
  | 0, h => I.bankFace / (bankRenewalFactor P * X.inflation 0 h)
  | t + 1, h =>
      expectedAggregateBankGrossReturn P X t (previousHistory h) /
        X.inflation (t + 1) h

/-- The source's retention, exit/seed renewal, and net owner-payment identities.
This is an accounting condition, not bank optimality. -/
def BankRenewalFlows (P : Primitives S) (I : InheritedState)
    (X : Allocation S) : Prop :=
  (∀ t h, FirmHistoryAdmissible P t h →
    X.bankRetainedEquity t h = X.bankEquity t h - X.bankDividend t h) ∧
  (∀ t h, FirmHistoryAdmissible P t h →
    X.bankEquity t h =
      bankRenewalFactor P *
        bankPreExitEquity P I X t h) ∧
  ∀ t h, FirmHistoryAdmissible P t h →
    X.bankNetIncome t h = X.bankDividend t h +
      P.bankExit * (1 - P.bankSeedShare) * bankPreExitEquity P I X t h

/-- Initial consistency of the household, firm, government, and bank nominal
faces.  This is the date-zero instance of the source identity
`Fᵂ = Σ vᵢ Fᵢ + Fᴳ - Fᴮ/a_B`; it prevents the flow theorem from
silently choosing unrelated inherited claims. -/
def InheritedNominalFaceConsistency (P : Primitives S) (I : InheritedState) : Prop :=
  0 < bankRenewalFactor P ∧
  I.depositRateLag * I.householdDeposits +
      I.governmentBondRateLag * I.householdBonds =
    ∑ i, P.mass i * I.firmFace i +
      (I.governmentBondRateLag * I.householdBonds +
        I.reserveRateLag * I.reservesLag -
        I.facilityRateLag * I.facilityBorrowingLag) -
      I.bankFace / bankRenewalFactor P

/-- Every current firm face is the nominal loan repayment net of the nominal
deposit repayment issued at that same history.  The inherited date-zero faces
remain governed separately by `InheritedNominalFaceConsistency`. -/
def CurrentNominalFaceConsistency (P : Primitives S) (X : Allocation S) : Prop :=
  ∀ i t h, FirmHistoryAdmissible P t h →
    X.firmFace i t h =
      X.loanRate t h * X.loan i t h - X.depositRate t h * X.firmDeposit i t h

/-- Individual-bank admissibility used in Bellman optimality: balance, leverage
limits, payment settlement, robust solvency, and the inherited nominal face.
Current real equity is not predetermined: date-zero inflation converts that
nominal promise into current goods.  Exit,
renewal and household seed transfers remain exclusively in
`BankRenewalFlows`; they are not Bellman feasibility constraints. -/
def BankFeasible (P : Primitives S) (I : InheritedState) (X : Allocation S)
    (p : BankPlan S) : Prop :=
  (∀ t h, FirmHistoryAdmissible P t h →
    0 < p.equity t h ∧ 0 ≤ p.dividend t h ∧
    0 < p.retainedEquity t h ∧ 0 ≤ p.loans t h ∧
    0 ≤ p.reservesPre t h ∧ 0 ≤ p.deposits t h) ∧
  (∀ t h, FirmHistoryAdmissible P t h →
    p.retainedEquity t h = p.equity t h - p.dividend t h) ∧
  (∀ t h, FirmHistoryAdmissible P t h → p.loans t h + p.reservesPre t h =
    p.deposits t h + p.retainedEquity t h) ∧
  (∀ t h, FirmHistoryAdmissible P t h →
    p.deposits t h ≤ P.bankDepositCap * p.retainedEquity t h ∧
    p.loans t h ≤ P.bankLoanCap * p.retainedEquity t h) ∧
  (∀ t h, FirmHistoryAdmissible P t h → ∀ ω, ω ∈ P.paymentSupport →
    0 ≤ p.facility ω t h ∧
    p.reservesPost ω t h = p.reservesPre t h +
      (X.depositRate t h / X.reserveRate t h) * P.paymentShock ω *
        p.deposits t h +
      p.interbank ω t h + p.facility ω t h ∧
    (P.reserveRequirementPath t h) * p.deposits t h * (1 + P.paymentShock ω) ≤
      p.reservesPost ω t h) ∧
  (∀ h, FirmHistoryAdmissible P 0 h →
    p.equity 0 h = I.bankFace / X.inflation 0 h) ∧
  (∀ t h, FirmHistoryAdmissible P t h → ∀ ω, ω ∈ P.paymentSupport → ∀ s,
    0 < P.tree.transition (currentState h) s →
      0 ≤ bankGrossReturn P X p ω t h /
        X.inflation (t + 1) (childHistory h s))

/-! ## Interior bank portfolio problem used by Proposition 3.8 -/

/-- The source's reduced nominal payoff before inflation, at fixed aggregate
prices and payment environment.  Only the bank's three portfolio controls
vary. -/
noncomputable def bankReducedPortfolioReturnWithShock
    (P : Primitives S) (X : Allocation S)
    (t : ℕ) (h : History S t) (deficitSlope surplusSlope loans reserves deposits
      shock : ℝ) : ℝ :=
  X.loanRate t h * loans + X.reserveRate t h * reserves -
    X.depositRate t h * deposits +
    otcLiquidityPayoff deficitSlope surplusSlope
      (bankSettlementSurplus reserves (P.reserveRequirementPath t h)
        (X.depositRate t h / X.reserveRate t h) deposits shock)

noncomputable def bankReducedPortfolioReturn (P : Primitives S) (X : Allocation S)
    (t : ℕ) (h : History S t) (deficitSlope surplusSlope loans reserves deposits : ℝ)
    (ω : BankPayment) : ℝ :=
  bankReducedPortfolioReturnWithShock P X t h deficitSlope surplusSlope
    loans reserves deposits (P.paymentShock ω)

/-- A finite bank-type population at one history.  Each type has its own
finite payment support and per-bank portfolio.  The candidate type is linked
only to the primitive payment law used in its Bellman problem, never to the
market-aggregate fields of `Allocation`. -/
def BankPopulationAt {J : Type*} [Fintype J]
    (P : Primitives S) (X : Allocation S) (t : ℕ) (h : History S t)
    (mass retainedEquity loans reserves deposits : J → ℝ)
    (depositCapByType loanCapByType : J → ℝ)
    (paymentSupportByType : J → Finset BankPayment)
    (paymentProbabilityByType paymentShockByType : J → BankPayment → ℝ)
    (candidateType : J) : Prop :=
  (∀ j, 0 < mass j) ∧
  (∀ j, 0 < retainedEquity j) ∧
  (∀ j, 0 ≤ depositCapByType j ∧ 0 ≤ loanCapByType j) ∧
  (∀ j, 0 ≤ loans j ∧ 0 ≤ reserves j ∧ 0 ≤ deposits j) ∧
  (∀ j, loans j + reserves j = deposits j + retainedEquity j) ∧
  (∀ j, deposits j ≤ depositCapByType j * retainedEquity j ∧
    loans j ≤ loanCapByType j * retainedEquity j) ∧
  (∀ j ω, 0 ≤ paymentProbabilityByType j ω) ∧
  (∀ j ω, ω ∈ paymentSupportByType j → 0 < paymentProbabilityByType j ω) ∧
  (∀ j ω, ω ∈ paymentSupportByType j → -1 < paymentShockByType j ω) ∧
  (∀ j ω, ω ∉ paymentSupportByType j → paymentProbabilityByType j ω = 0) ∧
  (∀ j, ∑ ω ∈ paymentSupportByType j, paymentProbabilityByType j ω = 1) ∧
  (∀ j, ∑ ω ∈ paymentSupportByType j,
    paymentProbabilityByType j ω * paymentShockByType j ω = 0) ∧
  paymentSupportByType candidateType = P.paymentSupport ∧
  paymentProbabilityByType candidateType = P.paymentProbability ∧
  paymentShockByType candidateType = P.paymentShock ∧
  depositCapByType candidateType = P.bankDepositCap ∧
  loanCapByType candidateType = P.bankLoanCap

/-- Source aggregate reserve deficits `S⁻ = Σ_j u_j E_ω[(-s_j)₊]`. -/
noncomputable def bankDeficitSupplyAt {J : Type*} [Fintype J]
    (P : Primitives S) (X : Allocation S) (t : ℕ) (h : History S t)
    (mass reserves deposits : J → ℝ)
    (paymentSupportByType : J → Finset BankPayment)
    (paymentProbabilityByType paymentShockByType : J → BankPayment → ℝ) : ℝ :=
  ∑ j, mass j * finiteSupportExpectation (paymentSupportByType j)
    (paymentProbabilityByType j) (fun ω ↦
    max (-bankSettlementSurplus (reserves j)
      (P.reserveRequirementPath t h) (X.depositRate t h / X.reserveRate t h)
      (deposits j) (paymentShockByType j ω)) 0)

/-- Source aggregate reserve surpluses `S⁺ = Σ_j u_j E_ω[(s_j)₊]`. -/
noncomputable def bankSurplusSupplyAt {J : Type*} [Fintype J]
    (P : Primitives S) (X : Allocation S) (t : ℕ) (h : History S t)
    (mass reserves deposits : J → ℝ)
    (paymentSupportByType : J → Finset BankPayment)
    (paymentProbabilityByType paymentShockByType : J → BankPayment → ℝ) : ℝ :=
  ∑ j, mass j * finiteSupportExpectation (paymentSupportByType j)
    (paymentProbabilityByType j) (fun ω ↦
    max (bankSettlementSurplus (reserves j)
      (P.reserveRequirementPath t h) (X.depositRate t h / X.reserveRate t h)
      (deposits j) (paymentShockByType j ω)) 0)

/-- OTC position of one bank type, expressed from that type's own settlement
surplus rather than from any aggregate `Allocation` field. -/
noncomputable def bankTypeOTCInterbankAt (P : Primitives S)
    (tightness surplus : ℝ) : ℝ :=
  if surplus < 0 then
    -otcDeficitMatchFraction P.matchingIntensity tightness * surplus
  else
    -otcSurplusMatchFraction P.matchingIntensity tightness * surplus

/-- Source OTC clearing `Σ_j u_j E f_j = 0`. -/
def BankTypeSettlementClearsAt {J : Type*} [Fintype J]
    (P : Primitives S) (X : Allocation S) (t : ℕ) (h : History S t)
    (mass reserves deposits : J → ℝ)
    (paymentSupportByType : J → Finset BankPayment)
    (paymentProbabilityByType paymentShockByType : J → BankPayment → ℝ)
    (tightness : ℝ) : Prop :=
  ∑ j, mass j * finiteSupportExpectation (paymentSupportByType j)
    (paymentProbabilityByType j) (fun ω ↦
      bankTypeOTCInterbankAt P tightness
        (bankSettlementSurplus (reserves j) (P.reserveRequirementPath t h)
          (X.depositRate t h / X.reserveRate t h) (deposits j)
          (paymentShockByType j ω))) = 0

theorem bankTypeOTCInterbankAt_eq_matchFractions
    (P : Primitives S) (tightness surplus : ℝ) :
    bankTypeOTCInterbankAt P tightness surplus =
      otcDeficitMatchFraction P.matchingIntensity tightness * max (-surplus) 0 -
        otcSurplusMatchFraction P.matchingIntensity tightness * max surplus 0 := by
  unfold bankTypeOTCInterbankAt
  by_cases hs : surplus < 0
  · simp [hs, le_of_lt hs, neg_nonneg.mpr (le_of_lt hs)]
  · have hs0 : 0 ≤ surplus := le_of_not_gt hs
    simp [hs, hs0]

theorem bankTypeSettlementAggregate_eq {J : Type*} [Fintype J]
    (P : Primitives S) (X : Allocation S) (t : ℕ) (h : History S t)
    (mass reserves deposits : J → ℝ)
    (paymentSupportByType : J → Finset BankPayment)
    (paymentProbabilityByType paymentShockByType : J → BankPayment → ℝ)
    (tightness : ℝ) :
    (∑ j, mass j * finiteSupportExpectation (paymentSupportByType j)
      (paymentProbabilityByType j) (fun ω ↦
        bankTypeOTCInterbankAt P tightness
          (bankSettlementSurplus (reserves j) (P.reserveRequirementPath t h)
            (X.depositRate t h / X.reserveRate t h) (deposits j)
            (paymentShockByType j ω)))) =
      otcDeficitMatchFraction P.matchingIntensity tightness *
          bankDeficitSupplyAt P X t h mass reserves deposits paymentSupportByType
            paymentProbabilityByType paymentShockByType -
        otcSurplusMatchFraction P.matchingIntensity tightness *
          bankSurplusSupplyAt P X t h mass reserves deposits paymentSupportByType
            paymentProbabilityByType paymentShockByType := by
  classical
  have htype : ∀ j,
      finiteSupportExpectation (paymentSupportByType j) (paymentProbabilityByType j)
        (fun ω ↦ bankTypeOTCInterbankAt P tightness
          (bankSettlementSurplus (reserves j) (P.reserveRequirementPath t h)
            (X.depositRate t h / X.reserveRate t h) (deposits j)
            (paymentShockByType j ω))) =
        otcDeficitMatchFraction P.matchingIntensity tightness *
          finiteSupportExpectation (paymentSupportByType j)
            (paymentProbabilityByType j) (fun ω ↦
              max (-bankSettlementSurplus (reserves j)
                (P.reserveRequirementPath t h)
                (X.depositRate t h / X.reserveRate t h) (deposits j)
                (paymentShockByType j ω)) 0) -
        otcSurplusMatchFraction P.matchingIntensity tightness *
          finiteSupportExpectation (paymentSupportByType j)
            (paymentProbabilityByType j) (fun ω ↦
              max (bankSettlementSurplus (reserves j)
                (P.reserveRequirementPath t h)
                (X.depositRate t h / X.reserveRate t h) (deposits j)
                (paymentShockByType j ω)) 0) := by
    intro j
    simp_rw [bankTypeOTCInterbankAt_eq_matchFractions]
    rw [finiteSupportExpectation_sub, finiteSupportExpectation_const_mul,
      finiteSupportExpectation_const_mul]
  simp_rw [htype, mul_sub]
  rw [Finset.sum_sub_distrib]
  unfold bankDeficitSupplyAt bankSurplusSupplyAt
  congr 1
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring

theorem otcMatchingFractions_clear
    (matchingIntensity deficitSupply surplusSupply tightness : ℝ)
    (H : BilateralOTCActivity deficitSupply surplusSupply tightness) :
    otcDeficitMatchFraction matchingIntensity tightness * deficitSupply =
      otcSurplusMatchFraction matchingIntensity tightness * surplusSupply := by
  rcases H with ⟨hdeficit, hsurplus, htightness⟩
  have htightness_pos : 0 < tightness := by
    rw [htightness]
    exact div_pos hdeficit hsurplus
  have hratio : deficitSupply = tightness * surplusSupply := by
    rw [htightness]
    field_simp [ne_of_gt hsurplus]
  by_cases hle : tightness ≤ 1
  · simp only [otcDeficitMatchFraction, otcSurplusMatchFraction, if_pos hle]
    rw [hratio]
    ring
  · simp only [otcDeficitMatchFraction, otcSurplusMatchFraction, if_neg hle]
    rw [hratio]
    field_simp [ne_of_gt htightness_pos]

theorem bankTypeSettlementClearsAt_of_bilateral {J : Type*} [Fintype J]
    (P : Primitives S) (X : Allocation S) (t : ℕ) (h : History S t)
    (mass reserves deposits : J → ℝ)
    (paymentSupportByType : J → Finset BankPayment)
    (paymentProbabilityByType paymentShockByType : J → BankPayment → ℝ)
    (tightness : ℝ)
    (H : BilateralOTCActivity
      (bankDeficitSupplyAt P X t h mass reserves deposits paymentSupportByType
        paymentProbabilityByType paymentShockByType)
      (bankSurplusSupplyAt P X t h mass reserves deposits paymentSupportByType
        paymentProbabilityByType paymentShockByType) tightness) :
    BankTypeSettlementClearsAt P X t h mass reserves deposits paymentSupportByType
      paymentProbabilityByType paymentShockByType tightness := by
  unfold BankTypeSettlementClearsAt
  rw [bankTypeSettlementAggregate_eq]
  rw [otcMatchingFractions_clear _ _ _ _ H]
  ring

noncomputable def bankOTCInterbankAt (P : Primitives S) (X : Allocation S)
    (t : ℕ) (h : History S t) (tightness reserves deposits : ℝ)
    (ω : BankPayment) : ℝ :=
  let surplus := bankSettlementSurplus reserves (P.reserveRequirementPath t h)
    (X.depositRate t h / X.reserveRate t h) deposits (P.paymentShock ω)
  if surplus < 0 then
    -otcDeficitMatchFraction P.matchingIntensity tightness * surplus
  else
    -otcSurplusMatchFraction P.matchingIntensity tightness * surplus

noncomputable def bankFacilityBorrowingAt (P : Primitives S) (X : Allocation S)
    (t : ℕ) (h : History S t) (tightness reserves deposits : ℝ)
    (ω : BankPayment) : ℝ :=
  let surplus := bankSettlementSurplus reserves (P.reserveRequirementPath t h)
    (X.depositRate t h / X.reserveRate t h) deposits (P.paymentShock ω)
  if surplus < 0 then
    -(1 - otcDeficitMatchFraction P.matchingIntensity tightness) * surplus
  else 0

theorem bankFacilityBorrowingAt_nonneg
    (P : Primitives S) (X : Allocation S) (t : ℕ) (h : History S t)
    (tightness reserves deposits : ℝ) (htightness : 0 < tightness)
    (ω : BankPayment) :
    0 ≤ bankFacilityBorrowingAt P X t h tightness reserves deposits ω := by
  unfold bankFacilityBorrowingAt
  let surplus := bankSettlementSurplus reserves (P.reserveRequirementPath t h)
    (X.depositRate t h / X.reserveRate t h) deposits (P.paymentShock ω)
  change 0 ≤ if surplus < 0 then
    -(1 - otcDeficitMatchFraction P.matchingIntensity tightness) * surplus else 0
  by_cases hs : surplus < 0
  · rw [if_pos hs]
    have hfraction := otcDeficitMatchFraction_mem P.matchingIntensity tightness
      P.matching_intensity_pos htightness
    have hcoefficient : 0 ≤ 1 - otcDeficitMatchFraction P.matchingIntensity tightness :=
      sub_nonneg.mpr hfraction.2
    have hproduct := mul_nonneg hcoefficient (neg_nonneg.mpr hs.le)
    nlinarith
  · rw [if_neg hs]

noncomputable def bankPostSettlementReservesAt
    (P : Primitives S) (X : Allocation S)
    (t : ℕ) (h : History S t) (tightness reserves deposits : ℝ)
    (ω : BankPayment) : ℝ :=
  reserves + (X.depositRate t h / X.reserveRate t h) *
      P.paymentShock ω * deposits +
    bankOTCInterbankAt P X t h tightness reserves deposits ω +
    bankFacilityBorrowingAt P X t h tightness reserves deposits ω

theorem bankOTCInterbankAt_scale
    (P : Primitives S) (X : Allocation S) (t : ℕ) (h : History S t)
    (tightness reserves deposits c : ℝ) (hc : 0 < c) (ω : BankPayment) :
    bankOTCInterbankAt P X t h tightness (c * reserves) (c * deposits) ω =
      c * bankOTCInterbankAt P X t h tightness reserves deposits ω := by
  unfold bankOTCInterbankAt
  have hscale : bankSettlementSurplus (c * reserves) (P.reserveRequirementPath t h)
      (X.depositRate t h / X.reserveRate t h) (c * deposits) (P.paymentShock ω) =
      c * bankSettlementSurplus reserves (P.reserveRequirementPath t h)
        (X.depositRate t h / X.reserveRate t h) deposits (P.paymentShock ω) := by
    unfold bankSettlementSurplus
    ring
  rw [hscale]
  by_cases hs : bankSettlementSurplus reserves (P.reserveRequirementPath t h)
      (X.depositRate t h / X.reserveRate t h) deposits (P.paymentShock ω) < 0
  · have hcs := mul_neg_of_pos_of_neg hc hs
    simp [hs, hcs]
    ring
  · have hs0 : 0 ≤ bankSettlementSurplus reserves (P.reserveRequirementPath t h)
        (X.depositRate t h / X.reserveRate t h) deposits (P.paymentShock ω) :=
      le_of_not_gt hs
    have hcs0 := mul_nonneg hc.le hs0
    simp [hs, not_lt.mpr hcs0]
    ring

theorem bankFacilityBorrowingAt_scale
    (P : Primitives S) (X : Allocation S) (t : ℕ) (h : History S t)
    (tightness reserves deposits c : ℝ) (hc : 0 < c) (ω : BankPayment) :
    bankFacilityBorrowingAt P X t h tightness (c * reserves) (c * deposits) ω =
      c * bankFacilityBorrowingAt P X t h tightness reserves deposits ω := by
  unfold bankFacilityBorrowingAt
  have hscale : bankSettlementSurplus (c * reserves) (P.reserveRequirementPath t h)
      (X.depositRate t h / X.reserveRate t h) (c * deposits) (P.paymentShock ω) =
      c * bankSettlementSurplus reserves (P.reserveRequirementPath t h)
        (X.depositRate t h / X.reserveRate t h) deposits (P.paymentShock ω) := by
    unfold bankSettlementSurplus
    ring
  rw [hscale]
  by_cases hs : bankSettlementSurplus reserves (P.reserveRequirementPath t h)
      (X.depositRate t h / X.reserveRate t h) deposits (P.paymentShock ω) < 0
  · have hcs := mul_neg_of_pos_of_neg hc hs
    simp [hs, hcs]
    ring
  · have hs0 : 0 ≤ bankSettlementSurplus reserves (P.reserveRequirementPath t h)
        (X.depositRate t h / X.reserveRate t h) deposits (P.paymentShock ω) :=
      le_of_not_gt hs
    have hcs0 := mul_nonneg hc.le hs0
    simp [hs, not_lt.mpr hcs0]

theorem bankPostSettlementReservesAt_scale
    (P : Primitives S) (X : Allocation S) (t : ℕ) (h : History S t)
    (tightness reserves deposits c : ℝ) (hc : 0 < c) (ω : BankPayment) :
    bankPostSettlementReservesAt P X t h tightness (c * reserves)
        (c * deposits) ω =
      c * bankPostSettlementReservesAt P X t h tightness reserves deposits ω := by
  unfold bankPostSettlementReservesAt
  rw [bankOTCInterbankAt_scale P X t h tightness reserves deposits c hc ω,
    bankFacilityBorrowingAt_scale P X t h tightness reserves deposits c hc ω]
  ring

/-- Detailed post-payment return using the source's matching-generated OTC
and facility positions.  Unlike candidate-only consistency certificates, this
is defined for every local portfolio deviation. -/
noncomputable def bankDetailedPortfolioReturnAt
    (P : Primitives S) (X : Allocation S)
    (t : ℕ) (h : History S t) (tightness loans reserves deposits : ℝ)
    (ω : BankPayment) : ℝ :=
  X.loanRate t h * loans + X.reserveRate t h *
      bankPostSettlementReservesAt P X t h tightness reserves deposits ω -
    X.depositRate t h * deposits * (1 + P.paymentShock ω) -
    X.interbankRate t h *
      bankOTCInterbankAt P X t h tightness reserves deposits ω -
    X.facilityRate t h *
      bankFacilityBorrowingAt P X t h tightness reserves deposits ω

/-- The two source liquidity slopes at one aggregate history. -/
noncomputable def bankOTCDeficitSlopeAt (P : Primitives S) (X : Allocation S)
    (t : ℕ) (h : History S t) (tightness : ℝ) : ℝ :=
  otcDeficitSlope (X.reserveRate t h) (X.interbankRate t h)
    (X.facilityRate t h) P.matchingIntensity tightness

noncomputable def bankOTCSurplusSlopeAt (P : Primitives S) (X : Allocation S)
    (t : ℕ) (h : History S t) (tightness : ℝ) : ℝ :=
  otcSurplusSlope (X.reserveRate t h) (X.interbankRate t h)
    P.matchingIntensity tightness

/-- Substitution of settlement flows reduces the detailed return to the
piecewise `χ` return for every portfolio, not only at the candidate. -/
theorem bankDetailedPortfolioReturn_eq_reduced
    (P : Primitives S) (X : Allocation S)
    (t : ℕ) (h : History S t) (tightness loans reserves deposits : ℝ)
    (ω : BankPayment) (hreserve : X.reserveRate t h ≠ 0) :
    bankDetailedPortfolioReturnAt P X t h tightness loans reserves deposits ω =
      bankReducedPortfolioReturn P X t h
        (bankOTCDeficitSlopeAt P X t h tightness)
        (bankOTCSurplusSlopeAt P X t h tightness)
        loans reserves deposits ω := by
  by_cases hs : bankSettlementSurplus reserves (P.reserveRequirementPath t h)
      (X.depositRate t h / X.reserveRate t h) deposits (P.paymentShock ω) < 0
  · simp only [bankDetailedPortfolioReturnAt, bankPostSettlementReservesAt,
      bankOTCInterbankAt, bankFacilityBorrowingAt, hs, if_pos,
      bankReducedPortfolioReturn, bankReducedPortfolioReturnWithShock,
      otcLiquidityPayoff, bankOTCDeficitSlopeAt,
      bankOTCSurplusSlopeAt, otcDeficitSlope, otcSurplusSlope]
    field_simp [hreserve]
    ring
  · simp only [bankDetailedPortfolioReturnAt, bankPostSettlementReservesAt,
      bankOTCInterbankAt, bankFacilityBorrowingAt, hs,
      bankReducedPortfolioReturn, bankReducedPortfolioReturnWithShock,
      otcLiquidityPayoff, bankOTCDeficitSlopeAt,
      bankOTCSurplusSlopeAt, otcDeficitSlope, otcSurplusSlope]
    simp only [if_false]
    field_simp [hreserve]
    ring

theorem bankDetailedPortfolioReturnAt_scale
    (P : Primitives S) (X : Allocation S)
    (t : ℕ) (h : History S t) (tightness loans reserves deposits c : ℝ)
    (hc : 0 < c) (ω : BankPayment) :
    bankDetailedPortfolioReturnAt P X t h tightness
        (c * loans) (c * reserves) (c * deposits) ω =
      c * bankDetailedPortfolioReturnAt P X t h tightness
        loans reserves deposits ω := by
  unfold bankDetailedPortfolioReturnAt
  rw [bankPostSettlementReservesAt_scale P X t h tightness reserves deposits c hc ω,
    bankOTCInterbankAt_scale P X t h tightness reserves deposits c hc ω,
    bankFacilityBorrowingAt_scale P X t h tightness reserves deposits c hc ω]
  ring

/-- Literal one-history bank admissibility for an explicitly supported payment
law: nonnegative controls, balance, both caps, and robust real solvency. -/
def BankStaticPortfolioFeasibleOnAt (P : Primitives S) (X : Allocation S)
    (t : ℕ) (h : History S t) (deficitSlope surplusSlope retainedEquity
      loans reserves deposits depositCap loanCap : ℝ)
      (support : Finset BankPayment)
      (shock : BankPayment → ℝ) : Prop :=
  0 ≤ loans ∧ 0 ≤ reserves ∧ 0 ≤ deposits ∧
  loans + reserves = deposits + retainedEquity ∧
  deposits ≤ depositCap * retainedEquity ∧
  loans ≤ loanCap * retainedEquity ∧
  ∀ ω ∈ support, ∀ s,
    0 < P.tree.transition (currentState h) s →
      0 ≤ bankReducedPortfolioReturnWithShock P X t h
        deficitSlope surplusSlope loans reserves deposits (shock ω) /
          X.inflation (t + 1) (childHistory h s)

def BankStaticPortfolioFeasibleAt (P : Primitives S) (X : Allocation S)
    (t : ℕ) (h : History S t) (deficitSlope surplusSlope retainedEquity
      loans reserves deposits : ℝ) : Prop :=
  BankStaticPortfolioFeasibleOnAt P X t h deficitSlope surplusSlope retainedEquity
    loans reserves deposits P.bankDepositCap P.bankLoanCap
      P.paymentSupport P.paymentShock

/-- Expected reduced payoff of the fixed-price static portfolio problem. -/
noncomputable def bankStaticPortfolioPayoffAt (P : Primitives S) (X : Allocation S)
    (t : ℕ) (h : History S t) (deficitSlope surplusSlope loans reserves deposits : ℝ) :
    ℝ :=
  finiteSupportExpectation P.paymentSupport P.paymentProbability (fun ω ↦
    bankReducedPortfolioReturn P X t h deficitSlope surplusSlope
      loans reserves deposits ω)

/-- The no-fixed-cost, degree-one restriction used by the source.  Both the
admissible set and the reduced payoff scale with equity and the portfolio. -/
def BankStaticProblemHomogeneousAt (P : Primitives S) (X : Allocation S)
    (t : ℕ) (h : History S t) (deficitSlope surplusSlope : ℝ) : Prop :=
  ∀ c retainedEquity loans reserves deposits,
    0 < c →
    (BankStaticPortfolioFeasibleAt P X t h deficitSlope surplusSlope retainedEquity
        loans reserves deposits ↔
      BankStaticPortfolioFeasibleAt P X t h deficitSlope surplusSlope
        (c * retainedEquity) (c * loans) (c * reserves) (c * deposits)) ∧
    bankStaticPortfolioPayoffAt P X t h deficitSlope surplusSlope
        (c * loans) (c * reserves) (c * deposits) =
      c * bankStaticPortfolioPayoffAt P X t h deficitSlope surplusSlope
        loans reserves deposits

theorem bankSettlementSurplus_scale
    (c reserves reserveRequirement depositReserveRatio deposits shock : ℝ) :
    bankSettlementSurplus (c * reserves) reserveRequirement depositReserveRatio
        (c * deposits) shock =
      c * bankSettlementSurplus reserves reserveRequirement depositReserveRatio
        deposits shock := by
  unfold bankSettlementSurplus
  ring

theorem otcLiquidityPayoff_scale
    (deficitSlope surplusSlope surplus c : ℝ) (hc : 0 < c) :
    otcLiquidityPayoff deficitSlope surplusSlope (c * surplus) =
      c * otcLiquidityPayoff deficitSlope surplusSlope surplus := by
  by_cases hs : surplus < 0
  · have hcs : c * surplus < 0 := mul_neg_of_pos_of_neg hc hs
    simp [otcLiquidityPayoff, hs, hcs]
    ring
  · have hs0 : 0 ≤ surplus := le_of_not_gt hs
    have hcs0 : 0 ≤ c * surplus := mul_nonneg hc.le hs0
    simp [otcLiquidityPayoff, hs, not_lt.mpr hcs0]
    ring

theorem bankReducedPortfolioReturn_scale
    (P : Primitives S) (X : Allocation S) (t : ℕ) (h : History S t)
    (deficitSlope surplusSlope retained loans reserves deposits c : ℝ)
    (hc : 0 < c) (ω : BankPayment) :
    bankReducedPortfolioReturn P X t h deficitSlope surplusSlope
        (c * loans) (c * reserves) (c * deposits) ω =
      c * bankReducedPortfolioReturn P X t h deficitSlope surplusSlope
        loans reserves deposits ω := by
  unfold bankReducedPortfolioReturn bankReducedPortfolioReturnWithShock
  rw [bankSettlementSurplus_scale,
    otcLiquidityPayoff_scale deficitSlope surplusSlope _ c hc]
  ring

theorem bankStaticPortfolioFeasible_scale
    (P : Primitives S) (X : Allocation S) (t : ℕ) (h : History S t)
    (deficitSlope surplusSlope retainedEquity loans reserves deposits c : ℝ)
    (hc : 0 < c)
    (hfeasible : BankStaticPortfolioFeasibleAt P X t h deficitSlope surplusSlope
      retainedEquity loans reserves deposits) :
    BankStaticPortfolioFeasibleAt P X t h deficitSlope surplusSlope
      (c * retainedEquity) (c * loans) (c * reserves) (c * deposits) := by
  rcases hfeasible with ⟨hl, hr, hd, hbalance, hdcap, hlcap, hsolvent⟩
  refine ⟨mul_nonneg hc.le hl, mul_nonneg hc.le hr, mul_nonneg hc.le hd, ?_, ?_, ?_, ?_⟩
  · nlinarith
  · nlinarith
  · nlinarith
  · intro ω hω s htransition
    change 0 ≤ bankReducedPortfolioReturn P X t h deficitSlope surplusSlope
      (c * loans) (c * reserves) (c * deposits) ω /
        X.inflation (t + 1) (childHistory h s)
    rw [bankReducedPortfolioReturn_scale P X t h deficitSlope surplusSlope
      retainedEquity loans reserves deposits c hc ω]
    calc
      0 ≤ c * (bankReducedPortfolioReturn P X t h deficitSlope surplusSlope
          loans reserves deposits ω /
            X.inflation (t + 1) (childHistory h s)) :=
        mul_nonneg hc.le (hsolvent ω hω s htransition)
      _ = c * bankReducedPortfolioReturn P X t h deficitSlope surplusSlope
            loans reserves deposits ω /
            X.inflation (t + 1) (childHistory h s) := by ring

theorem bankStaticPortfolioPayoff_scale
    (P : Primitives S) (X : Allocation S) (t : ℕ) (h : History S t)
    (deficitSlope surplusSlope loans reserves deposits c : ℝ)
    (hc : 0 < c) :
    bankStaticPortfolioPayoffAt P X t h deficitSlope surplusSlope
        (c * loans) (c * reserves) (c * deposits) =
      c * bankStaticPortfolioPayoffAt P X t h deficitSlope surplusSlope
        loans reserves deposits := by
  unfold bankStaticPortfolioPayoffAt finiteSupportExpectation
  simp_rw [bankReducedPortfolioReturn_scale P X t h deficitSlope surplusSlope
    0 loans reserves deposits c hc]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ω _
  ring

/-- Degree-one homogeneity is a theorem of the linear balance, caps, real
solvency inequalities and piecewise-linear payoff; it is not an input
certificate to Proposition 3.8. -/
theorem bankStaticProblemHomogeneousAt
    (P : Primitives S) (X : Allocation S) (t : ℕ) (h : History S t)
    (deficitSlope surplusSlope : ℝ) :
    BankStaticProblemHomogeneousAt P X t h deficitSlope surplusSlope := by
  intro c retainedEquity loans reserves deposits hc
  constructor
  · constructor
    · exact bankStaticPortfolioFeasible_scale P X t h deficitSlope surplusSlope
        retainedEquity loans reserves deposits c hc
    · intro hscaled
      have hinv : 0 < (1 / c : ℝ) := one_div_pos.mpr hc
      have hback := bankStaticPortfolioFeasible_scale P X t h
        deficitSlope surplusSlope (c * retainedEquity) (c * loans)
        (c * reserves) (c * deposits) (1 / c) hinv hscaled
      convert hback using 1 <;> field_simp [hc.ne']
  · exact bankStaticPortfolioPayoff_scale P X t h deficitSlope surplusSlope
      loans reserves deposits c hc

/-- Candidate settlement positions are generated by the source matching rule,
not merely chosen to make the reduced return agree ex post. -/
def BankCandidateOTCFlowsAt (P : Primitives S) (X : Allocation S)
    (p : BankPlan S) (t : ℕ) (h : History S t) (tightness : ℝ) : Prop :=
  ∀ ω,
    ω ∈ P.paymentSupport →
    p.interbank ω t h = bankOTCInterbankAt P X t h tightness
      (p.reservesPre t h) (p.deposits t h) ω ∧
    p.facility ω t h = bankFacilityBorrowingAt P X t h tightness
      (p.reservesPre t h) (p.deposits t h) ω ∧
    p.reservesPost ω t h = bankPostSettlementReservesAt P X t h tightness
      (p.reservesPre t h) (p.deposits t h) ω

/-- The source-consistent common normalized plan for a mass-one ex-ante bank
type.  Payment-history heterogeneity is not erased: it is generated later by
`bankContinuationPolicyFromPlan` from this common portfolio and the literal
payment-specific settlement returns. -/
noncomputable def fullRetentionCommonBankPlan
    (P : Primitives S) (X : Allocation S) : BankPlan S where
  equity := X.bankEquity
  dividend := fun _ _ ↦ 0
  retainedEquity := X.bankEquity
  loans := X.bankLoans
  reservesPre := X.reservesPrePayment
  deposits := X.bankDeposits
  reservesPost := fun ω t h ↦ bankPostSettlementReservesAt P X t h
    (X.bankTightness t h) (X.reservesPrePayment t h) (X.bankDeposits t h) ω
  interbank := fun ω t h ↦ bankOTCInterbankAt P X t h
    (X.bankTightness t h) (X.reservesPrePayment t h) (X.bankDeposits t h) ω
  facility := fun ω t h ↦ bankFacilityBorrowingAt P X t h
    (X.bankTightness t h) (X.reservesPrePayment t h) (X.bankDeposits t h) ω

/-- Every payment-specific flow of the common plan is generated by the
literal matching/facility mechanism, definitionally rather than through an
assumed feasibility record. -/
theorem fullRetentionCommonBankPlan_candidateFlows
    (P : Primitives S) (X : Allocation S) (t : ℕ) (h : History S t) :
    BankCandidateOTCFlowsAt P X (fullRetentionCommonBankPlan P X) t h
      (X.bankTightness t h) := by
  intro ω _hω
  exact ⟨rfl, rfl, rfl⟩

/-- Matching-generated settlement controls identify the literal `BankPlan`
return with the detailed return used by a supported-history continuation.
This identity does not require division by the reserve rate. -/
theorem bankGrossReturn_eq_detailed_of_candidateFlows
    (P : Primitives S) (X : Allocation S) (p : BankPlan S)
    (t : ℕ) (h : History S t) (tightness : ℝ)
    (hflows : BankCandidateOTCFlowsAt P X p t h tightness)
    (ω : BankPayment) (hω : ω ∈ P.paymentSupport) :
    bankGrossReturn P X p ω t h =
      bankDetailedPortfolioReturnAt P X t h tightness
        (p.loans t h) (p.reservesPre t h) (p.deposits t h) ω := by
  rcases hflows ω hω with ⟨hinterbank, hfacility, hpost⟩
  unfold bankGrossReturn bankDetailedPortfolioReturnAt
  rw [hinterbank, hfacility, hpost]

/-- The concrete full-retention common plan has the literal detailed return
on every primitive-supported payment.  This is an identification equality,
not a feasibility or optimality assertion. -/
theorem fullRetentionCommonBankPlan_grossReturn_eq_detailed
    (P : Primitives S) (X : Allocation S)
    (t : ℕ) (h : History S t) (ω : BankPayment)
    (hω : ω ∈ P.paymentSupport) :
    bankGrossReturn P X (fullRetentionCommonBankPlan P X) ω t h =
      bankDetailedPortfolioReturnAt P X t h (X.bankTightness t h)
        (X.bankLoans t h) (X.reservesPrePayment t h)
        (X.bankDeposits t h) ω := by
  simpa [fullRetentionCommonBankPlan] using
    bankGrossReturn_eq_detailed_of_candidateFlows P X
      (fullRetentionCommonBankPlan P X) t h (X.bankTightness t h)
      (fullRetentionCommonBankPlan_candidateFlows P X t h) ω hω

/-- Once the candidate's OTC and facility controls are generated by the
matching rule, its literal balance-sheet return equals the reduced kink payoff
used by the finite bank rows. -/
theorem bankGrossReturn_eq_reduced_of_candidateFlows
    (P : Primitives S) (X : Allocation S) (p : BankPlan S)
    (t : ℕ) (h : History S t) (tightness : ℝ)
    (hflows : BankCandidateOTCFlowsAt P X p t h tightness)
    (hreserve : X.reserveRate t h ≠ 0)
    (ω : BankPayment) (hω : ω ∈ P.paymentSupport) :
    bankGrossReturn P X p ω t h =
      bankReducedPortfolioReturn P X t h
        (bankOTCDeficitSlopeAt P X t h tightness)
        (bankOTCSurplusSlopeAt P X t h tightness)
        (p.loans t h) (p.reservesPre t h) (p.deposits t h) ω := by
  rcases hflows ω hω with ⟨hinterbank, hfacility, hpost⟩
  calc
    bankGrossReturn P X p ω t h =
        bankDetailedPortfolioReturnAt P X t h tightness
          (p.loans t h) (p.reservesPre t h) (p.deposits t h) ω := by
            unfold bankGrossReturn bankDetailedPortfolioReturnAt
            rw [hinterbank, hfacility, hpost]
    _ = _ := bankDetailedPortfolioReturn_eq_reduced P X t h tightness
      (p.loans t h) (p.reservesPre t h) (p.deposits t h) ω hreserve

/-- The household SDF in source lines 277--280 and 699--704.  It depends on
the aggregate successor `s` and, by construction, not on the idiosyncratic
payment realization `ω`. -/
noncomputable def bankStochasticDiscountAt
    (P : Primitives S) (X : Allocation S) (t : ℕ) (h : History S t)
    (s : S) : ℝ :=
  P.workerDiscount *
    (X.workerConsumption (t + 1) (childHistory h s) ^ (-P.workerRiskAversion)) /
      (X.workerConsumption t h ^ (-P.workerRiskAversion))

/-- With the illustrative branch's unit CRRA coefficient, the literal SDF is
the current/child consumption ratio.  The two nonzero premises are analytic
domain facts; no reduced-path existence or positivity is hidden here. -/
theorem bankStochasticDiscountAt_eq_ratio_of_riskAversion_one
    (P : Primitives S) (X : Allocation S) (t : ℕ) (h : History S t) (s : S)
    (hrisk : P.workerRiskAversion = 1)
    (hcurrent : X.workerConsumption t h ≠ 0)
    (hchild : X.workerConsumption (t + 1) (childHistory h s) ≠ 0) :
    bankStochasticDiscountAt P X t h s =
      P.workerDiscount * X.workerConsumption t h /
        X.workerConsumption (t + 1) (childHistory h s) := by
  unfold bankStochasticDiscountAt
  rw [hrisk]
  simp only [Real.rpow_neg_one]
  field_simp

/-- Real pre-exit equity generated by one local portfolio and one pair of
idiosyncratic-payment/aggregate-successor states. -/
noncomputable def bankRealPortfolioReturnAt
    (P : Primitives S) (X : Allocation S) (t : ℕ) (h : History S t)
    (deficitSlope surplusSlope loans reserves deposits : ℝ)
    (ω : BankPayment) (s : S) : ℝ :=
  bankReducedPortfolioReturn P X t h deficitSlope surplusSlope
      loans reserves deposits ω /
    X.inflation (t + 1) (childHistory h s)

theorem bankRealPortfolioReturnAt_scale
    (P : Primitives S) (X : Allocation S) (t : ℕ) (h : History S t)
    (deficitSlope surplusSlope loans reserves deposits c : ℝ)
    (hc : 0 < c) (ω : BankPayment) (s : S) :
    bankRealPortfolioReturnAt P X t h deficitSlope surplusSlope
        (c * loans) (c * reserves) (c * deposits) ω s =
      c * bankRealPortfolioReturnAt P X t h deficitSlope surplusSlope
        loans reserves deposits ω s := by
  unfold bankRealPortfolioReturnAt
  rw [bankReducedPortfolioReturn_scale P X t h deficitSlope surplusSlope
    0 loans reserves deposits c hc ω]
  ring

/-- The literal Bellman continuation payoff
`E[Λ ((1-η_B)V_B(e_ret,S') + η_B e_ret)]`. -/
noncomputable def bankBellmanContinuationAt
    (P : Primitives S) (X : Allocation S) (t : ℕ) (h : History S t)
    (deficitSlope surplusSlope loans reserves deposits : ℝ)
    (bankValueNext : ℝ → History S (t + 1) → ℝ) : ℝ :=
  ∑ ω ∈ P.paymentSupport, P.paymentProbability ω * ∑ s,
    P.tree.transition (currentState h) s * bankStochasticDiscountAt P X t h s *
      ((1 - P.bankExit) * bankValueNext
          (bankRealPortfolioReturnAt P X t h deficitSlope surplusSlope
            loans reserves deposits ω s) (childHistory h s) +
        P.bankExit * bankRealPortfolioReturnAt P X t h deficitSlope surplusSlope
          loans reserves deposits ω s)

/-- The positive continuation weight in source lines 797--798.  Homogeneity
makes this scalar common across `ω`, while it still integrates over aggregate
successors and their SDF/inflation. -/
noncomputable def bankBellmanContinuationWeightAt
    (P : Primitives S) (X : Allocation S) (t : ℕ) (h : History S t)
    (bankValueNext : ℝ → History S (t + 1) → ℝ) : ℝ :=
  ∑ s, P.tree.transition (currentState h) s * bankStochasticDiscountAt P X t h s *
    ((1 - P.bankExit) * bankValueNext 1 (childHistory h s) + P.bankExit) /
      X.inflation (t + 1) (childHistory h s)

/-- Literal fixed-price local optimality against every feasible static triple.
This is the authority used by Proposition 3.8; no opaque lift to a global plan
is hidden in the definition. -/
def BankStaticPortfolioOptimalAt (P : Primitives S) (X : Allocation S)
    (t : ℕ) (h : History S t) (deficitSlope surplusSlope retainedEquity
      candidateLoans candidateReserves candidateDeposits : ℝ) : Prop :=
  ∀ loans reserves deposits,
    BankStaticPortfolioFeasibleAt P X t h deficitSlope surplusSlope
        retainedEquity loans reserves deposits →
    bankStaticPortfolioPayoffAt P X t h deficitSlope surplusSlope
        loans reserves deposits ≤
      bankStaticPortfolioPayoffAt P X t h deficitSlope surplusSlope
        candidateLoans candidateReserves candidateDeposits

/-- A bank value is allowed to depend on the full aggregate history, rather
than only its current Markov label. -/
abbrev BankValueProcess (S : Type*) :=
  (t : ℕ) → ℝ → History S t → ℝ

/-- A source continuation policy records an individual bank's equity and
portfolio controls after every future aggregate-state and supported-payment
history.  Unlike `BankPlan`, the carrier retains the idiosyncratic payment
history that generates the bank's next equity. -/
structure BankContinuationPolicy (S Ω : Type*) where
  equity : (n : ℕ) → (Fin n → S) → (Fin n → Ω) → ℝ
  dividend : (n : ℕ) → (Fin n → S) → (Fin n → Ω) → ℝ
  retainedEquity : (n : ℕ) → (Fin n → S) → (Fin n → Ω) → ℝ
  loans : (n : ℕ) → (Fin n → S) → (Fin n → Ω) → ℝ
  reserves : (n : ℕ) → (Fin n → S) → (Fin n → Ω) → ℝ
  deposits : (n : ℕ) → (Fin n → S) → (Fin n → Ω) → ℝ

/-- Attach a newest-first future path to the already observed history. -/
def continuationHistory {t n : ℕ} (h : History S t) (future : Fin n → S) :
    History S (t + n) :=
  fun j ↦ Fin.append future h (Fin.cast (by omega) j)

/-- Extend a newest-first future path by one aggregate state. -/
def childFutureHistory {n : ℕ} (future : Fin n → S) (s : S) :
    Fin (n + 1) → S :=
  Fin.cases s future

/-- Extend the supported idiosyncratic-payment path by one realization. -/
def childPaymentHistory {Ω : Type*} {n : ℕ} (payments : Fin n → Ω) (ω : Ω) :
    Fin (n + 1) → Ω :=
  Fin.cases ω payments

/-- Individual pre-exit equity generated by repeatedly applying the literal
post-settlement return to a common normalized `BankPlan`.  The aggregate plan
supplies only portfolio ratios: the level at every node is the bank's own
payment-history-dependent equity.  Exit and entry are not inserted here;
survival is represented separately in the continuation objective. -/
noncomputable def bankContinuationEquityFromPlan
    (P : Primitives S) (X : Allocation S) (p : BankPlan S)
    (t : ℕ) (h : History S t) :
    (n : ℕ) → (Fin n → S) → (Fin n → P.paymentSupport) → ℝ
  | 0, _, _ => p.equity t h
  | n + 1, future, payments =>
      let previousFuture : Fin n → S := fun j ↦ future j.succ
      let previousPayments : Fin n → P.paymentSupport := fun j ↦ payments j.succ
      let H := continuationHistory h previousFuture
      let equity := bankContinuationEquityFromPlan P X p t h n
        previousFuture previousPayments
      let scale := equity / p.equity (t + n) H
      bankDetailedPortfolioReturnAt P X (t + n) H
          (X.bankTightness (t + n) H)
          (scale * p.loans (t + n) H)
          (scale * p.reservesPre (t + n) H)
          (scale * p.deposits (t + n) H) (payments 0) /
        X.inflation (t + n + 1) (childHistory H (future 0))

/-- The individual-to-common-plan scale at a future aggregate/payment
history.  Positivity is deliberately not built into this definition; it is a
separate feasibility consequence of robust portfolio returns. -/
noncomputable def bankContinuationPlanScaleAt
    (P : Primitives S) (X : Allocation S) (p : BankPlan S)
    (t : ℕ) (h : History S t) (n : ℕ)
    (future : Fin n → S) (payments : Fin n → P.paymentSupport) : ℝ :=
  bankContinuationEquityFromPlan P X p t h n future payments /
    p.equity (t + n) (continuationHistory h future)

/-- Construct the full supported-history continuation carrier generated by a
common normalized bank plan.  All six fields are explicit.  This definition
does not assert that the input plan is feasible, optimal, or supplied by the
externally certified reduced aggregate path. -/
noncomputable def bankContinuationPolicyFromPlan
    (P : Primitives S) (X : Allocation S) (p : BankPlan S)
    (t : ℕ) (h : History S t) : BankContinuationPolicy S P.paymentSupport where
  equity := bankContinuationEquityFromPlan P X p t h
  dividend n future payments :=
    bankContinuationPlanScaleAt P X p t h n future payments *
      p.dividend (t + n) (continuationHistory h future)
  retainedEquity n future payments :=
    bankContinuationPlanScaleAt P X p t h n future payments *
      p.retainedEquity (t + n) (continuationHistory h future)
  loans n future payments :=
    bankContinuationPlanScaleAt P X p t h n future payments *
      p.loans (t + n) (continuationHistory h future)
  reserves n future payments :=
    bankContinuationPlanScaleAt P X p t h n future payments *
      p.reservesPre (t + n) (continuationHistory h future)
  deposits n future payments :=
    bankContinuationPlanScaleAt P X p t h n future payments *
      p.deposits (t + n) (continuationHistory h future)

@[simp] theorem bankContinuationEquityFromPlan_zero
    (P : Primitives S) (X : Allocation S) (p : BankPlan S)
    (t : ℕ) (h : History S t) (future : Fin 0 → S)
    (payments : Fin 0 → P.paymentSupport) :
    bankContinuationEquityFromPlan P X p t h 0 future payments =
      p.equity t h := rfl

/-- The constructed policy's child equity is definitionally the literal
payment-specific real portfolio return.  Thus an aggregate equity path is not
being reused at every payment history. -/
theorem bankContinuationPolicyFromPlan_equity_child
    (P : Primitives S) (X : Allocation S) (p : BankPlan S)
    (t : ℕ) (h : History S t) (n : ℕ)
    (future : Fin n → S) (payments : Fin n → P.paymentSupport)
    (s : S) (ω : P.paymentSupport) :
    (bankContinuationPolicyFromPlan P X p t h).equity (n + 1)
        (childFutureHistory future s) (childPaymentHistory payments ω) =
      bankDetailedPortfolioReturnAt P X (t + n)
          (continuationHistory h future)
          (X.bankTightness (t + n) (continuationHistory h future))
          ((bankContinuationPolicyFromPlan P X p t h).loans
            n future payments)
          ((bankContinuationPolicyFromPlan P X p t h).reserves
            n future payments)
          ((bankContinuationPolicyFromPlan P X p t h).deposits
            n future payments) ω /
        X.inflation (t + n + 1)
          (childHistory (continuationHistory h future) s) := by
  rfl

/-- For the constructed full-retention plan, every payment-history child's
equity is the positive plan scale times the same literal detailed aggregate
portfolio return.  This is an all-history identity, not a growth bound. -/
theorem fullRetentionContinuation_equity_child
    (P : Primitives S) (X : Allocation S)
    (t : ℕ) (h : History S t) (n : ℕ)
    (future : Fin n → S) (payments : Fin n → P.paymentSupport)
    (s : S) (omega : P.paymentSupport)
    (hscale : 0 < bankContinuationPlanScaleAt P X
      (fullRetentionCommonBankPlan P X) t h n future payments) :
    (bankContinuationPolicyFromPlan P X (fullRetentionCommonBankPlan P X) t h).equity
        (n + 1) (childFutureHistory future s)
          (childPaymentHistory payments omega) =
      bankContinuationPlanScaleAt P X (fullRetentionCommonBankPlan P X)
          t h n future payments *
        bankDetailedPortfolioReturnAt P X (t + n) (continuationHistory h future)
          (X.bankTightness (t + n) (continuationHistory h future))
          (X.bankLoans (t + n) (continuationHistory h future))
          (X.reservesPrePayment (t + n) (continuationHistory h future))
          (X.bankDeposits (t + n) (continuationHistory h future)) omega /
        X.inflation (t + n + 1)
          (childHistory (continuationHistory h future) s) := by
  rw [bankContinuationPolicyFromPlan_equity_child]
  change bankDetailedPortfolioReturnAt P X (t + n) (continuationHistory h future)
      (X.bankTightness (t + n) (continuationHistory h future))
      (bankContinuationPlanScaleAt P X (fullRetentionCommonBankPlan P X)
        t h n future payments * X.bankLoans (t + n) (continuationHistory h future))
      (bankContinuationPlanScaleAt P X (fullRetentionCommonBankPlan P X)
        t h n future payments * X.reservesPrePayment (t + n)
          (continuationHistory h future))
      (bankContinuationPlanScaleAt P X (fullRetentionCommonBankPlan P X)
        t h n future payments * X.bankDeposits (t + n)
          (continuationHistory h future))
      omega / X.inflation (t + n + 1)
        (childHistory (continuationHistory h future) s) = _
  rw [bankDetailedPortfolioReturnAt_scale P X (t + n)
    (continuationHistory h future)
    (X.bankTightness (t + n) (continuationHistory h future))
    (X.bankLoans (t + n) (continuationHistory h future))
    (X.reservesPrePayment (t + n) (continuationHistory h future))
    (X.bankDeposits (t + n) (continuationHistory h future))
    (bankContinuationPlanScaleAt P X (fullRetentionCommonBankPlan P X)
      t h n future payments) hscale omega]

/-- Pointwise scaling of the entire continuation policy.  Prices, payment
laws and matching tightness remain fixed, exactly as in the source scaling
argument. -/
def scaleBankContinuationPolicy (c : ℝ) (p : BankContinuationPolicy S Ω) :
    BankContinuationPolicy S Ω where
  equity n future payments := c * p.equity n future payments
  dividend n future payments := c * p.dividend n future payments
  retainedEquity n future payments := c * p.retainedEquity n future payments
  loans n future payments := c * p.loans n future payments
  reserves n future payments := c * p.reserves n future payments
  deposits n future payments := c * p.deposits n future payments

/-- Every aggregate transition used by a future path has positive conditional
probability.  This is a support predicate, not a numerical lower bound. -/
def FuturePathSupported (T : FiniteMarkovTree S) (start : S) :
    (n : ℕ) → (Fin n → S) → Prop
  | 0, _ => True
  | n + 1, future =>
      let previous : Fin n → S := fun j ↦ future j.succ
      let previousState := if hn : n = 0 then start
        else previous ⟨0, Nat.pos_of_ne_zero hn⟩
      FuturePathSupported T start n previous ∧
        0 < T.transition previousState (future 0)

theorem scaleBankContinuationPolicy_inv
    (c : ℝ) (hc : c ≠ 0) (p : BankContinuationPolicy S Ω) :
    scaleBankContinuationPolicy c (scaleBankContinuationPolicy (1 / c) p) = p := by
  rcases p with ⟨equity, dividend, retainedEquity, loans, reserves, deposits⟩
  simp only [scaleBankContinuationPolicy]
  congr 1 <;> funext n future payments <;> field_simp

/-- Literal dynamic feasibility from one observed aggregate history and one
initial equity.  The policy is indexed by the bank's supported payment path;
its next equity is the real post-settlement return, so dynamic homogeneity is
not inferred from an aggregate bank balance sheet. -/
def BankContinuationFeasibleAt
    (P : Primitives S) (X : Allocation S) (t : ℕ) (h : History S t)
    (initialEquity : ℝ)
    (p : BankContinuationPolicy S P.paymentSupport) : Prop :=
  p.equity 0 (fun j ↦ Fin.elim0 j) (fun j ↦ Fin.elim0 j) = initialEquity ∧
  ∀ n future payments, FuturePathSupported P.tree (currentState h) n future →
    let H := continuationHistory h future
    0 ≤ p.equity n future payments ∧
    0 ≤ p.dividend n future payments ∧
    0 ≤ p.retainedEquity n future payments ∧
    0 ≤ p.loans n future payments ∧
    0 ≤ p.reserves n future payments ∧
    0 ≤ p.deposits n future payments ∧
    (p.equity n future payments = 0 →
      p.dividend n future payments = 0 ∧
      p.retainedEquity n future payments = 0 ∧
      p.loans n future payments = 0 ∧
      p.reserves n future payments = 0 ∧
      p.deposits n future payments = 0) ∧
    (0 < p.equity n future payments →
      0 < p.retainedEquity n future payments) ∧
    p.retainedEquity n future payments =
      p.equity n future payments - p.dividend n future payments ∧
    p.loans n future payments + p.reserves n future payments =
      p.deposits n future payments + p.retainedEquity n future payments ∧
    p.deposits n future payments ≤
      P.bankDepositCap * p.retainedEquity n future payments ∧
    p.loans n future payments ≤
      P.bankLoanCap * p.retainedEquity n future payments ∧
    0 < X.reserveRate (t + n) H ∧
    ∀ (ω : P.paymentSupport),
      0 ≤ bankFacilityBorrowingAt P X (t + n) H (X.bankTightness (t + n) H)
        (p.reserves n future payments) (p.deposits n future payments) ω ∧
      (P.reserveRequirementPath (t + n) H) * p.deposits n future payments *
          (1 + P.paymentShock ω) ≤
        bankPostSettlementReservesAt P X (t + n) H (X.bankTightness (t + n) H)
          (p.reserves n future payments) (p.deposits n future payments) ω ∧
      ∀ s, 0 < P.tree.transition (currentState H) s →
        p.equity (n + 1) (childFutureHistory future s)
            (childPaymentHistory payments ω) =
          bankDetailedPortfolioReturnAt P X (t + n) H
            (X.bankTightness (t + n) H)
            (p.loans n future payments) (p.reserves n future payments)
            (p.deposits n future payments) ω /
              X.inflation (t + n + 1) (childHistory H s)

theorem bankContinuationFeasibleAt_scale
    (P : Primitives S) (X : Allocation S) (t : ℕ) (h : History S t)
    (equity c : ℝ) (p : BankContinuationPolicy S P.paymentSupport)
    (hc : 0 < c)
    (hp : BankContinuationFeasibleAt P X t h equity p) :
    BankContinuationFeasibleAt P X t h (c * equity)
      (scaleBankContinuationPolicy c p) := by
  rcases hp with ⟨hinitial, hp⟩
  constructor
  · simp only [scaleBankContinuationPolicy]
    rw [hinitial]
  · intro n future payments hfuture
    rcases hp n future payments hfuture with
      ⟨hequity, hdividend, hretained, hloans, hreserves, hdeposits,
        hzeroBoundary, hretainedPos, hretention, hbalance, hdepositCap,
        hloanCap, hreserveRate, hsettlement⟩
    dsimp only [scaleBankContinuationPolicy]
    refine ⟨mul_nonneg hc.le hequity, mul_nonneg hc.le hdividend,
      mul_nonneg hc.le hretained, mul_nonneg hc.le hloans,
      mul_nonneg hc.le hreserves, mul_nonneg hc.le hdeposits,
      ?_, ?_, ?_, ?_, ?_, ?_, hreserveRate, ?_⟩
    · intro hscaledZero
      have horiginalZero : p.equity n future payments = 0 := by
        nlinarith
      rcases hzeroBoundary horiginalZero with
        ⟨hdividendZero, hretainedZero, hloansZero, hreservesZero, hdepositsZero⟩
      simp [hdividendZero, hretainedZero, hloansZero, hreservesZero, hdepositsZero]
    · intro hscaledPos
      have horiginalPos : 0 < p.equity n future payments := by
        nlinarith
      exact mul_pos hc (hretainedPos horiginalPos)
    · rw [hretention]
      ring
    · nlinarith
    · nlinarith
    · nlinarith
    · intro ω
      rcases hsettlement ω with ⟨hfacility, hreservesPost, htransition⟩
      refine ⟨?_, ?_, ?_⟩
      · rw [bankFacilityBorrowingAt_scale P X (t + n)
          (continuationHistory h future)
          (X.bankTightness (t + n) (continuationHistory h future))
          (p.reserves n future payments) (p.deposits n future payments) c hc ω]
        exact mul_nonneg hc.le hfacility
      · rw [bankPostSettlementReservesAt_scale P X (t + n)
          (continuationHistory h future)
          (X.bankTightness (t + n) (continuationHistory h future))
          (p.reserves n future payments) (p.deposits n future payments) c hc ω]
        nlinarith
      · intro s hs
        rw [htransition s hs,
          bankDetailedPortfolioReturnAt_scale P X (t + n)
            (continuationHistory h future)
            (X.bankTightness (t + n) (continuationHistory h future))
            (p.loans n future payments) (p.reserves n future payments)
            (p.deposits n future payments) c hc ω]
        ring

def oldestExtendedFuture {S : Type*} {n : ℕ}
    (future : Fin n → S) (s : S) : Fin (n + 1) → S :=
  Fin.snoc future s

theorem tail_oldestExtendedFuture {S : Type*} {n : ℕ}
    (future : Fin (n + 1) → S) (s : S) :
    (fun j ↦ oldestExtendedFuture future s j.succ) =
      oldestExtendedFuture (fun j ↦ future j.succ) s := by
  funext j
  cases j using Fin.lastCases with
  | last => simp [oldestExtendedFuture]
  | cast i => simp [oldestExtendedFuture, ← Fin.castSucc_succ]

theorem continuationHistory_oldestExtendedFuture
    {S : Type*} {t n : ℕ} (h : History S t) (future : Fin n → S) (s : S) :
    continuationHistory h (oldestExtendedFuture future s) =
      fun j ↦ continuationHistory (childHistory h s) future
        (Fin.cast (by omega) j) := by
  funext j
  simp only [continuationHistory, oldestExtendedFuture]
  rw [Fin.append_left_snoc]
  rfl

theorem adaptedProcess_continuationHistory_oldestExtendedFuture
    {S : Type*} {t n : ℕ} (Y : AdaptedProcess S)
    (h : History S t) (future : Fin n → S) (s : S) :
    Y (t + (n + 1)) (continuationHistory h (oldestExtendedFuture future s)) =
      Y (t + 1 + n) (continuationHistory (childHistory h s) future) := by
  rw [continuationHistory_oldestExtendedFuture h future s]
  congr 1
  · omega
  · apply (Fin.heq_fun_iff (by omega)).2
    intro i
    rfl

theorem continuationHistory_zero
    {S : Type*} {t : ℕ} (h : History S t) (future : Fin 0 → S) :
    continuationHistory h future = h := by
  have hfuture : future = fun j ↦ Fin.elim0 j := Subsingleton.elim _ _
  subst future
  funext j
  simp [continuationHistory]

/-- The current state of an appended future is the newest future state when
the future is nonempty, and otherwise remains the current observed state. -/
theorem currentState_continuationHistory
    {S : Type*} {t n : ℕ} (h : History S t) (future : Fin n → S) :
    currentState (continuationHistory h future) =
      if hn : n = 0 then currentState h
      else future ⟨0, Nat.pos_of_ne_zero hn⟩ := by
  cases n with
  | zero => simp [continuationHistory_zero, currentState]
  | succ n =>
      simp only [currentState, continuationHistory]
      change Fin.append future h
        (Fin.castAdd (t + 1) (0 : Fin (n + 1))) = future 0
      rw [Fin.append_left]

theorem adaptedProcess_continuationHistory_zero
    {S : Type*} {t : ℕ} (Y : AdaptedProcess S)
    (h : History S t) (future : Fin 0 → S) :
    Y (t + 0) (continuationHistory h future) = Y t h := by
  rw [continuationHistory_zero h future]
  rfl

theorem continuationHistory_snoc
    {S : Type*} {t n : ℕ} (h : History S t) (future : Fin n → S) (s : S) :
    continuationHistory h (Fin.snoc future s) =
      fun j ↦ continuationHistory (childHistory h s) future
        (Fin.cast (by omega) j) :=
  continuationHistory_oldestExtendedFuture h future s

theorem adaptedProcess_continuationHistory_snoc
    {S : Type*} {t n : ℕ} (Y : AdaptedProcess S)
    (h : History S t) (future : Fin n → S) (s : S) :
    Y (t + (n + 1)) (continuationHistory h (Fin.snoc future s)) =
      Y (t + 1 + n) (continuationHistory (childHistory h s) future) :=
  adaptedProcess_continuationHistory_oldestExtendedFuture Y h future s

theorem futurePathSupported_oldestExtendedFuture_of
    {S : Type*} [Fintype S] (T : FiniteMarkovTree S)
    (start s : S) (n : ℕ) (future : Fin n → S)
    (hfirst : 0 < T.transition start s)
    (htail : FuturePathSupported T s n future) :
    FuturePathSupported T start (n + 1) (oldestExtendedFuture future s) := by
  induction n with
  | zero =>
      simpa [FuturePathSupported, oldestExtendedFuture] using hfirst
  | succ n ih =>
      rcases htail with ⟨htail, hnew⟩
      have hprevious := ih (fun j ↦ future j.succ) htail
      refine ⟨?_, ?_⟩
      · convert hprevious using 1
        exact tail_oldestExtendedFuture future s
      · rw [tail_oldestExtendedFuture future s]
        cases n with
        | zero => simpa [oldestExtendedFuture] using hnew
        | succ n => simpa [oldestExtendedFuture] using hnew

theorem futurePathSupported_oldestExtendedFuture_to
    {S : Type*} [Fintype S] (T : FiniteMarkovTree S)
    (start s : S) (n : ℕ) (future : Fin n → S)
    (hcombined : FuturePathSupported T start (n + 1)
      (oldestExtendedFuture future s)) :
    0 < T.transition start s ∧ FuturePathSupported T s n future := by
  induction n with
  | zero =>
      simpa [FuturePathSupported, oldestExtendedFuture] using hcombined
  | succ n ih =>
      rcases hcombined with ⟨hprevious, hnew⟩
      have hprevious' : FuturePathSupported T start (n + 1)
          (oldestExtendedFuture (fun j ↦ future j.succ) s) := by
        convert hprevious using 1
        exact (tail_oldestExtendedFuture future s).symm
      rcases ih (fun j ↦ future j.succ) hprevious' with ⟨hfirst, htail⟩
      refine ⟨hfirst, htail, ?_⟩
      rw [tail_oldestExtendedFuture future s] at hnew
      cases n with
      | zero => simpa [oldestExtendedFuture] using hnew
      | succ n => simpa [oldestExtendedFuture] using hnew

theorem futurePathSupported_oldestExtendedFuture_iff
    {S : Type*} [Fintype S] (T : FiniteMarkovTree S)
    (start s : S) (n : ℕ) (future : Fin n → S) :
    FuturePathSupported T start (n + 1) (oldestExtendedFuture future s) ↔
      0 < T.transition start s ∧ FuturePathSupported T s n future :=
  ⟨futurePathSupported_oldestExtendedFuture_to T start s n future,
    fun H ↦ futurePathSupported_oldestExtendedFuture_of T start s n future H.1 H.2⟩

/-- Appending a conditionally supported future path to a positive-probability
history again gives a positive-probability history.  This connects the
continuation carrier's support predicate to the model-wide admissibility
predicate rather than adding admissibility as a separate certificate field. -/
theorem firmHistoryAdmissible_continuationHistory
    {S : Type*} [Fintype S] [DecidableEq S]
    (P : Primitives S) (t : ℕ) (h : History S t)
    (hh : FirmHistoryAdmissible P t h) :
    ∀ n (future : Fin n → S),
      FuturePathSupported P.tree (currentState h) n future →
      FirmHistoryAdmissible P (t + n) (continuationHistory h future) := by
  intro n
  induction n generalizing t h with
  | zero =>
      intro future _
      simpa [FirmHistoryAdmissible, continuationHistory_zero] using hh
  | succ n ih =>
      intro future hfuture
      have hsupportCombined : FuturePathSupported P.tree (currentState h)
          (n + 1) (oldestExtendedFuture (Fin.init future)
            (future (Fin.last n))) := by
        change FuturePathSupported P.tree (currentState h) (n + 1)
          (Fin.snoc (Fin.init future) (future (Fin.last n)))
        rw [Fin.snoc_init_self]
        exact hfuture
      rcases futurePathSupported_oldestExtendedFuture_to P.tree
          (currentState h) (future (Fin.last n)) n (Fin.init future)
          hsupportCombined with ⟨hfirst, htail⟩
      have hchild : FirmHistoryAdmissible P (t + 1)
          (childHistory h (future (Fin.last n))) := by
        unfold FirmHistoryAdmissible at hh ⊢
        simpa [FiniteMarkovTree.historyWeight, previousHistory, childHistory,
          currentState] using mul_pos hh hfirst
      have htailAdmissible := ih (t := t + 1)
        (h := childHistory h (future (Fin.last n))) hchild (Fin.init future) htail
      unfold FirmHistoryAdmissible at htailAdmissible ⊢
      rw [← Fin.snoc_init_self future]
      change 0 < P.tree.historyWeight (t + (n + 1))
        (continuationHistory h (oldestExtendedFuture (Fin.init future)
          (future (Fin.last n))))
      rw [adaptedProcess_continuationHistory_oldestExtendedFuture
          (fun k H ↦ P.tree.historyWeight k H) h (Fin.init future)
            (future (Fin.last n))]
      exact htailAdmissible

theorem bankPostSettlementReservesAt_ge_requirement
    {S : Type*} [Fintype S] [DecidableEq S]
    (P : Primitives S) (X : Allocation S) (t : ℕ) (h : History S t)
    (tightness reserves deposits : ℝ) (htightness : 0 < tightness)
    (ω : BankPayment) :
    P.reserveRequirementPath t h * deposits * (1 + P.paymentShock ω) ≤
      bankPostSettlementReservesAt P X t h tightness reserves deposits ω := by
  let surplus := bankSettlementSurplus reserves (P.reserveRequirementPath t h)
    (X.depositRate t h / X.reserveRate t h) deposits (P.paymentShock ω)
  have hsurplus : surplus = reserves +
      (X.depositRate t h / X.reserveRate t h) * P.paymentShock ω * deposits -
      P.reserveRequirementPath t h * deposits * (1 + P.paymentShock ω) := by
    dsimp only [surplus]
    unfold bankSettlementSurplus
    ring
  unfold bankPostSettlementReservesAt bankOTCInterbankAt
    bankFacilityBorrowingAt
  change _ ≤ reserves + (X.depositRate t h / X.reserveRate t h) *
      P.paymentShock ω * deposits +
      (if surplus < 0 then
        -otcDeficitMatchFraction P.matchingIntensity tightness * surplus
      else -otcSurplusMatchFraction P.matchingIntensity tightness * surplus) +
      (if surplus < 0 then
        -(1 - otcDeficitMatchFraction P.matchingIntensity tightness) * surplus
      else 0)
  by_cases hs : surplus < 0
  · simp only [if_pos hs]
    rw [hsurplus]
    ring_nf
    exact le_rfl
  · simp only [if_neg hs]
    have hs0 : 0 ≤ surplus := le_of_not_gt hs
    have hfraction := otcSurplusMatchFraction_mem P.matchingIntensity tightness
      P.matching_intensity_pos htightness
    rw [hsurplus]
    nlinarith

/-- A feasible common plan with matching-generated settlement flows generates
nonnegative individual equity on every supported aggregate/payment history.
The proof is an induction through the literal detailed real return; no
aggregate equity path or external continuation certificate is substituted. -/
theorem bankContinuationEquityFromPlan_nonneg_of_feasible
    {S : Type*} [Fintype S] [DecidableEq S]
    (P : Primitives S) (I : InheritedState) (X : Allocation S)
    (p : BankPlan S) (t : ℕ) (h : History S t)
    (hh : FirmHistoryAdmissible P t h)
    (hfeasible : BankFeasible P I X p)
    (hflows : ∀ k H, FirmHistoryAdmissible P k H →
      BankCandidateOTCFlowsAt P X p k H (X.bankTightness k H)) :
    ∀ n (future : Fin n → S) (payments : Fin n → P.paymentSupport),
      FuturePathSupported P.tree (currentState h) n future →
      0 ≤ bankContinuationEquityFromPlan P X p t h n future payments := by
  rcases hfeasible with
    ⟨hpositive, _hretention, _hbalance, _hcaps, _hsettlement, _hinitial,
      hsolvent⟩
  intro n
  induction n with
  | zero =>
      intro future payments _
      simpa using (hpositive t h hh).1.le
  | succ n ih =>
      intro future payments hfuture
      let previousFuture : Fin n → S := fun j ↦ future j.succ
      let previousPayments : Fin n → P.paymentSupport := fun j ↦ payments j.succ
      let H := continuationHistory h previousFuture
      let equity := bankContinuationEquityFromPlan P X p t h n
        previousFuture previousPayments
      let scale := equity / p.equity (t + n) H
      rcases hfuture with ⟨hpreviousSupported, hstep⟩
      have hH : FirmHistoryAdmissible P (t + n) H :=
        firmHistoryAdmissible_continuationHistory P t h hh n previousFuture
          hpreviousSupported
      have hequity : 0 ≤ equity := ih previousFuture previousPayments
        hpreviousSupported
      have hplanEquity : 0 < p.equity (t + n) H := (hpositive _ _ hH).1
      have htransition :
          0 < P.tree.transition (currentState H) (future 0) := by
        rw [currentState_continuationHistory h previousFuture]
        exact hstep
      have hbaseReturn := hsolvent (t + n) H hH (payments 0)
        (payments 0).property (future 0) htransition
      rw [bankGrossReturn_eq_detailed_of_candidateFlows P X p (t + n) H
        (X.bankTightness (t + n) H) (hflows _ _ hH) (payments 0)
        (payments 0).property] at hbaseReturn
      change 0 ≤ bankDetailedPortfolioReturnAt P X (t + n) H
        (X.bankTightness (t + n) H)
        (scale * p.loans (t + n) H)
        (scale * p.reservesPre (t + n) H)
        (scale * p.deposits (t + n) H) (payments 0) /
          X.inflation (t + n + 1) (childHistory H (future 0))
      by_cases hequityZero : equity = 0
      · have hscaleZero : scale = 0 := by simp [scale, hequityZero]
        rw [hscaleZero]
        simp [bankDetailedPortfolioReturnAt, bankPostSettlementReservesAt,
          bankOTCInterbankAt, bankFacilityBorrowingAt, bankSettlementSurplus]
      · have hequityPos : 0 < equity :=
          lt_of_le_of_ne hequity (Ne.symm hequityZero)
        have hscalePos : 0 < scale := div_pos hequityPos hplanEquity
        rw [bankDetailedPortfolioReturnAt_scale P X (t + n) H
          (X.bankTightness (t + n) H) (p.loans (t + n) H)
          (p.reservesPre (t + n) H) (p.deposits (t + n) H) scale
          hscalePos (payments 0)]
        convert mul_nonneg hscalePos.le hbaseReturn using 1
        ring

/-- The explicit supported-history carrier is dynamically feasible whenever
the common plan is literally feasible, its settlement controls are generated
by the source matching rule, and reserve rates and matching tightness are
positive at admissible histories.  These are transparent model predicates;
the theorem does not supply the still-missing branch-specific common plan. -/
theorem bankContinuationPolicyFromPlan_feasible
    {S : Type*} [Fintype S] [DecidableEq S]
    (P : Primitives S) (I : InheritedState) (X : Allocation S)
    (p : BankPlan S) (t : ℕ) (h : History S t)
    (hh : FirmHistoryAdmissible P t h)
    (hfeasible : BankFeasible P I X p)
    (hflows : ∀ k H, FirmHistoryAdmissible P k H →
      BankCandidateOTCFlowsAt P X p k H (X.bankTightness k H))
    (hreserveRate : ∀ k H, FirmHistoryAdmissible P k H →
      0 < X.reserveRate k H)
    (htightness : ∀ k H, FirmHistoryAdmissible P k H →
      0 < X.bankTightness k H) :
    BankContinuationFeasibleAt P X t h (p.equity t h)
      (bankContinuationPolicyFromPlan P X p t h) := by
  have hequityNonneg := bankContinuationEquityFromPlan_nonneg_of_feasible
    P I X p t h hh hfeasible hflows
  rcases hfeasible with
    ⟨hpositive, hretention, hbalance, hcaps, _hsettlement, _hinitial,
      _hsolvent⟩
  unfold BankContinuationFeasibleAt
  constructor
  · rfl
  · intro n future payments hfuture
    let H := continuationHistory h future
    let equity := bankContinuationEquityFromPlan P X p t h n future payments
    let scale := equity / p.equity (t + n) H
    have hH : FirmHistoryAdmissible P (t + n) H :=
      firmHistoryAdmissible_continuationHistory P t h hh n future hfuture
    have hequity : 0 ≤ equity := hequityNonneg n future payments hfuture
    rcases hpositive (t + n) H hH with
      ⟨hplanEquity, hplanDividend, hplanRetained, hplanLoans, hplanReserves,
        hplanDeposits⟩
    have hscale : 0 ≤ scale := div_nonneg hequity hplanEquity.le
    have hscaleEquity : scale * p.equity (t + n) H = equity := by
      dsimp only [scale]
      field_simp [hplanEquity.ne']
    have hretention' := hretention (t + n) H hH
    have hbalance' := hbalance (t + n) H hH
    rcases hcaps (t + n) H hH with ⟨hdepositCap, hloanCap⟩
    change 0 ≤ equity ∧
      0 ≤ scale * p.dividend (t + n) H ∧
      0 ≤ scale * p.retainedEquity (t + n) H ∧
      0 ≤ scale * p.loans (t + n) H ∧
      0 ≤ scale * p.reservesPre (t + n) H ∧
      0 ≤ scale * p.deposits (t + n) H ∧
      (equity = 0 →
        scale * p.dividend (t + n) H = 0 ∧
        scale * p.retainedEquity (t + n) H = 0 ∧
        scale * p.loans (t + n) H = 0 ∧
        scale * p.reservesPre (t + n) H = 0 ∧
        scale * p.deposits (t + n) H = 0) ∧
      (0 < equity → 0 < scale * p.retainedEquity (t + n) H) ∧
      scale * p.retainedEquity (t + n) H =
        equity - scale * p.dividend (t + n) H ∧
      scale * p.loans (t + n) H + scale * p.reservesPre (t + n) H =
        scale * p.deposits (t + n) H +
          scale * p.retainedEquity (t + n) H ∧
      scale * p.deposits (t + n) H ≤
        P.bankDepositCap * (scale * p.retainedEquity (t + n) H) ∧
      scale * p.loans (t + n) H ≤
        P.bankLoanCap * (scale * p.retainedEquity (t + n) H) ∧
      0 < X.reserveRate (t + n) H ∧
      ∀ (ω : P.paymentSupport),
        0 ≤ bankFacilityBorrowingAt P X (t + n) H
          (X.bankTightness (t + n) H)
          (scale * p.reservesPre (t + n) H)
          (scale * p.deposits (t + n) H) ω ∧
        P.reserveRequirementPath (t + n) H *
            (scale * p.deposits (t + n) H) * (1 + P.paymentShock ω) ≤
          bankPostSettlementReservesAt P X (t + n) H
            (X.bankTightness (t + n) H)
            (scale * p.reservesPre (t + n) H)
            (scale * p.deposits (t + n) H) ω ∧
        ∀ s, 0 < P.tree.transition (currentState H) s →
          (bankContinuationPolicyFromPlan P X p t h).equity (n + 1)
              (childFutureHistory future s) (childPaymentHistory payments ω) =
            bankDetailedPortfolioReturnAt P X (t + n) H
              (X.bankTightness (t + n) H)
              (scale * p.loans (t + n) H)
              (scale * p.reservesPre (t + n) H)
              (scale * p.deposits (t + n) H) ω /
                X.inflation (t + n + 1) (childHistory H s)
    refine ⟨hequity, mul_nonneg hscale hplanDividend,
      mul_nonneg hscale hplanRetained.le, mul_nonneg hscale hplanLoans,
      mul_nonneg hscale hplanReserves, mul_nonneg hscale hplanDeposits,
      ?_, ?_, ?_, ?_, ?_, ?_, hreserveRate _ _ hH, ?_⟩
    · intro hequityZero
      have hscaleZero : scale = 0 := by simp [scale, hequityZero]
      simp [hscaleZero]
    · intro hequityPos
      have hscalePos : 0 < scale := div_pos hequityPos hplanEquity
      exact mul_pos hscalePos hplanRetained
    · rw [hretention']
      nlinarith
    · nlinarith
    · nlinarith
    · nlinarith
    · intro ω
      refine ⟨bankFacilityBorrowingAt_nonneg P X (t + n) H
          (X.bankTightness (t + n) H)
          (scale * p.reservesPre (t + n) H)
          (scale * p.deposits (t + n) H) (htightness _ _ hH) ω,
        bankPostSettlementReservesAt_ge_requirement P X (t + n) H
          (X.bankTightness (t + n) H)
          (scale * p.reservesPre (t + n) H)
          (scale * p.deposits (t + n) H) (htightness _ _ hH) ω, ?_⟩
      intro s _hs
      exact bankContinuationPolicyFromPlan_equity_child P X p t h n
        future payments s ω

def tailBankContinuationPolicy {S Ω : Type*}
    (p : BankContinuationPolicy S Ω) (s : S) (ω : Ω) :
    BankContinuationPolicy S Ω where
  equity n future payments :=
    p.equity (n + 1) (oldestExtendedFuture future s)
      (oldestExtendedFuture payments ω)
  dividend n future payments :=
    p.dividend (n + 1) (oldestExtendedFuture future s)
      (oldestExtendedFuture payments ω)
  retainedEquity n future payments :=
    p.retainedEquity (n + 1) (oldestExtendedFuture future s)
      (oldestExtendedFuture payments ω)
  loans n future payments :=
    p.loans (n + 1) (oldestExtendedFuture future s)
      (oldestExtendedFuture payments ω)
  reserves n future payments :=
    p.reserves (n + 1) (oldestExtendedFuture future s)
      (oldestExtendedFuture payments ω)
  deposits n future payments :=
    p.deposits (n + 1) (oldestExtendedFuture future s)
      (oldestExtendedFuture payments ω)

def spliceBankContinuationPolicy {S Ω : Type*}
    (currentEquity currentDividend currentRetained currentLoans currentReserves
      currentDeposits : ℝ)
    (continuation : S → Ω → BankContinuationPolicy S Ω) :
    BankContinuationPolicy S Ω where
  equity
    | 0, _, _ => currentEquity
    | n + 1, future, payments =>
        (continuation (future (Fin.last n)) (payments (Fin.last n))).equity n
          (Fin.init future) (Fin.init payments)
  dividend
    | 0, _, _ => currentDividend
    | n + 1, future, payments =>
        (continuation (future (Fin.last n)) (payments (Fin.last n))).dividend n
          (Fin.init future) (Fin.init payments)
  retainedEquity
    | 0, _, _ => currentRetained
    | n + 1, future, payments =>
        (continuation (future (Fin.last n)) (payments (Fin.last n))).retainedEquity n
          (Fin.init future) (Fin.init payments)
  loans
    | 0, _, _ => currentLoans
    | n + 1, future, payments =>
        (continuation (future (Fin.last n)) (payments (Fin.last n))).loans n
          (Fin.init future) (Fin.init payments)
  reserves
    | 0, _, _ => currentReserves
    | n + 1, future, payments =>
        (continuation (future (Fin.last n)) (payments (Fin.last n))).reserves n
          (Fin.init future) (Fin.init payments)
  deposits
    | 0, _, _ => currentDeposits
    | n + 1, future, payments =>
        (continuation (future (Fin.last n)) (payments (Fin.last n))).deposits n
          (Fin.init future) (Fin.init payments)

theorem tailBankContinuationPolicy_feasible
    {S : Type*} [Fintype S] [DecidableEq S]
    (P : Primitives S) (X : Allocation S) (t : ℕ) (h : History S t)
    (initialEquity : ℝ) (p : BankContinuationPolicy S P.paymentSupport)
    (hp : BankContinuationFeasibleAt P X t h initialEquity p)
    (s : S) (hs : 0 < P.tree.transition (currentState h) s)
    (ω : P.paymentSupport) :
    BankContinuationFeasibleAt P X (t + 1) (childHistory h s)
      (p.equity 1 (fun _ ↦ s) (fun _ ↦ ω))
      (tailBankContinuationPolicy p s ω) := by
  rcases hp with ⟨_, hp⟩
  constructor
  · rfl
  · intro n future payments hfuture
    have hcombined := futurePathSupported_oldestExtendedFuture_of P.tree
      (currentState h) s n future hs hfuture
    have hp' := hp (n + 1) (oldestExtendedFuture future s)
      (oldestExtendedFuture payments ω) hcombined
    dsimp only [tailBankContinuationPolicy]
    rcases hp' with
      ⟨hequity, hdividend, hretained, hloans, hreserves, hdeposits,
        hzeroBoundary, hretainedPos, hretention, hbalance, hdepositCap,
        hloanCap, hreserveRate, hsettlement⟩
    refine ⟨hequity, hdividend, hretained, hloans, hreserves, hdeposits,
      hzeroBoundary, hretainedPos, hretention, hbalance, hdepositCap,
      hloanCap, ?_, ?_⟩
    · rw [adaptedProcess_continuationHistory_oldestExtendedFuture
          X.reserveRate h future s] at hreserveRate
      exact hreserveRate
    · intro ω'
      rcases hsettlement ω' with ⟨hfacility, hpost, htransition⟩
      refine ⟨?_, ?_, ?_⟩
      · rw [adaptedProcess_continuationHistory_oldestExtendedFuture
          (fun k H ↦ bankFacilityBorrowingAt P X k H
            (X.bankTightness k H)
            (p.reserves (n + 1) (oldestExtendedFuture future s)
              (oldestExtendedFuture payments ω))
            (p.deposits (n + 1) (oldestExtendedFuture future s)
              (oldestExtendedFuture payments ω)) ω') h future s] at hfacility
        exact hfacility
      · rw [adaptedProcess_continuationHistory_oldestExtendedFuture
          (fun k H ↦ P.reserveRequirementPath k H *
            p.deposits (n + 1) (oldestExtendedFuture future s)
              (oldestExtendedFuture payments ω) *
            (1 + P.paymentShock ω')) h future s,
          adaptedProcess_continuationHistory_oldestExtendedFuture
          (fun k H ↦ bankPostSettlementReservesAt P X k H
            (X.bankTightness k H)
            (p.reserves (n + 1) (oldestExtendedFuture future s)
              (oldestExtendedFuture payments ω))
            (p.deposits (n + 1) (oldestExtendedFuture future s)
              (oldestExtendedFuture payments ω)) ω') h future s] at hpost
        exact hpost
      · intro s' hs'
        have hsOriginal : 0 < P.tree.transition
            (currentState (continuationHistory h
              (oldestExtendedFuture future s))) s' := by
          rw [adaptedProcess_continuationHistory_oldestExtendedFuture
            (fun _ H ↦ P.tree.transition (currentState H) s') h future s]
          exact hs'
        have ht := htransition s' hsOriginal
        have hfutureEq : childFutureHistory (oldestExtendedFuture future s) s' =
            oldestExtendedFuture (childFutureHistory future s') s := by
          exact Fin.cons_snoc_eq_snoc_cons s' future s
        have hpaymentEq : childPaymentHistory (oldestExtendedFuture payments ω) ω' =
            oldestExtendedFuture (childPaymentHistory payments ω') ω := by
          exact Fin.cons_snoc_eq_snoc_cons ω' payments ω
        rw [hfutureEq, hpaymentEq] at ht
        rw [adaptedProcess_continuationHistory_oldestExtendedFuture
          (fun k H ↦ bankDetailedPortfolioReturnAt P X k H
              (X.bankTightness k H)
              (p.loans (n + 1) (oldestExtendedFuture future s)
                (oldestExtendedFuture payments ω))
              (p.reserves (n + 1) (oldestExtendedFuture future s)
                (oldestExtendedFuture payments ω))
              (p.deposits (n + 1) (oldestExtendedFuture future s)
                (oldestExtendedFuture payments ω)) ω' /
            X.inflation (k + 1) (childHistory H s')) h future s] at ht
        exact ht

theorem spliceBankContinuationPolicy_feasible
    {S : Type*} [Fintype S] [DecidableEq S]
    (P : Primitives S) (X : Allocation S) (t : ℕ) (h : History S t)
    (currentEquity currentDividend currentRetained currentLoans currentReserves
      currentDeposits : ℝ)
    (continuation : S → P.paymentSupport →
      BankContinuationPolicy S P.paymentSupport)
    (hequity : 0 < currentEquity) (hdividend : 0 ≤ currentDividend)
    (hretained : 0 < currentRetained)
    (hretention : currentRetained = currentEquity - currentDividend)
    (hreserveRate : 0 < X.reserveRate t h)
    (htightness : 0 < X.bankTightness t h)
    (hstatic : BankStaticPortfolioFeasibleAt P X t h
      (bankOTCDeficitSlopeAt P X t h (X.bankTightness t h))
      (bankOTCSurplusSlopeAt P X t h (X.bankTightness t h))
      currentRetained currentLoans currentReserves currentDeposits)
    (hcontinuation : ∀ s,
      0 < P.tree.transition (currentState h) s → ∀ ω : P.paymentSupport,
      BankContinuationFeasibleAt P X (t + 1) (childHistory h s)
        (bankDetailedPortfolioReturnAt P X t h (X.bankTightness t h)
            currentLoans currentReserves currentDeposits ω /
          X.inflation (t + 1) (childHistory h s))
        (continuation s ω)) :
    BankContinuationFeasibleAt P X t h currentEquity
      (spliceBankContinuationPolicy currentEquity currentDividend currentRetained
        currentLoans currentReserves currentDeposits continuation) := by
  constructor
  · rfl
  · intro n future payments hfuture
    cases n with
    | zero =>
        have hfuture0 : future = fun j ↦ Fin.elim0 j := Subsingleton.elim _ _
        have hpayments0 : payments = fun j ↦ Fin.elim0 j := Subsingleton.elim _ _
        subst future
        subst payments
        rcases hstatic with
          ⟨hloans, hreserves, hdeposits, hbalance, hdepositCap, hloanCap,
            hsolvent⟩
        dsimp only [spliceBankContinuationPolicy]
        refine ⟨hequity.le, hdividend, hretained.le, hloans, hreserves,
          hdeposits, ?_, fun _ ↦ hretained, hretention, hbalance,
          hdepositCap, hloanCap, ?_, ?_⟩
        · intro hzero
          exact (hequity.ne' hzero).elim
        · rw [adaptedProcess_continuationHistory_zero X.reserveRate h]
          exact hreserveRate
        · intro ω
          rw [adaptedProcess_continuationHistory_zero
            (fun k H ↦ bankFacilityBorrowingAt P X k H (X.bankTightness k H)
              currentReserves currentDeposits ω) h,
            adaptedProcess_continuationHistory_zero
            (fun k H ↦ P.reserveRequirementPath k H * currentDeposits *
              (1 + P.paymentShock ω)) h,
            adaptedProcess_continuationHistory_zero
            (fun k H ↦ bankPostSettlementReservesAt P X k H
              (X.bankTightness k H) currentReserves currentDeposits ω) h]
          refine ⟨bankFacilityBorrowingAt_nonneg P X t h
              (X.bankTightness t h) currentReserves currentDeposits htightness ω,
            bankPostSettlementReservesAt_ge_requirement P X t h
              (X.bankTightness t h) currentReserves currentDeposits htightness ω,
            ?_⟩
          intro s hs
          have hq := hcontinuation s hs ω
          have hinitial := hq.1
          have hinitFuture : Fin.init
              (childFutureHistory (fun j : Fin 0 ↦ Fin.elim0 j) s) =
              (fun j : Fin 0 ↦ Fin.elim0 j) := Subsingleton.elim _ _
          have hinitPayments : Fin.init
              (childPaymentHistory (fun j : Fin 0 ↦ Fin.elim0 j) ω) =
              (fun j : Fin 0 ↦ Fin.elim0 j) := Subsingleton.elim _ _
          rw [continuationHistory_zero h, hinitFuture, hinitPayments]
          simpa [spliceBankContinuationPolicy, childFutureHistory,
            childPaymentHistory] using hinitial
    | succ n =>
        have hsupportCombined : FuturePathSupported P.tree (currentState h)
            (n + 1) (oldestExtendedFuture (Fin.init future)
              (future (Fin.last n))) := by
          change FuturePathSupported P.tree (currentState h) (n + 1)
            (Fin.snoc (Fin.init future) (future (Fin.last n)))
          rw [Fin.snoc_init_self]
          exact hfuture
        rcases futurePathSupported_oldestExtendedFuture_to P.tree
          (currentState h) (future (Fin.last n)) n (Fin.init future)
            hsupportCombined with
          ⟨hs0, htail⟩
        have hq := hcontinuation (future (Fin.last n)) hs0
          (payments (Fin.last n))
        have hq' := hq.2 n (Fin.init future) (Fin.init payments) htail
        dsimp only [spliceBankContinuationPolicy]
        rw [← Fin.snoc_init_self future, ← Fin.snoc_init_self payments]
        simp only [Fin.init_snoc, Fin.snoc_last]
        rcases hq' with
          ⟨hequity', hdividend', hretained', hloans', hreserves', hdeposits',
            hzeroBoundary', hretainedPos', hretention', hbalance', hdepositCap',
            hloanCap', hreserveRate', hsettlement'⟩
        refine ⟨hequity', hdividend', hretained', hloans', hreserves', hdeposits',
          hzeroBoundary', hretainedPos', hretention', hbalance', hdepositCap',
          hloanCap', ?_, ?_⟩
        · rw [adaptedProcess_continuationHistory_snoc
            X.reserveRate h (Fin.init future) (future (Fin.last n))]
          exact hreserveRate'
        · intro ω
          rcases hsettlement' ω with ⟨hfacility', hpost', htransition'⟩
          refine ⟨?_, ?_, ?_⟩
          · rw [adaptedProcess_continuationHistory_snoc
              (fun k H ↦ bankFacilityBorrowingAt P X k H
                (X.bankTightness k H)
                ((continuation (future (Fin.last n))
                  (payments (Fin.last n))).reserves n
                    (Fin.init future) (Fin.init payments))
                ((continuation (future (Fin.last n))
                  (payments (Fin.last n))).deposits n
                    (Fin.init future) (Fin.init payments)) ω)
              h (Fin.init future) (future (Fin.last n))]
            exact hfacility'
          · rw [adaptedProcess_continuationHistory_snoc
              (fun k H ↦ P.reserveRequirementPath k H *
                ((continuation (future (Fin.last n))
                  (payments (Fin.last n))).deposits n
                    (Fin.init future) (Fin.init payments)) *
                (1 + P.paymentShock ω))
              h (Fin.init future) (future (Fin.last n)),
              adaptedProcess_continuationHistory_snoc
              (fun k H ↦ bankPostSettlementReservesAt P X k H
                (X.bankTightness k H)
                ((continuation (future (Fin.last n))
                  (payments (Fin.last n))).reserves n
                    (Fin.init future) (Fin.init payments))
                ((continuation (future (Fin.last n))
                  (payments (Fin.last n))).deposits n
                    (Fin.init future) (Fin.init payments)) ω)
              h (Fin.init future) (future (Fin.last n))]
            exact hpost'
          · intro s hs
            have hs' : 0 < P.tree.transition
                (currentState (continuationHistory
                  (childHistory h (future (Fin.last n))) (Fin.init future))) s := by
              rw [← adaptedProcess_continuationHistory_oldestExtendedFuture
                (fun _ H ↦ P.tree.transition (currentState H) s)
                h (Fin.init future) (future (Fin.last n))]
              exact hs
            have ht := htransition' s hs'
            have hfutureEq : childFutureHistory
                (Fin.snoc (Fin.init future) (future (Fin.last n))) s =
                Fin.snoc (childFutureHistory (Fin.init future) s)
                  (future (Fin.last n)) := by
              exact Fin.cons_snoc_eq_snoc_cons s (Fin.init future)
                (future (Fin.last n))
            have hpaymentEq : childPaymentHistory
                (Fin.snoc (Fin.init payments) (payments (Fin.last n))) ω =
                Fin.snoc (childPaymentHistory (Fin.init payments) ω)
                  (payments (Fin.last n)) := by
              exact Fin.cons_snoc_eq_snoc_cons ω (Fin.init payments)
                (payments (Fin.last n))
            have hlastFuture : Fin.snoc (α := fun _ ↦ S)
                (childFutureHistory (Fin.init future) s) (future (Fin.last n))
                  (Fin.last (n + 1)) = future (Fin.last n) :=
              by simp
            have hlastPayment : Fin.snoc (α := fun _ ↦ P.paymentSupport)
                (childPaymentHistory (Fin.init payments) ω) (payments (Fin.last n))
                  (Fin.last (n + 1)) = payments (Fin.last n) :=
              by simp
            have hinitFuture : Fin.init (Fin.snoc (α := fun _ ↦ S)
                (childFutureHistory (Fin.init future) s) (future (Fin.last n))) =
                childFutureHistory (Fin.init future) s :=
              by simp
            have hinitPayment : Fin.init (Fin.snoc (α := fun _ ↦ P.paymentSupport)
                (childPaymentHistory (Fin.init payments) ω) (payments (Fin.last n))) =
                childPaymentHistory (Fin.init payments) ω :=
              by simp
            rw [hfutureEq, hpaymentEq, hlastFuture, hlastPayment,
              hinitFuture, hinitPayment]
            rw [adaptedProcess_continuationHistory_snoc
              (fun k H ↦ bankDetailedPortfolioReturnAt P X k H
                  (X.bankTightness k H)
                  ((continuation (future (Fin.last n))
                    (payments (Fin.last n))).loans n
                      (Fin.init future) (Fin.init payments))
                  ((continuation (future (Fin.last n))
                    (payments (Fin.last n))).reserves n
                      (Fin.init future) (Fin.init payments))
                  ((continuation (future (Fin.last n))
                    (payments (Fin.last n))).deposits n
                      (Fin.init future) (Fin.init payments)) ω /
                X.inflation (k + 1) (childHistory H s))
              h (Fin.init future) (future (Fin.last n))]
            exact ht



/-- Conditional Markov probability of a newest-first future aggregate path.
It is defined recursively, so the continuation problem remains meaningful at
any current history without division by an off-path history probability. -/
noncomputable def continuationTransitionWeight (T : FiniteMarkovTree S)
    (start : S) : (n : ℕ) → (Fin n → S) → ℝ
  | 0, _ => 1
  | n + 1, future =>
      let previous : Fin n → S := fun j ↦ future j.succ
      let previousState := if hn : n = 0 then start else previous ⟨0, Nat.pos_of_ne_zero hn⟩
      continuationTransitionWeight T start n previous *
        T.transition previousState (future 0)

/-- Probability of a supported idiosyncratic-payment path. -/
noncomputable def continuationPaymentWeight (P : Primitives S) {n : ℕ}
    (payments : Fin n → P.paymentSupport) : ℝ :=
  ∏ j, P.paymentProbability (payments j)

/-- The household's cumulative real SDF from the observed history to a future
aggregate path.  This is the telescoped product of the one-step SDFs in the
bank Bellman equation. -/
noncomputable def bankCumulativeSDFAt
    (P : Primitives S) (X : Allocation S) (t : ℕ) (h : History S t)
    {n : ℕ} (future : Fin n → S) : ℝ :=
  P.workerDiscount ^ n *
    (X.workerConsumption (t + n) (continuationHistory h future) ^
      (-P.workerRiskAversion)) /
    (X.workerConsumption t h ^ (-P.workerRiskAversion))

theorem continuationTransitionWeight_snoc
    {S : Type*} [Fintype S] (T : FiniteMarkovTree S)
    (start s : S) (n : ℕ) (future : Fin n → S) :
    continuationTransitionWeight T start (n + 1) (Fin.snoc future s) =
      T.transition start s * continuationTransitionWeight T s n future := by
  induction n generalizing start s with
  | zero =>
      rw [continuationTransitionWeight.eq_2,
        continuationTransitionWeight.eq_1,
        continuationTransitionWeight.eq_1]
      simp [Fin.snoc_zero]
  | succ n ih =>
      rw [continuationTransitionWeight.eq_2]
      have htail : (fun j : Fin (n + 1) ↦
          Fin.snoc (α := fun _ ↦ S) future s j.succ) =
          Fin.snoc (α := fun _ ↦ S) (fun j : Fin n ↦ future j.succ) s := by
        exact tail_oldestExtendedFuture future s
      rw [htail, ih, continuationTransitionWeight.eq_2]
      simp only [Nat.succ_ne_zero, ↓reduceDIte]
      by_cases hn : n = 0
      · subst n
        simp [Fin.snoc_zero]
        ring
      · simp only [hn, ↓reduceDIte]
        have hnpos : 0 < n := Nat.pos_of_ne_zero hn
        simp [Fin.snoc, hnpos]
        have hz : Fin.castLT (0 : Fin (n + 1)) hnpos = (⟨0, hnpos⟩ : Fin n) :=
          Fin.ext rfl
        rw [hz]
        have hprev : future (⟨0, hnpos⟩ : Fin n).succ =
            future (⟨1, by omega⟩ : Fin (n + 1)) := by
          congr 1
        rw [hprev]
        rw [← mul_assoc]
        congr 3

theorem continuationPaymentWeight_snoc
    {S : Type*} [Fintype S] (P : Primitives S) {n : ℕ}
    (payments : Fin n → P.paymentSupport) (ω : P.paymentSupport) :
    continuationPaymentWeight P (Fin.snoc payments ω) =
      P.paymentProbability ω * continuationPaymentWeight P payments := by
  unfold continuationPaymentWeight
  rw [Fin.prod_univ_castSucc]
  simp only [Fin.snoc_castSucc, Fin.snoc_last]
  ring

theorem bankCumulativeSDFAt_snoc
    {S : Type*} [Fintype S] (P : Primitives S) (X : Allocation S)
    (t : ℕ) (h : History S t) {n : ℕ} (future : Fin n → S) (s : S)
    (hchild : 0 < X.workerConsumption (t + 1) (childHistory h s)) :
    bankCumulativeSDFAt P X t h (Fin.snoc future s) =
      bankStochasticDiscountAt P X t h s *
        bankCumulativeSDFAt P X (t + 1) (childHistory h s) future := by
  unfold bankCumulativeSDFAt bankStochasticDiscountAt
  rw [adaptedProcess_continuationHistory_snoc X.workerConsumption h future s]
  rw [pow_succ']
  have hchildPow : X.workerConsumption (t + 1) (childHistory h s) ^
      (-P.workerRiskAversion) ≠ 0 :=
    (Real.rpow_pos_of_pos hchild (-P.workerRiskAversion)).ne'
  field_simp [hchildPow]

theorem sum_pi_snoc {A : Type*} [Fintype A] {n : ℕ}
    (f : (Fin (n + 1) → A) → ℝ) :
    (∑ q, f q) = ∑ a, ∑ q : Fin n → A, f (Fin.snoc q a) := by
  rw [← (Fin.snocEquiv (fun _ : Fin (n + 1) ↦ A)).sum_comp f,
    Fintype.sum_prod_type]
  rfl

/-- Appending a newest state to a continuation path gives the corresponding
child of the continued history. -/
theorem continuationHistory_childFutureHistory
    {S : Type*} {t n : ℕ} (h : History S t)
    (future : Fin n → S) (s : S) :
    continuationHistory h (childFutureHistory future s) =
      childHistory (continuationHistory h future) s := by
  change continuationHistory h (Fin.cons s future) = _
  unfold continuationHistory childHistory
  rw [Fin.append_cons]
  funext j
  refine Fin.cases ?_ (fun i ↦ ?_) j
  · simp
  · simp [Function.comp_apply]

/-- Chronological extension of the cumulative SDF by its newest one-step SDF.
This complements `bankCumulativeSDFAt_snoc`, which peels off the oldest step. -/
theorem bankCumulativeSDFAt_childFutureHistory
    {S : Type*} [Fintype S] [DecidableEq S]
    (P : Primitives S) (X : Allocation S) (t : ℕ) (h : History S t)
    {n : ℕ} (future : Fin n → S) (s : S)
    (hcurrent : 0 < X.workerConsumption (t + n)
      (continuationHistory h future)) :
    bankCumulativeSDFAt P X t h (childFutureHistory future s) =
      bankCumulativeSDFAt P X t h future *
        bankStochasticDiscountAt P X (t + n)
          (continuationHistory h future) s := by
  unfold bankCumulativeSDFAt bankStochasticDiscountAt
  rw [continuationHistory_childFutureHistory]
  rw [pow_succ']
  have hcurrentPow : X.workerConsumption (t + n)
      (continuationHistory h future) ^ (-P.workerRiskAversion) ≠ 0 :=
    (Real.rpow_pos_of_pos hcurrent (-P.workerRiskAversion)).ne'
  field_simp [hcurrentPow]
  congr 4

/-- Exact one-step SDF times individual-equity identity for the constructed
full-retention continuation.  The detailed return remains the literal
matching-generated payment return; this theorem asserts no numerical bound. -/
theorem fullRetentionContinuation_joint_child
    {S : Type*} [Fintype S] [DecidableEq S]
    (P : Primitives S) (X : Allocation S)
    (t : ℕ) (h : History S t) (n : ℕ)
    (future : Fin n → S) (payments : Fin n → P.paymentSupport)
    (s : S) (omega : P.paymentSupport)
    (hrisk : P.workerRiskAversion = 1)
    (hcurrentConsumption :
      X.workerConsumption (t + n) (continuationHistory h future) ≠ 0)
    (hchildConsumption : X.workerConsumption (t + n + 1)
      (childHistory (continuationHistory h future) s) ≠ 0)
    (hindividual : 0 <
      (bankContinuationPolicyFromPlan P X
        (fullRetentionCommonBankPlan P X) t h).equity n future payments)
    (haggregate : 0 <
      X.bankEquity (t + n) (continuationHistory h future)) :
    bankStochasticDiscountAt P X (t + n)
        (continuationHistory h future) s *
      (bankContinuationPolicyFromPlan P X
        (fullRetentionCommonBankPlan P X) t h).equity (n + 1)
          (childFutureHistory future s) (childPaymentHistory payments omega) =
      (bankContinuationPolicyFromPlan P X
        (fullRetentionCommonBankPlan P X) t h).equity n future payments *
        ((P.workerDiscount *
            X.workerConsumption (t + n) (continuationHistory h future) /
              X.workerConsumption (t + n + 1)
                (childHistory (continuationHistory h future) s)) *
          (bankDetailedPortfolioReturnAt P X (t + n)
              (continuationHistory h future)
              (X.bankTightness (t + n) (continuationHistory h future))
              (X.bankLoans (t + n) (continuationHistory h future))
              (X.reservesPrePayment (t + n) (continuationHistory h future))
              (X.bankDeposits (t + n) (continuationHistory h future)) omega /
            X.bankEquity (t + n) (continuationHistory h future) /
            X.inflation (t + n + 1)
              (childHistory (continuationHistory h future) s))) := by
  let q := bankContinuationPolicyFromPlan P X
    (fullRetentionCommonBankPlan P X) t h
  have hscale : 0 < bankContinuationPlanScaleAt P X
      (fullRetentionCommonBankPlan P X) t h n future payments := by
    unfold bankContinuationPlanScaleAt
    change 0 < q.equity n future payments /
      X.bankEquity (t + n) (continuationHistory h future)
    exact div_pos hindividual haggregate
  rw [bankStochasticDiscountAt_eq_ratio_of_riskAversion_one
    P X (t + n) (continuationHistory h future) s hrisk
      hcurrentConsumption hchildConsumption]
  rw [fullRetentionContinuation_equity_child P X t h n future payments
    s omega hscale]
  unfold bankContinuationPlanScaleAt
  change _ = q.equity n future payments * _
  dsimp [q, fullRetentionCommonBankPlan]
  simp only [bankContinuationPolicyFromPlan]
  ring

/-- All-date chronological recurrence for cumulative SDF times individual
equity.  A separate arithmetic certificate may bound the displayed one-step
factor, but no such bound or exact-sequence existence is asserted here. -/
theorem fullRetentionContinuation_cumulative_joint_child
    {S : Type*} [Fintype S] [DecidableEq S]
    (P : Primitives S) (X : Allocation S)
    (t : ℕ) (h : History S t) (n : ℕ)
    (future : Fin n → S) (payments : Fin n → P.paymentSupport)
    (s : S) (omega : P.paymentSupport)
    (hrisk : P.workerRiskAversion = 1)
    (hcurrentConsumptionPos : 0 <
      X.workerConsumption (t + n) (continuationHistory h future))
    (hchildConsumption : X.workerConsumption (t + n + 1)
      (childHistory (continuationHistory h future) s) ≠ 0)
    (hindividual : 0 <
      (bankContinuationPolicyFromPlan P X
        (fullRetentionCommonBankPlan P X) t h).equity n future payments)
    (haggregate : 0 <
      X.bankEquity (t + n) (continuationHistory h future)) :
    bankCumulativeSDFAt P X t h (childFutureHistory future s) *
      (bankContinuationPolicyFromPlan P X
        (fullRetentionCommonBankPlan P X) t h).equity (n + 1)
          (childFutureHistory future s) (childPaymentHistory payments omega) =
      (bankCumulativeSDFAt P X t h future *
        (bankContinuationPolicyFromPlan P X
          (fullRetentionCommonBankPlan P X) t h).equity n future payments) *
        ((P.workerDiscount *
            X.workerConsumption (t + n) (continuationHistory h future) /
              X.workerConsumption (t + n + 1)
                (childHistory (continuationHistory h future) s)) *
          (bankDetailedPortfolioReturnAt P X (t + n)
              (continuationHistory h future)
              (X.bankTightness (t + n) (continuationHistory h future))
              (X.bankLoans (t + n) (continuationHistory h future))
              (X.reservesPrePayment (t + n) (continuationHistory h future))
              (X.bankDeposits (t + n) (continuationHistory h future)) omega /
            X.bankEquity (t + n) (continuationHistory h future) /
            X.inflation (t + n + 1)
              (childHistory (continuationHistory h future) s))) := by
  rw [bankCumulativeSDFAt_childFutureHistory P X t h future s
    hcurrentConsumptionPos]
  rw [mul_assoc]
  rw [fullRetentionContinuation_joint_child P X t h n future payments
    s omega hrisk hcurrentConsumptionPos.ne' hchildConsumption hindividual
    haggregate]
  ring



/-- Expected owner payoff at relative date `n`: surviving banks distribute
their dividend, while banks exiting after the preceding return transfer their
real equity to the household. -/
noncomputable def bankContinuationPayoffTermAt
    (P : Primitives S) (X : Allocation S) (t : ℕ) (h : History S t)
    (p : BankContinuationPolicy S P.paymentSupport) (n : ℕ) : ℝ :=
  ∑ future : Fin n → S, ∑ payments : Fin n → P.paymentSupport,
    continuationTransitionWeight P.tree (currentState h) n future *
      continuationPaymentWeight P payments * bankCumulativeSDFAt P X t h future *
      ((1 - P.bankExit) ^ n * p.dividend n future payments +
        if n = 0 then 0 else
          (1 - P.bankExit) ^ (n - 1) * P.bankExit * p.equity n future payments)

theorem bankContinuationPayoffTermAt_zero
    {S : Type*} [Fintype S] (P : Primitives S) (X : Allocation S)
    (t : ℕ) (h : History S t)
    (p : BankContinuationPolicy S P.paymentSupport)
    (hconsumption : 0 < X.workerConsumption t h) :
    bankContinuationPayoffTermAt P X t h p 0 =
      p.dividend 0 (fun j ↦ Fin.elim0 j) (fun j ↦ Fin.elim0 j) := by
  classical
  unfold bankContinuationPayoffTermAt continuationTransitionWeight
    continuationPaymentWeight bankCumulativeSDFAt
  simp only [Finset.univ_unique, Finset.sum_singleton, pow_zero,
    if_pos, one_mul]
  rw [continuationHistory_zero]
  have hfuture : (default : Fin 0 → S) = (fun j ↦ Fin.elim0 j) :=
    Subsingleton.elim _ _
  have hpayments : (default : Fin 0 → P.paymentSupport) =
      (fun j ↦ Fin.elim0 j) := Subsingleton.elim _ _
  rw [hfuture, hpayments]
  have hpow : X.workerConsumption t h ^ (-P.workerRiskAversion) ≠ 0 :=
    (Real.rpow_pos_of_pos hconsumption (-P.workerRiskAversion)).ne'
  simp
  field_simp [hpow]

/-- Exact one-step decomposition of every positive-date owner-payoff term.
The first state/payment pair is separated from its continuation policy.  A
surviving bank contributes the discounted tail term; the equity of a bank that
exits after the first return appears only when the tail date is zero.  This is
an algebraic decomposition, not a Bellman optimality assumption. -/
theorem bankContinuationPayoffTermAt_succ
    {S : Type*} [Fintype S] (P : Primitives S) (X : Allocation S)
    (t : ℕ) (h : History S t)
    (p : BankContinuationPolicy S P.paymentSupport) (n : ℕ)
    (hchild : ∀ s, 0 < P.tree.transition (currentState h) s →
      0 < X.workerConsumption (t + 1) (childHistory h s)) :
    bankContinuationPayoffTermAt P X t h p (n + 1) =
      ∑ s, ∑ ω : P.paymentSupport,
        P.tree.transition (currentState h) s * P.paymentProbability ω *
          bankStochasticDiscountAt P X t h s *
          ((1 - P.bankExit) *
              bankContinuationPayoffTermAt P X (t + 1) (childHistory h s)
                (tailBankContinuationPolicy p s ω) n +
            if n = 0 then P.bankExit *
              p.equity 1 (fun _ ↦ s) (fun _ ↦ ω) else 0) := by
  classical
  unfold bankContinuationPayoffTermAt
  rw [sum_pi_snoc]
  apply Finset.sum_congr rfl
  intro s _hsum
  rw [Finset.sum_comm, sum_pi_snoc]
  apply Finset.sum_congr rfl
  intro ω _hωsum
  rw [Finset.sum_comm]
  have hsnonneg : 0 ≤ P.tree.transition (currentState h) s :=
    P.tree.transition_nonneg _ _
  by_cases hs : P.tree.transition (currentState h) s = 0
  · simp_rw [continuationTransitionWeight_snoc]
    simp [hs]
  · have hspos : 0 < P.tree.transition (currentState h) s :=
      lt_of_le_of_ne hsnonneg (Ne.symm hs)
    by_cases hn : n = 0
    · subst n
      simp only [Finset.univ_unique, Finset.sum_singleton]
      have hfuture : (default : Fin 0 → S) = (fun j ↦ Fin.elim0 j) :=
        Subsingleton.elim _ _
      have hpayments : (default : Fin 0 → P.paymentSupport) =
          (fun j ↦ Fin.elim0 j) := Subsingleton.elim _ _
      have hsnocFuture : Fin.snoc (fun j : Fin 0 ↦ Fin.elim0 j) s =
          (fun _ : Fin 1 ↦ s) := by
        funext j
        simp [Fin.snoc]
      have hsnocPayment : Fin.snoc
          (fun j : Fin 0 ↦ (Fin.elim0 j : P.paymentSupport)) ω =
          (fun _ : Fin 1 ↦ ω) := by
        funext j
        simp [Fin.snoc]
      rw [hfuture, hpayments, continuationTransitionWeight_snoc,
        continuationPaymentWeight_snoc,
        bankCumulativeSDFAt_snoc P X t h (fun j ↦ Fin.elim0 j) s
          (hchild s hspos)]
      simp only [tailBankContinuationPolicy, oldestExtendedFuture]
      rw [hsnocFuture, hsnocPayment]
      simp [currentState,
        continuationTransitionWeight,
        continuationPaymentWeight, bankCumulativeSDFAt, continuationHistory_zero,
        pow_one, pow_zero, add_zero]
      have hchildPow : X.workerConsumption (t + 1) (childHistory h s) ^
          (-P.workerRiskAversion) ≠ 0 :=
        (Real.rpow_pos_of_pos (hchild s hspos) (-P.workerRiskAversion)).ne'
      field_simp [hchildPow]
    · rcases n with _ | k
      · exact (hn rfl).elim
      · simp only [Nat.succ_ne_zero, if_false, add_zero]
        conv_rhs => rw [← mul_assoc]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro future _hfuture
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro payments _hpayments
        rw [continuationTransitionWeight_snoc,
          continuationPaymentWeight_snoc,
          bankCumulativeSDFAt_snoc P X t h future s (hchild s hspos)]
        simp only [tailBankContinuationPolicy, oldestExtendedFuture,
          Nat.add_sub_cancel]
        simp only [currentState, childHistory, Fin.cases_zero]
        rw [pow_succ', pow_succ']
        ring

/-- Exchange an infinite sum with two finite sums.  Kept private because it is
only proof infrastructure for the bank continuation decomposition. -/
private theorem tsum_fintype_sum_fintype_sum {I J : Type*} [Fintype I]
    [Fintype J] (f : I → J → ℕ → ℝ)
    (hf : ∀ i j, Summable (f i j)) :
    (∑' n, ∑ i, ∑ j, f i j n) = ∑ i, ∑ j, ∑' n, f i j n := by
  classical
  rw [Summable.tsum_finsetSum (s := Finset.univ)
      (fun i _hi ↦ summable_sum (fun j _hj ↦ hf i j))]
  apply Finset.sum_congr rfl
  intro i _hi
  exact Summable.tsum_finsetSum (s := Finset.univ) (fun j _hj ↦ hf i j)

/-- Sum a constant multiple of a summable series plus one date-zero payment. -/
private theorem tsum_const_mul_add_ite_zero (c a b : ℝ) (f : ℕ → ℝ)
    (hf : Summable f) :
    (∑' n, c * (a * f n + if n = 0 then b else 0)) =
      c * (a * ∑' n, f n + b) := by
  have ha : Summable (fun n ↦ a * f n) := hf.mul_left a
  have hb : Summable (fun n : ℕ ↦ if n = 0 then b else 0) :=
    (hasSum_ite_eq 0 b).summable
  have hb_tsum : (∑' n : ℕ, if n = 0 then b else 0) = b :=
    (hasSum_ite_eq 0 b).tsum_eq
  rw [(ha.add hb).tsum_mul_left c, ha.tsum_add hb, hf.tsum_mul_left a,
    hb_tsum]

theorem bankContinuationPayoffTermAt_scale
    (P : Primitives S) (X : Allocation S) (t : ℕ) (h : History S t)
    (p : BankContinuationPolicy S P.paymentSupport) (c : ℝ) (n : ℕ) :
    bankContinuationPayoffTermAt P X t h
        (scaleBankContinuationPolicy c p) n =
      c * bankContinuationPayoffTermAt P X t h p n := by
  classical
  unfold bankContinuationPayoffTermAt
  simp only [scaleBankContinuationPolicy]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro future _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro payments _
  split_ifs <;> ring

def BankContinuationObjectiveWellDefinedAt
    (P : Primitives S) (X : Allocation S) (t : ℕ) (h : History S t)
    (p : BankContinuationPolicy S P.paymentSupport) : Prop :=
  Summable (bankContinuationPayoffTermAt P X t h p)

noncomputable def bankContinuationPayoffAt
    (P : Primitives S) (X : Allocation S) (t : ℕ) (h : History S t)
    (p : BankContinuationPolicy S P.paymentSupport) : ℝ :=
  ∑' n, bankContinuationPayoffTermAt P X t h p n

/-- Exact first-step decomposition of the infinite owner payoff.  The analytic
boundary is explicit: every state/payment-specific tail series must be
summable.  No Bellman comparison, terminal condition, FOC, or equilibrium
conclusion is assumed here. -/
theorem bankContinuationPayoffAt_first_step
    {S : Type*} [Fintype S] (P : Primitives S) (X : Allocation S)
    (t : ℕ) (h : History S t)
    (p : BankContinuationPolicy S P.paymentSupport)
    (hconsumption : 0 < X.workerConsumption t h)
    (hchild : ∀ s, 0 < P.tree.transition (currentState h) s →
      0 < X.workerConsumption (t + 1) (childHistory h s))
    (htail : ∀ s, 0 < P.tree.transition (currentState h) s → ∀ ω,
      Summable (bankContinuationPayoffTermAt P X (t + 1) (childHistory h s)
        (tailBankContinuationPolicy p s ω))) :
    bankContinuationPayoffAt P X t h p =
      p.dividend 0 (fun j ↦ Fin.elim0 j) (fun j ↦ Fin.elim0 j) +
        ∑ s, ∑ ω : P.paymentSupport,
          P.tree.transition (currentState h) s * P.paymentProbability ω *
            bankStochasticDiscountAt P X t h s *
            ((1 - P.bankExit) *
                bankContinuationPayoffAt P X (t + 1) (childHistory h s)
                  (tailBankContinuationPolicy p s ω) +
              P.bankExit * p.equity 1 (fun _ ↦ s) (fun _ ↦ ω)) := by
  classical
  let A : S → P.paymentSupport → ℝ := fun s ω ↦
    P.tree.transition (currentState h) s * P.paymentProbability ω *
      bankStochasticDiscountAt P X t h s
  let E : S → P.paymentSupport → ℝ := fun s ω ↦
    P.bankExit * p.equity 1 (fun _ ↦ s) (fun _ ↦ ω)
  have hcomponent : ∀ s ω, Summable (fun n ↦
      A s ω * ((1 - P.bankExit) *
        bankContinuationPayoffTermAt P X (t + 1) (childHistory h s)
          (tailBankContinuationPolicy p s ω) n +
        if n = 0 then E s ω else 0)) := by
    intro s ω
    by_cases hs : P.tree.transition (currentState h) s = 0
    · simp [A, hs]
    have hspos : 0 < P.tree.transition (currentState h) s :=
      lt_of_le_of_ne (P.tree.transition_nonneg _ _) (Ne.symm hs)
    have ha := (htail s hspos ω).mul_left (1 - P.bankExit)
    have he : Summable (fun n : ℕ ↦ if n = 0 then E s ω else 0) :=
      (hasSum_ite_eq 0 (E s ω)).summable
    exact (ha.add he).mul_left (A s ω)
  have hsucc : Summable (fun n ↦
      bankContinuationPayoffTermAt P X t h p (n + 1)) := by
    have hsums : Summable (fun n ↦ ∑ s, ∑ ω : P.paymentSupport,
        A s ω * ((1 - P.bankExit) *
          bankContinuationPayoffTermAt P X (t + 1) (childHistory h s)
            (tailBankContinuationPolicy p s ω) n +
          if n = 0 then E s ω else 0)) :=
      summable_sum (fun s _hs ↦ summable_sum (fun ω _hω ↦ hcomponent s ω))
    apply hsums.congr
    intro n
    simpa [A, E] using
      (bankContinuationPayoffTermAt_succ P X t h p n hchild).symm
  have hfull : Summable (bankContinuationPayoffTermAt P X t h p) :=
    (summable_nat_add_iff 1).mp hsucc
  unfold bankContinuationPayoffAt
  rw [hfull.tsum_eq_zero_add,
    bankContinuationPayoffTermAt_zero P X t h p hconsumption]
  rw [tsum_congr (fun n ↦ bankContinuationPayoffTermAt_succ P X t h p n hchild)]
  change _ + (∑' n, ∑ s, ∑ ω : P.paymentSupport,
      A s ω * ((1 - P.bankExit) *
        bankContinuationPayoffTermAt P X (t + 1) (childHistory h s)
          (tailBankContinuationPolicy p s ω) n +
        if n = 0 then E s ω else 0)) = _
  rw [tsum_fintype_sum_fintype_sum]
  · apply congrArg (fun z ↦
      p.dividend 0 (fun j ↦ Fin.elim0 j) (fun j ↦ Fin.elim0 j) + z)
    apply Finset.sum_congr rfl
    intro s _hs
    apply Finset.sum_congr rfl
    intro ω _hω
    by_cases hs : P.tree.transition (currentState h) s = 0
    · simp [A, hs]
    · have hspos : 0 < P.tree.transition (currentState h) s :=
        lt_of_le_of_ne (P.tree.transition_nonneg _ _) (Ne.symm hs)
      rw [tsum_const_mul_add_ite_zero (A s ω) (1 - P.bankExit) (E s ω) _
        (htail s hspos ω)]
  · exact hcomponent

/-- Expected discounted value carried by banks that survive to horizon `T`.
The source requires this tail to vanish; objective summability alone is not
used as a substitute for the economic terminal condition. -/
noncomputable def bankSurvivingValueTermAt
    (P : Primitives S) (X : Allocation S) (t : ℕ) (h : History S t)
    (p : BankContinuationPolicy S P.paymentSupport) (T : ℕ) : ℝ :=
  ∑ future : Fin T → S, ∑ payments : Fin T → P.paymentSupport,
    continuationTransitionWeight P.tree (currentState h) T future *
      continuationPaymentWeight P payments * bankCumulativeSDFAt P X t h future *
      (1 - P.bankExit) ^ T * p.equity T future payments

def BankContinuationTerminalConditionAt
    (P : Primitives S) (X : Allocation S) (t : ℕ) (h : History S t)
    (p : BankContinuationPolicy S P.paymentSupport) : Prop :=
  Tendsto (bankSurvivingValueTermAt P X t h p) atTop (nhds 0)

/-- The continuation policy starts from the candidate bank's current equity,
dividend and pre-payment portfolio.  The empty future/payment histories are
unique, so these are literal date-zero equalities rather than distributional
shortcuts. -/
def BankContinuationStartsWithPlanAt
    (p : BankPlan S) (t : ℕ) (h : History S t)
    (q : BankContinuationPolicy S Ω) : Prop :=
  let emptyS : Fin 0 → S := fun j ↦ Fin.elim0 j
  let emptyΩ : Fin 0 → Ω := fun j ↦ Fin.elim0 j
  q.equity 0 emptyS emptyΩ = p.equity t h ∧
  q.dividend 0 emptyS emptyΩ = p.dividend t h ∧
  q.retainedEquity 0 emptyS emptyΩ = p.retainedEquity t h ∧
  q.loans 0 emptyS emptyΩ = p.loans t h ∧
  q.reserves 0 emptyS emptyΩ = p.reservesPre t h ∧
  q.deposits 0 emptyS emptyΩ = p.deposits t h

/-- At positive current equity, the explicitly constructed normalized policy
starts from all six fields of the input bank plan. -/
theorem bankContinuationPolicyFromPlan_startsWithPlanAt
    (P : Primitives S) (X : Allocation S) (p : BankPlan S)
    (t : ℕ) (h : History S t) (hequity : p.equity t h ≠ 0) :
    BankContinuationStartsWithPlanAt p t h
      (bankContinuationPolicyFromPlan P X p t h) := by
  unfold BankContinuationStartsWithPlanAt
  simp only [bankContinuationPolicyFromPlan,
    bankContinuationPlanScaleAt, bankContinuationEquityFromPlan_zero,
    Nat.add_zero]
  rw [continuationHistory_zero h (fun j : Fin 0 ↦ Fin.elim0 j)]
  rw [div_self hequity]
  simp

/-- Literal infinite-horizon bank optimality at a history.  Both candidate and
deviating policies use the full supported payment-history carrier and must
have a well-defined discounted owner payoff. -/
def BankContinuationOptimalAt
    (P : Primitives S) (X : Allocation S) (t : ℕ) (h : History S t)
    (initialEquity : ℝ)
    (candidate : BankContinuationPolicy S P.paymentSupport) : Prop :=
  BankContinuationFeasibleAt P X t h initialEquity candidate ∧
  BankContinuationObjectiveWellDefinedAt P X t h candidate ∧
  BankContinuationTerminalConditionAt P X t h candidate ∧
  ∀ alternative,
    BankContinuationFeasibleAt P X t h initialEquity alternative →
    BankContinuationObjectiveWellDefinedAt P X t h alternative →
    bankContinuationPayoffAt P X t h alternative ≤
      bankContinuationPayoffAt P X t h candidate

theorem bankContinuationObjectiveWellDefinedAt_scale_iff
    (P : Primitives S) (X : Allocation S) (t : ℕ) (h : History S t)
    (p : BankContinuationPolicy S P.paymentSupport) (c : ℝ) (hc : c ≠ 0) :
    BankContinuationObjectiveWellDefinedAt P X t h
        (scaleBankContinuationPolicy c p) ↔
      BankContinuationObjectiveWellDefinedAt P X t h p := by
  unfold BankContinuationObjectiveWellDefinedAt
  have heq :
      (fun n ↦ bankContinuationPayoffTermAt P X t h
        (scaleBankContinuationPolicy c p) n) =
        (fun n ↦ c * bankContinuationPayoffTermAt P X t h p n) := by
    funext n
    exact bankContinuationPayoffTermAt_scale P X t h p c n
  change Summable (fun n ↦ bankContinuationPayoffTermAt P X t h
      (scaleBankContinuationPolicy c p) n) ↔
    Summable (fun n ↦ bankContinuationPayoffTermAt P X t h p n)
  rw [heq]
  exact summable_mul_left_iff hc

theorem bankContinuationPayoffAt_scale
    (P : Primitives S) (X : Allocation S) (t : ℕ) (h : History S t)
    (p : BankContinuationPolicy S P.paymentSupport) (c : ℝ)
    (hp : BankContinuationObjectiveWellDefinedAt P X t h p) :
    bankContinuationPayoffAt P X t h (scaleBankContinuationPolicy c p) =
      c * bankContinuationPayoffAt P X t h p := by
  unfold bankContinuationPayoffAt
  simp_rw [bankContinuationPayoffTermAt_scale]
  exact hp.tsum_mul_left c

/-- Degree-one continuation-value conclusion used in the local Bellman
reduction.  It is kept separate so it cannot be mistaken for a FOC or be
hidden inside the candidate's desired optimality conclusion. -/
def BankValueHomogeneousAt (P : Primitives S) (t : ℕ) (h : History S t)
    (bankValue : BankValueProcess S) : Prop :=
  ∀ c equity s, 0 < c → 0 ≤ equity →
    0 < P.tree.transition (currentState h) s →
    bankValue (t + 1) (c * equity) (childHistory h s) =
      c * bankValue (t + 1) equity (childHistory h s)

/-- Source dynamic value conditions instantiated with the actual
payment-history continuation carrier, its economic feasibility constraints,
its discounted owner payoff and its explicit summability domain.  Only finite
attained value and dominance of every admissible continuation are hypotheses;
both directions of policy scaling and payoff homogeneity are theorems above. -/
def BankDynamicHomogeneityConditionsAt
    (P : Primitives S) (X : Allocation S) (t : ℕ) (h : History S t)
    (bankValue : BankValueProcess S) : Prop :=
  ∀ s, 0 < P.tree.transition (currentState h) s →
    (∀ equity, 0 ≤ equity → ∃ p,
        BankContinuationFeasibleAt P X (t + 1) (childHistory h s) equity p ∧
        BankContinuationObjectiveWellDefinedAt P X (t + 1)
          (childHistory h s) p ∧
        bankContinuationPayoffAt P X (t + 1) (childHistory h s) p =
          bankValue (t + 1) equity (childHistory h s)) ∧
    (∀ equity p,
      BankContinuationFeasibleAt P X (t + 1) (childHistory h s) equity p →
      BankContinuationObjectiveWellDefinedAt P X (t + 1)
          (childHistory h s) p →
      bankContinuationPayoffAt P X (t + 1) (childHistory h s) p ≤
        bankValue (t + 1) equity (childHistory h s))

theorem bankValueHomogeneous_of_dynamicPolicyConditions
    (P : Primitives S) (X : Allocation S) (t : ℕ) (h : History S t)
    (bankValue : BankValueProcess S)
    (H : BankDynamicHomogeneityConditionsAt P X t h bankValue) :
    BankValueHomogeneousAt P t h bankValue := by
  intro c equity s hc hequity hs
  rcases H s hs with ⟨hattain, hupper⟩
  rcases hattain equity hequity with ⟨p, hpfeasible, hpdefined, hpvalue⟩
  have hscaledFeasible := bankContinuationFeasibleAt_scale P X (t + 1)
    (childHistory h s) equity c p hc hpfeasible
  have hscaledDefined :=
    (bankContinuationObjectiveWellDefinedAt_scale_iff P X (t + 1)
      (childHistory h s) p c hc.ne').2 hpdefined
  have hlower := hupper (c * equity) (scaleBankContinuationPolicy c p)
    hscaledFeasible hscaledDefined
  rw [bankContinuationPayoffAt_scale P X (t + 1) (childHistory h s) p c
    hpdefined, hpvalue] at hlower
  rcases hattain (c * equity) (mul_nonneg hc.le hequity) with
    ⟨q, hqfeasible, hqdefined, hqvalue⟩
  have hcinv : 0 < (1 / c : ℝ) := one_div_pos.mpr hc
  have hbackFeasibleRaw := bankContinuationFeasibleAt_scale P X (t + 1)
    (childHistory h s) (c * equity) (1 / c) q hcinv hqfeasible
  have hbackFeasible : BankContinuationFeasibleAt P X (t + 1)
      (childHistory h s) equity (scaleBankContinuationPolicy (1 / c) q) := by
    convert hbackFeasibleRaw using 1 <;> field_simp [hc.ne']
  have hbackDefined :=
    (bankContinuationObjectiveWellDefinedAt_scale_iff P X (t + 1)
      (childHistory h s) q (1 / c) (one_div_ne_zero hc.ne')).2 hqdefined
  have hbackUpper := hupper equity (scaleBankContinuationPolicy (1 / c) q)
    hbackFeasible hbackDefined
  have hrescale := bankContinuationPayoffAt_scale P X (t + 1)
    (childHistory h s) (scaleBankContinuationPolicy (1 / c) q) c
    hbackDefined
  rw [scaleBankContinuationPolicy_inv c hc.ne' q] at hrescale
  rw [hqvalue] at hrescale
  nlinarith

/-- Transparent source Bellman environment.  It contains positive current and
successor consumption, the explicit household SDF and real return, a
real-valued continuation value, Bellman equality at the candidate,
and the literal Bellman inequality against every locally feasible deviation.
It deliberately contains no static-optimality, FOC, KKT, covariance, or spread
conjunct.  Dynamic value conditions and the derived homogeneity theorem remain
separate and provenance-visible. -/
def BankBellmanLocalEnvironmentAt
    (P : Primitives S) (X : Allocation S) (t : ℕ) (h : History S t)
    (p : BankPlan S) (tightness : ℝ) (bankValue : BankValueProcess S) : Prop :=
  0 < X.workerConsumption t h ∧
  (∀ s, 0 < P.tree.transition (currentState h) s →
    0 < X.workerConsumption (t + 1) (childHistory h s)) ∧
  (∀ s, 0 < P.tree.transition (currentState h) s →
    0 < bankStochasticDiscountAt P X t h s) ∧
  0 ≤ p.dividend t h ∧
  p.retainedEquity t h = p.equity t h - p.dividend t h ∧
  BankStaticPortfolioFeasibleAt P X t h
    (bankOTCDeficitSlopeAt P X t h tightness)
    (bankOTCSurplusSlopeAt P X t h tightness)
    (p.retainedEquity t h) (p.loans t h) (p.reservesPre t h)
    (p.deposits t h) ∧
  bankValue t (p.equity t h) h = p.dividend t h +
    bankBellmanContinuationAt P X t h
      (bankOTCDeficitSlopeAt P X t h tightness)
      (bankOTCSurplusSlopeAt P X t h tightness)
      (p.loans t h) (p.reservesPre t h) (p.deposits t h) (bankValue (t + 1)) ∧
  (∀ loans reserves deposits,
    BankStaticPortfolioFeasibleAt P X t h
      (bankOTCDeficitSlopeAt P X t h tightness)
      (bankOTCSurplusSlopeAt P X t h tightness)
      (p.retainedEquity t h) loans reserves deposits →
    p.dividend t h + bankBellmanContinuationAt P X t h
      (bankOTCDeficitSlopeAt P X t h tightness)
      (bankOTCSurplusSlopeAt P X t h tightness)
      loans reserves deposits (bankValue (t + 1)) ≤ bankValue t (p.equity t h) h) ∧
  0 < bankBellmanContinuationWeightAt P X t h (bankValue (t + 1))

/-- Taking the first supported successor of a spliced policy recovers exactly
the continuation assigned to that state/payment pair. -/
theorem tail_spliceBankContinuationPolicy
    {S Ω : Type*}
    (currentEquity currentDividend currentRetained currentLoans currentReserves
      currentDeposits : ℝ)
    (continuation : S → Ω → BankContinuationPolicy S Ω)
    (s : S) (ω : Ω) :
    tailBankContinuationPolicy
        (spliceBankContinuationPolicy currentEquity currentDividend currentRetained
          currentLoans currentReserves currentDeposits continuation) s ω =
      continuation s ω := by
  rcases hq : continuation s ω with
    ⟨equity, dividend, retainedEquity, loans, reserves, deposits⟩
  rw [BankContinuationPolicy.mk.injEq]
  repeat' apply And.intro
  all_goals
    funext n future payments
    simp [tailBankContinuationPolicy, spliceBankContinuationPolicy,
      oldestExtendedFuture, hq]

/-- Summable supported successor tails imply summability of the spliced
whole-policy objective.  Zero-probability aggregate successors require no
conditional objective. -/
theorem bankContinuationObjectiveWellDefinedAt_of_tails
    {S : Type*} [Fintype S] (P : Primitives S) (X : Allocation S)
    (t : ℕ) (h : History S t)
    (p : BankContinuationPolicy S P.paymentSupport)
    (hchild : ∀ s, 0 < P.tree.transition (currentState h) s →
      0 < X.workerConsumption (t + 1) (childHistory h s))
    (htail : ∀ s, 0 < P.tree.transition (currentState h) s → ∀ ω,
      BankContinuationObjectiveWellDefinedAt P X (t + 1) (childHistory h s)
        (tailBankContinuationPolicy p s ω)) :
    BankContinuationObjectiveWellDefinedAt P X t h p := by
  classical
  let A : S → P.paymentSupport → ℝ := fun s ω ↦
    P.tree.transition (currentState h) s * P.paymentProbability ω *
      bankStochasticDiscountAt P X t h s
  let E : S → P.paymentSupport → ℝ := fun s ω ↦
    P.bankExit * p.equity 1 (fun _ ↦ s) (fun _ ↦ ω)
  have hcomponent : ∀ s ω, Summable (fun n ↦
      A s ω * ((1 - P.bankExit) *
        bankContinuationPayoffTermAt P X (t + 1) (childHistory h s)
          (tailBankContinuationPolicy p s ω) n +
        if n = 0 then E s ω else 0)) := by
    intro s ω
    by_cases hs : P.tree.transition (currentState h) s = 0
    · simp [A, hs]
    have hspos : 0 < P.tree.transition (currentState h) s :=
      lt_of_le_of_ne (P.tree.transition_nonneg _ _) (Ne.symm hs)
    have ha := (htail s hspos ω).mul_left (1 - P.bankExit)
    have he : Summable (fun n : ℕ ↦ if n = 0 then E s ω else 0) :=
      (hasSum_ite_eq 0 (E s ω)).summable
    exact (ha.add he).mul_left (A s ω)
  have hsums : Summable (fun n ↦ ∑ s, ∑ ω : P.paymentSupport,
      A s ω * ((1 - P.bankExit) *
        bankContinuationPayoffTermAt P X (t + 1) (childHistory h s)
          (tailBankContinuationPolicy p s ω) n +
        if n = 0 then E s ω else 0)) :=
    summable_sum (fun s _hs ↦ summable_sum (fun ω _hω ↦ hcomponent s ω))
  have hsucc : Summable (fun n ↦
      bankContinuationPayoffTermAt P X t h p (n + 1)) := by
    apply hsums.congr
    intro n
    simpa [A, E] using
      (bankContinuationPayoffTermAt_succ P X t h p n hchild).symm
  exact (summable_nat_add_iff 1).mp hsucc

/-- The date-one equity stored by a feasible continuation candidate is the
actual real post-settlement return of its date-zero portfolio. -/
theorem continuationCandidate_nextEquity_eq_realReturn
    {S : Type*} [Fintype S] [DecidableEq S]
    (P : Primitives S) (X : Allocation S) (p : BankPlan S)
    (t : ℕ) (h : History S t)
    (candidate : BankContinuationPolicy S P.paymentSupport)
    (hfeasible : BankContinuationFeasibleAt P X t h (p.equity t h) candidate)
    (hstarts : BankContinuationStartsWithPlanAt p t h candidate)
    (s : S) (hs : 0 < P.tree.transition (currentState h) s)
    (ω : P.paymentSupport) :
    candidate.equity 1 (fun _ ↦ s) (fun _ ↦ ω) =
      bankRealPortfolioReturnAt P X t h
        (bankOTCDeficitSlopeAt P X t h (X.bankTightness t h))
        (bankOTCSurplusSlopeAt P X t h (X.bankTightness t h))
        (p.loans t h) (p.reservesPre t h) (p.deposits t h) ω s := by
  let emptyS : Fin 0 → S := fun j ↦ Fin.elim0 j
  let emptyΩ : Fin 0 → P.paymentSupport := fun j ↦ Fin.elim0 j
  rcases hstarts with ⟨_equityStart, _dividendStart, _retainedStart,
    hloansStart, hreservesStart, hdepositsStart⟩
  have hzero := hfeasible.2 0 emptyS emptyΩ (by trivial)
  have hreserveRate : 0 < X.reserveRate t h := by
    simpa [emptyS, continuationHistory_zero] using
      hzero.2.2.2.2.2.2.2.2.2.2.2.2.1
  have htransition := hzero.2.2.2.2.2.2.2.2.2.2.2.2.2 ω |>.2.2 s
  have hs' : 0 < P.tree.transition
      (currentState (continuationHistory h emptyS)) s := by
    simpa [emptyS, continuationHistory_zero] using hs
  specialize htransition hs'
  have hchildFuture : childFutureHistory emptyS s = (fun _ ↦ s) := by
    funext j
    exact Fin.eq_zero j ▸ rfl
  have hchildPayment : childPaymentHistory emptyΩ ω = (fun _ ↦ ω) := by
    funext j
    exact Fin.eq_zero j ▸ rfl
  rw [hchildFuture, hchildPayment] at htransition
  unfold bankRealPortfolioReturnAt
  rw [← bankDetailedPortfolioReturn_eq_reduced P X t h
    (X.bankTightness t h) (p.loans t h) (p.reservesPre t h)
    (p.deposits t h) ω hreserveRate.ne']
  simpa [emptyS, emptyΩ, hloansStart, hreservesStart, hdepositsStart,
    continuationHistory_zero] using htransition

/-- Dynamic feasibility and literal date-zero agreement imply the reduced
one-history portfolio feasibility used by the bank Bellman problem. -/
theorem continuationCandidate_staticFeasibleAt
    {S : Type*} [Fintype S] [DecidableEq S]
    (P : Primitives S) (X : Allocation S) (p : BankPlan S)
    (t : ℕ) (h : History S t)
    (candidate : BankContinuationPolicy S P.paymentSupport)
    (hfeasible : BankContinuationFeasibleAt P X t h (p.equity t h) candidate)
    (hstarts : BankContinuationStartsWithPlanAt p t h candidate) :
    BankStaticPortfolioFeasibleAt P X t h
      (bankOTCDeficitSlopeAt P X t h (X.bankTightness t h))
      (bankOTCSurplusSlopeAt P X t h (X.bankTightness t h))
      (p.retainedEquity t h) (p.loans t h) (p.reservesPre t h)
      (p.deposits t h) := by
  let emptyS : Fin 0 → S := fun j ↦ Fin.elim0 j
  let emptyΩ : Fin 0 → P.paymentSupport := fun j ↦ Fin.elim0 j
  rcases hstarts with ⟨_equityStart, _dividendStart, hretainedStart,
    hloansStart, hreservesStart, hdepositsStart⟩
  have hzero := hfeasible.2 0 emptyS emptyΩ (by trivial)
  rcases hzero with ⟨equityNonneg, dividendNonneg, hretainedNonneg,
    hloansNonneg, hreservesNonneg, hdepositsNonneg, zeroBoundary,
    retainedPos, retention, hbalance, hdepositCap, hloanCap,
    hreserveRate, hsettlement⟩
  have hreserveRate' : 0 < X.reserveRate t h := by
    simpa [emptyS, continuationHistory_zero] using hreserveRate
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [emptyS, emptyΩ, hloansStart] using hloansNonneg
  · simpa [emptyS, emptyΩ, hreservesStart] using hreservesNonneg
  · simpa [emptyS, emptyΩ, hdepositsStart] using hdepositsNonneg
  · simpa [emptyS, emptyΩ, hloansStart, hreservesStart, hdepositsStart,
      hretainedStart] using hbalance
  · simpa [emptyS, emptyΩ, hdepositsStart, hretainedStart] using hdepositCap
  · simpa [emptyS, emptyΩ, hloansStart, hretainedStart] using hloanCap
  · intro ω hω s hs
    change 0 ≤ bankReducedPortfolioReturn P X t h
      (bankOTCDeficitSlopeAt P X t h (X.bankTightness t h))
      (bankOTCSurplusSlopeAt P X t h (X.bankTightness t h))
      (p.loans t h) (p.reservesPre t h) (p.deposits t h) ω /
        X.inflation (t + 1) (childHistory h s)
    let ωs : P.paymentSupport := ⟨ω, hω⟩
    have htransition := (hsettlement ωs).2.2 s hs
    have hsupported : FuturePathSupported P.tree (currentState h) 1
        (fun _ ↦ s) := by
      simpa [FuturePathSupported] using hs
    have hone := hfeasible.2 1 (fun _ ↦ s) (fun _ ↦ ωs) hsupported
    have hequityNonneg : 0 ≤ candidate.equity 1 (fun _ ↦ s) (fun _ ↦ ωs) :=
      hone.1
    have hchildFuture : childFutureHistory emptyS s = (fun _ ↦ s) := by
      funext j
      exact Fin.eq_zero j ▸ rfl
    have hchildPayment : childPaymentHistory emptyΩ ωs = (fun _ ↦ ωs) := by
      funext j
      exact Fin.eq_zero j ▸ rfl
    rw [hchildFuture, hchildPayment] at htransition
    rw [htransition] at hequityNonneg
    rw [← bankDetailedPortfolioReturn_eq_reduced P X t h
      (X.bankTightness t h) (p.loans t h) (p.reservesPre t h)
      (p.deposits t h) ω hreserveRate'.ne']
    simpa [emptyS, emptyΩ, hloansStart, hreservesStart, hdepositsStart,
      continuationHistory_zero] using hequityNonneg

/-- A feasible continuation whose supported tails realize `bankValue` has the
literal dividend-plus-Bellman payoff. -/
theorem bankContinuationPayoffAt_eq_dividend_add_bellman
    {S : Type*} [Fintype S] [DecidableEq S]
    (P : Primitives S) (X : Allocation S) (p : BankPlan S)
    (t : ℕ) (h : History S t) (bankValue : BankValueProcess S)
    (candidate : BankContinuationPolicy S P.paymentSupport)
    (hfeasible : BankContinuationFeasibleAt P X t h (p.equity t h) candidate)
    (hstarts : BankContinuationStartsWithPlanAt p t h candidate)
    (hconsumption : 0 < X.workerConsumption t h)
    (hchild : ∀ s, 0 < P.tree.transition (currentState h) s →
      0 < X.workerConsumption (t + 1) (childHistory h s))
    (htail : ∀ s, 0 < P.tree.transition (currentState h) s → ∀ ω,
      BankContinuationObjectiveWellDefinedAt P X (t + 1) (childHistory h s)
        (tailBankContinuationPolicy candidate s ω))
    (htailValue : ∀ s, 0 < P.tree.transition (currentState h) s → ∀ ω,
      bankContinuationPayoffAt P X (t + 1) (childHistory h s)
          (tailBankContinuationPolicy candidate s ω) =
        bankValue (t + 1)
          (candidate.equity 1 (fun _ ↦ s) (fun _ ↦ ω))
          (childHistory h s)) :
    bankContinuationPayoffAt P X t h candidate =
      p.dividend t h + bankBellmanContinuationAt P X t h
        (bankOTCDeficitSlopeAt P X t h (X.bankTightness t h))
        (bankOTCSurplusSlopeAt P X t h (X.bankTightness t h))
        (p.loans t h) (p.reservesPre t h) (p.deposits t h)
        (bankValue (t + 1)) := by
  rw [bankContinuationPayoffAt_first_step P X t h candidate hconsumption hchild
    (fun s hs ω ↦ htail s hs ω)]
  rcases hstarts with ⟨equityStart, hdividendStart, hretainedStart,
    hloansStart, hreservesStart, hdepositsStart⟩
  rw [hdividendStart]
  apply congrArg (fun z ↦ p.dividend t h + z)
  unfold bankBellmanContinuationAt
  rw [Finset.sum_subtype P.paymentSupport (fun x ↦ Iff.rfl)]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ω _hωsum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _hsum
  by_cases hs : P.tree.transition (currentState h) s = 0
  · simp [hs]
  have hspos : 0 < P.tree.transition (currentState h) s :=
    lt_of_le_of_ne (P.tree.transition_nonneg _ _) (Ne.symm hs)
  rw [htailValue s hspos ω]
  rw [continuationCandidate_nextEquity_eq_realReturn P X p t h candidate
    hfeasible ⟨equityStart, hdividendStart, hretainedStart, hloansStart,
      hreservesStart, hdepositsStart⟩ s hspos ω]
  ring

theorem bankStochasticDiscountAt_pos_of_consumption
    {S : Type*} [Fintype S] (P : Primitives S) (X : Allocation S)
    (t : ℕ) (h : History S t) (s : S)
    (hcurrent : 0 < X.workerConsumption t h)
    (hnext : 0 < X.workerConsumption (t + 1) (childHistory h s)) :
    0 < bankStochasticDiscountAt P X t h s := by
  unfold bankStochasticDiscountAt
  have hdiscount : 0 < P.workerDiscount :=
    lt_trans P.discount_order.1 P.discount_order.2.1
  positivity

/-- Positivity of the common continuation weight follows from positive exit,
positive supported consumption/inflation, and nonnegative unit franchise
values.  These prerequisites remain visible rather than being hidden in a
Bellman-environment record. -/
theorem bankBellmanContinuationWeightAt_pos_of_finiteValue
    {S : Type*} [Fintype S] (P : Primitives S) (X : Allocation S)
    (t : ℕ) (h : History S t) (bankValue : BankValueProcess S)
    (hcurrent : 0 < X.workerConsumption t h)
    (hchild : ∀ s, 0 < P.tree.transition (currentState h) s →
      0 < X.workerConsumption (t + 1) (childHistory h s))
    (hinflation : ∀ s, 0 < P.tree.transition (currentState h) s →
      0 < X.inflation (t + 1) (childHistory h s))
    (hexit : 0 < P.bankExit)
    (hvalue : ∀ s, 0 < P.tree.transition (currentState h) s →
      0 ≤ bankValue (t + 1) 1 (childHistory h s)) :
    0 < bankBellmanContinuationWeightAt P X t h (bankValue (t + 1)) := by
  classical
  have hsurvival : 0 ≤ 1 - P.bankExit := sub_nonneg.mpr P.bank_exit_mem.2
  have hexists : ∃ s, 0 < P.tree.transition (currentState h) s := by
    by_contra hnone
    push Not at hnone
    have hzero : ∀ s, P.tree.transition (currentState h) s = 0 := by
      intro s
      exact le_antisymm (hnone s) (P.tree.transition_nonneg _ _)
    have hone := P.tree.transition_sum_one (currentState h)
    simp [hzero] at hone
  unfold bankBellmanContinuationWeightAt
  apply Finset.sum_pos'
  · intro s _hsum
    by_cases hs : P.tree.transition (currentState h) s = 0
    · simp [hs]
    have hspos : 0 < P.tree.transition (currentState h) s :=
      lt_of_le_of_ne (P.tree.transition_nonneg _ _) (Ne.symm hs)
    have hsdf := (bankStochasticDiscountAt_pos_of_consumption P X t h s
      hcurrent (hchild s hspos)).le
    have hbracket : 0 ≤ (1 - P.bankExit) *
        bankValue (t + 1) 1 (childHistory h s) + P.bankExit :=
      add_nonneg (mul_nonneg hsurvival (hvalue s hspos)) hexit.le
    exact div_nonneg (mul_nonneg (mul_nonneg hspos.le hsdf) hbracket)
      (hinflation s hspos).le
  · rcases hexists with ⟨s, hs⟩
    refine ⟨s, Finset.mem_univ s, ?_⟩
    have hsdf := bankStochasticDiscountAt_pos_of_consumption P X t h s
      hcurrent (hchild s hs)
    have hbracket : 0 < (1 - P.bankExit) *
        bankValue (t + 1) 1 (childHistory h s) + P.bankExit :=
      add_pos_of_nonneg_of_pos (mul_nonneg hsurvival (hvalue s hs)) hexit
    exact div_pos (mul_pos (mul_pos hs hsdf) hbracket) (hinflation s hs)

/-- Supported tail dominance by the attained dynamic value gives the weak
Bellman upper bound for the candidate's actual infinite payoff. -/
theorem bankContinuationPayoffAt_le_dividend_add_bellman
    {S : Type*} [Fintype S] [DecidableEq S]
    (P : Primitives S) (X : Allocation S) (p : BankPlan S)
    (t : ℕ) (h : History S t) (bankValue : BankValueProcess S)
    (candidate : BankContinuationPolicy S P.paymentSupport)
    (hfeasible : BankContinuationFeasibleAt P X t h (p.equity t h) candidate)
    (hstarts : BankContinuationStartsWithPlanAt p t h candidate)
    (hconsumption : 0 < X.workerConsumption t h)
    (hchild : ∀ s, 0 < P.tree.transition (currentState h) s →
      0 < X.workerConsumption (t + 1) (childHistory h s))
    (htail : ∀ s, 0 < P.tree.transition (currentState h) s → ∀ ω,
      BankContinuationObjectiveWellDefinedAt P X (t + 1) (childHistory h s)
        (tailBankContinuationPolicy candidate s ω))
    (htailUpper : ∀ s, 0 < P.tree.transition (currentState h) s → ∀ ω,
      bankContinuationPayoffAt P X (t + 1) (childHistory h s)
          (tailBankContinuationPolicy candidate s ω) ≤
        bankValue (t + 1)
          (candidate.equity 1 (fun _ ↦ s) (fun _ ↦ ω))
          (childHistory h s)) :
    bankContinuationPayoffAt P X t h candidate ≤
      p.dividend t h + bankBellmanContinuationAt P X t h
        (bankOTCDeficitSlopeAt P X t h (X.bankTightness t h))
        (bankOTCSurplusSlopeAt P X t h (X.bankTightness t h))
        (p.loans t h) (p.reservesPre t h) (p.deposits t h)
        (bankValue (t + 1)) := by
  rw [bankContinuationPayoffAt_first_step P X t h candidate hconsumption hchild
    (fun s hs ω ↦ htail s hs ω)]
  rcases hstarts with ⟨equityStart, hdividendStart, hretainedStart,
    hloansStart, hreservesStart, hdepositsStart⟩
  rw [hdividendStart]
  gcongr
  unfold bankBellmanContinuationAt
  rw [Finset.sum_subtype P.paymentSupport (fun x ↦ Iff.rfl)]
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro ω _hωsum
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro s _hsum
  by_cases hs : P.tree.transition (currentState h) s = 0
  · simp [hs]
  have hspos : 0 < P.tree.transition (currentState h) s :=
    lt_of_le_of_ne (P.tree.transition_nonneg _ _) (Ne.symm hs)
  have hequityReturn := continuationCandidate_nextEquity_eq_realReturn P X p t h
    candidate hfeasible ⟨equityStart, hdividendStart, hretainedStart,
      hloansStart, hreservesStart, hdepositsStart⟩ s hspos ω
  rw [hequityReturn]
  have hsurvival : 0 ≤ 1 - P.bankExit := sub_nonneg.mpr P.bank_exit_mem.2
  have hsdf : 0 ≤ bankStochasticDiscountAt P X t h s :=
    (bankStochasticDiscountAt_pos_of_consumption P X t h s hconsumption
      (hchild s hspos)).le
  have hcoefficient : 0 ≤ P.tree.transition (currentState h) s *
      P.paymentProbability ω * bankStochasticDiscountAt P X t h s :=
    mul_nonneg (mul_nonneg hspos.le (P.payment_probability_nonneg ω)) hsdf
  have htailLe := htailUpper s hspos ω
  rw [hequityReturn] at htailLe
  have hinner := mul_le_mul_of_nonneg_left htailLe hsurvival
  have hinner' := add_le_add_right hinner
    (P.bankExit * bankRealPortfolioReturnAt P X t h
      (bankOTCDeficitSlopeAt P X t h (X.bankTightness t h))
      (bankOTCSurplusSlopeAt P X t h (X.bankTightness t h))
      (p.loans t h) (p.reservesPre t h) (p.deposits t h) ω s)
  have hweighted := mul_le_mul_of_nonneg_left hinner' hcoefficient
  simpa only [add_comm, mul_assoc, mul_left_comm, mul_comm] using hweighted

/-- The payoff of a spliced policy is the current dividend plus the Bellman
continuation when every supported tail is summable, starts from the actual
real return, and attains the declared continuation value. -/
theorem spliceBankContinuationPayoffAt_eq_dividend_add_bellman
    {S : Type*} [Fintype S] [DecidableEq S]
    (P : Primitives S) (X : Allocation S) (t : ℕ) (h : History S t)
    (currentEquity currentDividend currentRetained currentLoans currentReserves
      currentDeposits : ℝ)
    (continuation : S → P.paymentSupport →
      BankContinuationPolicy S P.paymentSupport)
    (bankValue : BankValueProcess S)
    (hconsumption : 0 < X.workerConsumption t h)
    (hchild : ∀ s, 0 < P.tree.transition (currentState h) s →
      0 < X.workerConsumption (t + 1) (childHistory h s))
    (hdefined : ∀ s, 0 < P.tree.transition (currentState h) s → ∀ ω,
      BankContinuationObjectiveWellDefinedAt P X (t + 1) (childHistory h s)
        (continuation s ω))
    (hinitial : ∀ s, 0 < P.tree.transition (currentState h) s → ∀ ω,
      (continuation s ω).equity 0 (fun j ↦ Fin.elim0 j)
          (fun j ↦ Fin.elim0 j) =
        bankRealPortfolioReturnAt P X t h
          (bankOTCDeficitSlopeAt P X t h (X.bankTightness t h))
          (bankOTCSurplusSlopeAt P X t h (X.bankTightness t h))
          currentLoans currentReserves currentDeposits ω s)
    (hvalue : ∀ s, 0 < P.tree.transition (currentState h) s → ∀ ω,
      bankContinuationPayoffAt P X (t + 1) (childHistory h s)
          (continuation s ω) =
        bankValue (t + 1)
          (bankRealPortfolioReturnAt P X t h
            (bankOTCDeficitSlopeAt P X t h (X.bankTightness t h))
            (bankOTCSurplusSlopeAt P X t h (X.bankTightness t h))
            currentLoans currentReserves currentDeposits ω s)
          (childHistory h s)) :
    bankContinuationPayoffAt P X t h
        (spliceBankContinuationPolicy currentEquity currentDividend currentRetained
          currentLoans currentReserves currentDeposits continuation) =
      currentDividend + bankBellmanContinuationAt P X t h
        (bankOTCDeficitSlopeAt P X t h (X.bankTightness t h))
        (bankOTCSurplusSlopeAt P X t h (X.bankTightness t h))
        currentLoans currentReserves currentDeposits (bankValue (t + 1)) := by
  let q := spliceBankContinuationPolicy currentEquity currentDividend
    currentRetained currentLoans currentReserves currentDeposits continuation
  have htail : ∀ s, 0 < P.tree.transition (currentState h) s → ∀ ω,
      BankContinuationObjectiveWellDefinedAt P X (t + 1) (childHistory h s)
        (tailBankContinuationPolicy q s ω) := by
    intro s hs ω
    rw [show tailBankContinuationPolicy q s ω = continuation s ω by
      exact tail_spliceBankContinuationPolicy currentEquity currentDividend
        currentRetained currentLoans currentReserves currentDeposits continuation s ω]
    exact hdefined s hs ω
  rw [bankContinuationPayoffAt_first_step P X t h q hconsumption hchild htail]
  change currentDividend + _ = currentDividend + _
  apply congrArg (fun z ↦ currentDividend + z)
  unfold bankBellmanContinuationAt
  rw [Finset.sum_subtype P.paymentSupport (fun x ↦ Iff.rfl)]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ω _hωsum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _hsum
  by_cases hs : P.tree.transition (currentState h) s = 0
  · simp [hs]
  have hspos : 0 < P.tree.transition (currentState h) s :=
    lt_of_le_of_ne (P.tree.transition_nonneg _ _) (Ne.symm hs)
  have htailEq := tail_spliceBankContinuationPolicy currentEquity currentDividend
    currentRetained currentLoans currentReserves currentDeposits continuation s ω
  rw [htailEq, hvalue s hspos ω]
  rw [show q.equity 1 (fun _ ↦ s) (fun _ ↦ ω) =
      (continuation s ω).equity 0 (fun j ↦ Fin.elim0 j)
        (fun j ↦ Fin.elim0 j) by
    simp only [q, spliceBankContinuationPolicy]
    congr 2 <;> exact Subsingleton.elim _ _]
  change _ * (_ * _ + P.bankExit *
      (continuation s ω).equity 0 (fun j ↦ Fin.elim0 j)
        (fun j ↦ Fin.elim0 j)) = _
  rw [hinitial s hspos ω]
  ring

/-- Every feasible current portfolio can be spliced with value-attaining
supported continuations.  The resulting infinite policy is feasible, has a
summable payoff, and realizes the literal Bellman objective. -/
theorem exists_feasible_splice_attaining_dynamicValue
    {S : Type*} [Fintype S] [DecidableEq S]
    (P : Primitives S) (X : Allocation S) (t : ℕ) (h : History S t)
    (currentEquity currentDividend currentRetained currentLoans currentReserves
      currentDeposits : ℝ) (bankValue : BankValueProcess S)
    (hdynamic : BankDynamicHomogeneityConditionsAt P X t h bankValue)
    (hequity : 0 < currentEquity) (hdividend : 0 ≤ currentDividend)
    (hretained : 0 < currentRetained)
    (hretention : currentRetained = currentEquity - currentDividend)
    (hreserveRate : 0 < X.reserveRate t h)
    (htightness : 0 < X.bankTightness t h)
    (hstatic : BankStaticPortfolioFeasibleAt P X t h
      (bankOTCDeficitSlopeAt P X t h (X.bankTightness t h))
      (bankOTCSurplusSlopeAt P X t h (X.bankTightness t h))
      currentRetained currentLoans currentReserves currentDeposits)
    (hconsumption : 0 < X.workerConsumption t h)
    (hchild : ∀ s, 0 < P.tree.transition (currentState h) s →
      0 < X.workerConsumption (t + 1) (childHistory h s)) :
    ∃ q : BankContinuationPolicy S P.paymentSupport,
      BankContinuationFeasibleAt P X t h currentEquity q ∧
      BankContinuationObjectiveWellDefinedAt P X t h q ∧
      bankContinuationPayoffAt P X t h q =
        currentDividend + bankBellmanContinuationAt P X t h
          (bankOTCDeficitSlopeAt P X t h (X.bankTightness t h))
          (bankOTCSurplusSlopeAt P X t h (X.bankTightness t h))
          currentLoans currentReserves currentDeposits (bankValue (t + 1)) := by
  classical
  let initial : S → P.paymentSupport → ℝ := fun s ω ↦
    bankRealPortfolioReturnAt P X t h
      (bankOTCDeficitSlopeAt P X t h (X.bankTightness t h))
      (bankOTCSurplusSlopeAt P X t h (X.bankTightness t h))
      currentLoans currentReserves currentDeposits ω s
  let zeroPolicy : BankContinuationPolicy S P.paymentSupport :=
    { equity := fun _ _ _ ↦ 0
      dividend := fun _ _ _ ↦ 0
      retainedEquity := fun _ _ _ ↦ 0
      loans := fun _ _ _ ↦ 0
      reserves := fun _ _ _ ↦ 0
      deposits := fun _ _ _ ↦ 0 }
  have hexists : ∀ s ω, ∃ q : BankContinuationPolicy S P.paymentSupport,
      0 < P.tree.transition (currentState h) s →
        BankContinuationFeasibleAt P X (t + 1) (childHistory h s)
            (initial s ω) q ∧
          BankContinuationObjectiveWellDefinedAt P X (t + 1)
              (childHistory h s) q ∧
          bankContinuationPayoffAt P X (t + 1) (childHistory h s) q =
            bankValue (t + 1) (initial s ω) (childHistory h s) := by
    intro s ω
    by_cases hs : 0 < P.tree.transition (currentState h) s
    · have hinitialNonneg : 0 ≤ initial s ω := by
        exact hstatic.2.2.2.2.2.2 ω ω.property s hs
      rcases (hdynamic s hs).1 (initial s ω) hinitialNonneg with
        ⟨q, hqfeasible, hqdefined, hqvalue⟩
      exact ⟨q, fun _ ↦ ⟨hqfeasible, hqdefined, hqvalue⟩⟩
    · exact ⟨zeroPolicy, fun hs' ↦ (hs hs').elim⟩
  choose continuation hcontinuation using hexists
  let q := spliceBankContinuationPolicy currentEquity currentDividend
    currentRetained currentLoans currentReserves currentDeposits continuation
  have hcontinuationFeasible : ∀ s,
      0 < P.tree.transition (currentState h) s → ∀ ω : P.paymentSupport,
      BankContinuationFeasibleAt P X (t + 1) (childHistory h s)
        (bankDetailedPortfolioReturnAt P X t h (X.bankTightness t h)
            currentLoans currentReserves currentDeposits ω /
          X.inflation (t + 1) (childHistory h s))
        (continuation s ω) := by
    intro s hs ω
    have hq := (hcontinuation s ω hs).1
    have heq : bankDetailedPortfolioReturnAt P X t h (X.bankTightness t h)
          currentLoans currentReserves currentDeposits ω /
            X.inflation (t + 1) (childHistory h s) = initial s ω := by
      unfold initial bankRealPortfolioReturnAt
      rw [bankDetailedPortfolioReturn_eq_reduced P X t h
        (X.bankTightness t h) currentLoans currentReserves currentDeposits ω
        hreserveRate.ne']
    rwa [heq]
  have hqfeasible : BankContinuationFeasibleAt P X t h currentEquity q := by
    exact spliceBankContinuationPolicy_feasible P X t h currentEquity
      currentDividend currentRetained currentLoans currentReserves currentDeposits
      continuation hequity hdividend hretained hretention hreserveRate htightness
      hstatic hcontinuationFeasible
  have htailDefined : ∀ s,
      0 < P.tree.transition (currentState h) s → ∀ ω : P.paymentSupport,
      BankContinuationObjectiveWellDefinedAt P X (t + 1) (childHistory h s)
        (tailBankContinuationPolicy q s ω) := by
    intro s hs ω
    rw [show tailBankContinuationPolicy q s ω = continuation s ω by
      exact tail_spliceBankContinuationPolicy currentEquity currentDividend
        currentRetained currentLoans currentReserves currentDeposits continuation s ω]
    exact (hcontinuation s ω hs).2.1
  have hqdefined : BankContinuationObjectiveWellDefinedAt P X t h q :=
    bankContinuationObjectiveWellDefinedAt_of_tails P X t h q hchild htailDefined
  have hinitial : ∀ s, 0 < P.tree.transition (currentState h) s → ∀ ω,
      (continuation s ω).equity 0 (fun j ↦ Fin.elim0 j)
          (fun j ↦ Fin.elim0 j) = initial s ω := by
    intro s hs ω
    exact (hcontinuation s ω hs).1.1
  have hvalue : ∀ s, 0 < P.tree.transition (currentState h) s → ∀ ω,
      bankContinuationPayoffAt P X (t + 1) (childHistory h s)
          (continuation s ω) =
        bankValue (t + 1) (initial s ω) (childHistory h s) := by
    intro s hs ω
    exact (hcontinuation s ω hs).2.2
  refine ⟨q, hqfeasible, hqdefined, ?_⟩
  exact spliceBankContinuationPayoffAt_eq_dividend_add_bellman P X t h
    currentEquity currentDividend currentRetained currentLoans currentReserves
    currentDeposits continuation bankValue hconsumption hchild
    (fun s hs ω ↦ (hcontinuation s ω hs).2.1)
    (fun s hs ω ↦ by simpa [initial] using hinitial s hs ω)
    (fun s hs ω ↦ by simpa [initial] using hvalue s hs ω)

/-- Analytic data needed to derive the finite local Bellman problem from the
literal infinite-horizon continuation problem.  This deliberately contains
neither `BankValueHomogeneousAt` nor `BankBellmanLocalEnvironmentAt`: both are
conclusions of the scaling, splice and `tsum` arguments below. -/
def BankDynamicBellmanDataAt
    {S : Type*} [Fintype S] [DecidableEq S]
    (P : Primitives S) (X : Allocation S) (p : BankPlan S)
    (t : ℕ) (h : History S t) (bankValue : BankValueProcess S) : Prop :=
  ∃ candidate : BankContinuationPolicy S P.paymentSupport,
    BankContinuationStartsWithPlanAt p t h candidate ∧
    BankContinuationOptimalAt P X t h (p.equity t h) candidate ∧
    BankDynamicHomogeneityConditionsAt P X t h bankValue ∧
    bankContinuationPayoffAt P X t h candidate =
      bankValue t (p.equity t h) h ∧
    0 < P.bankExit ∧
    (∀ s, 0 < P.tree.transition (currentState h) s →
      0 ≤ bankValue (t + 1) 1 (childHistory h s)) ∧
    (∀ s, 0 < P.tree.transition (currentState h) s → ∀ ω,
      BankContinuationObjectiveWellDefinedAt P X (t + 1)
        (childHistory h s) (tailBankContinuationPolicy candidate s ω))

/-- Convert literal infinite-horizon continuation optimality into the local
Bellman environment used by the finite-payment KKT block.  The theorem does
not manufacture a value function: attained child values/dominance, supported
tail summability, positive exit, and nonnegative unit continuation values stay
as explicit analytic prerequisites. -/
theorem bankBellmanLocalEnvironmentAt_of_continuationOptimality
    {S : Type*} [Fintype S] [DecidableEq S]
    (P : Primitives S) (X : Allocation S) (p : BankPlan S)
    (t : ℕ) (h : History S t) (bankValue : BankValueProcess S)
    (candidate : BankContinuationPolicy S P.paymentSupport)
    (hstarts : BankContinuationStartsWithPlanAt p t h candidate)
    (hoptimal : BankContinuationOptimalAt P X t h (p.equity t h) candidate)
    (hdynamic : BankDynamicHomogeneityConditionsAt P X t h bankValue)
    (hcurrentValue : bankContinuationPayoffAt P X t h candidate =
      bankValue t (p.equity t h) h)
    (hretained : 0 < p.retainedEquity t h)
    (htightness : 0 < X.bankTightness t h)
    (hconsumption : 0 < X.workerConsumption t h)
    (hchild : ∀ s, 0 < P.tree.transition (currentState h) s →
      0 < X.workerConsumption (t + 1) (childHistory h s))
    (hinflation : ∀ s, 0 < P.tree.transition (currentState h) s →
      0 < X.inflation (t + 1) (childHistory h s))
    (hexit : 0 < P.bankExit)
    (hvalueNonneg : ∀ s, 0 < P.tree.transition (currentState h) s →
      0 ≤ bankValue (t + 1) 1 (childHistory h s))
    (htail : ∀ s, 0 < P.tree.transition (currentState h) s → ∀ ω,
      BankContinuationObjectiveWellDefinedAt P X (t + 1) (childHistory h s)
        (tailBankContinuationPolicy candidate s ω)) :
    BankBellmanLocalEnvironmentAt P X t h p (X.bankTightness t h)
      bankValue := by
  let emptyS : Fin 0 → S := fun j ↦ Fin.elim0 j
  let emptyΩ : Fin 0 → P.paymentSupport := fun j ↦ Fin.elim0 j
  rcases hoptimal with
    ⟨hcandidateFeasible, _hcandidateDefined, _hcandidateTerminal, hdominates⟩
  have hstartsFields := hstarts
  rcases hstartsFields with ⟨hequityStart, hdividendStart, hretainedStart,
    hloansStart, hreservesStart, hdepositsStart⟩
  have hzero := hcandidateFeasible.2 0 emptyS emptyΩ (by trivial)
  have hdividend : 0 ≤ p.dividend t h := by
    simpa [emptyS, emptyΩ, hdividendStart] using hzero.2.1
  have hretention : p.retainedEquity t h = p.equity t h - p.dividend t h := by
    simpa [emptyS, emptyΩ, hequityStart, hdividendStart, hretainedStart] using
      hzero.2.2.2.2.2.2.2.2.1
  have hequity : 0 < p.equity t h := by
    nlinarith
  have hreserveRate : 0 < X.reserveRate t h := by
    simpa [emptyS, continuationHistory_zero] using
      hzero.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hstatic := continuationCandidate_staticFeasibleAt P X p t h candidate
    hcandidateFeasible hstarts
  have htailUpper : ∀ s, 0 < P.tree.transition (currentState h) s → ∀ ω,
      bankContinuationPayoffAt P X (t + 1) (childHistory h s)
          (tailBankContinuationPolicy candidate s ω) ≤
        bankValue (t + 1)
          (candidate.equity 1 (fun _ ↦ s) (fun _ ↦ ω))
          (childHistory h s) := by
    intro s hs ω
    exact (hdynamic s hs).2 _ _
      (tailBankContinuationPolicy_feasible P X t h (p.equity t h) candidate
        hcandidateFeasible s hs ω)
      (htail s hs ω)
  have hcandidateLe := bankContinuationPayoffAt_le_dividend_add_bellman
    P X p t h bankValue candidate hcandidateFeasible hstarts hconsumption hchild
      htail htailUpper
  obtain ⟨q, hqfeasible, hqdefined, hqpayoff⟩ :=
    exists_feasible_splice_attaining_dynamicValue P X t h
      (p.equity t h) (p.dividend t h) (p.retainedEquity t h)
      (p.loans t h) (p.reservesPre t h) (p.deposits t h) bankValue
      hdynamic hequity hdividend hretained hretention hreserveRate htightness
      hstatic hconsumption hchild
  have hqLe := hdominates q hqfeasible hqdefined
  rw [hqpayoff] at hqLe
  have hcandidateBellman : bankContinuationPayoffAt P X t h candidate =
      p.dividend t h + bankBellmanContinuationAt P X t h
        (bankOTCDeficitSlopeAt P X t h (X.bankTightness t h))
        (bankOTCSurplusSlopeAt P X t h (X.bankTightness t h))
        (p.loans t h) (p.reservesPre t h) (p.deposits t h)
        (bankValue (t + 1)) :=
    le_antisymm hcandidateLe hqLe
  have hbellmanValue : bankValue t (p.equity t h) h =
      p.dividend t h + bankBellmanContinuationAt P X t h
        (bankOTCDeficitSlopeAt P X t h (X.bankTightness t h))
        (bankOTCSurplusSlopeAt P X t h (X.bankTightness t h))
        (p.loans t h) (p.reservesPre t h) (p.deposits t h)
        (bankValue (t + 1)) := by
    rw [← hcurrentValue]
    exact hcandidateBellman
  have hdeviation : ∀ loans reserves deposits,
      BankStaticPortfolioFeasibleAt P X t h
        (bankOTCDeficitSlopeAt P X t h (X.bankTightness t h))
        (bankOTCSurplusSlopeAt P X t h (X.bankTightness t h))
        (p.retainedEquity t h) loans reserves deposits →
      p.dividend t h + bankBellmanContinuationAt P X t h
        (bankOTCDeficitSlopeAt P X t h (X.bankTightness t h))
        (bankOTCSurplusSlopeAt P X t h (X.bankTightness t h))
        loans reserves deposits (bankValue (t + 1)) ≤
          bankValue t (p.equity t h) h := by
    intro loans reserves deposits hfeasible
    obtain ⟨alternative, halternativeFeasible, halternativeDefined,
      halternativePayoff⟩ :=
      exists_feasible_splice_attaining_dynamicValue P X t h
        (p.equity t h) (p.dividend t h) (p.retainedEquity t h)
        loans reserves deposits bankValue hdynamic hequity hdividend hretained
        hretention hreserveRate htightness hfeasible hconsumption hchild
    have halternativeLe := hdominates alternative halternativeFeasible
      halternativeDefined
    calc
      _ = bankContinuationPayoffAt P X t h alternative := halternativePayoff.symm
      _ ≤ bankContinuationPayoffAt P X t h candidate := halternativeLe
      _ = bankValue t (p.equity t h) h := hcurrentValue
  have hweight := bankBellmanContinuationWeightAt_pos_of_finiteValue
    P X t h bankValue hconsumption hchild hinflation hexit hvalueNonneg
  refine ⟨hconsumption, hchild, ?_, hdividend, hretention, hstatic,
    hbellmanValue, hdeviation, hweight⟩
  intro s hs
  exact bankStochasticDiscountAt_pos_of_consumption P X t h s hconsumption
    (hchild s hs)

/-- Under feasible real solvency and degree-one continuation value, the
literal Bellman continuation is the source's common positive continuation
weight times the reduced static portfolio payoff.  The zero-return case is
not discarded: homogeneity at zero implies that the continuation value at
zero is zero on every successor with positive transition probability. -/
theorem bankBellmanContinuation_eq_weight_mul_payoff
    (P : Primitives S) (X : Allocation S) (t : ℕ) (h : History S t)
    (deficitSlope surplusSlope retainedEquity loans reserves deposits : ℝ)
    (bankValue : BankValueProcess S)
    (hhomogeneous : BankValueHomogeneousAt P t h bankValue)
    (hfeasible : BankStaticPortfolioFeasibleAt P X t h deficitSlope surplusSlope
      retainedEquity loans reserves deposits) :
    bankBellmanContinuationAt P X t h deficitSlope surplusSlope
        loans reserves deposits (bankValue (t + 1)) =
      bankBellmanContinuationWeightAt P X t h (bankValue (t + 1)) *
        bankStaticPortfolioPayoffAt P X t h deficitSlope surplusSlope
          loans reserves deposits := by
  rcases hfeasible with ⟨_, _, _, _, _, _, hsolvent⟩
  have hinner : ∀ ω ∈ P.paymentSupport,
      (∑ s, P.tree.transition (currentState h) s *
        bankStochasticDiscountAt P X t h s *
          ((1 - P.bankExit) * bankValue (t + 1)
              (bankRealPortfolioReturnAt P X t h deficitSlope surplusSlope
                loans reserves deposits ω s) (childHistory h s) +
            P.bankExit * bankRealPortfolioReturnAt P X t h deficitSlope
              surplusSlope loans reserves deposits ω s)) =
        bankBellmanContinuationWeightAt P X t h (bankValue (t + 1)) *
          bankReducedPortfolioReturn P X t h deficitSlope surplusSlope
            loans reserves deposits ω := by
    intro ω hω
    unfold bankBellmanContinuationWeightAt
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro s _
    have htransition : 0 ≤ P.tree.transition (currentState h) s :=
      P.tree.transition_nonneg _ _
    by_cases hzero : P.tree.transition (currentState h) s = 0
    · simp [hzero]
    · have hpositive : 0 < P.tree.transition (currentState h) s :=
        lt_of_le_of_ne htransition (Ne.symm hzero)
      have hreturn : 0 ≤ bankRealPortfolioReturnAt P X t h deficitSlope
          surplusSlope loans reserves deposits ω s := hsolvent ω hω s hpositive
      have hvalue : bankValue (t + 1)
          (bankRealPortfolioReturnAt P X t h deficitSlope surplusSlope
            loans reserves deposits ω s) (childHistory h s) =
          bankRealPortfolioReturnAt P X t h deficitSlope surplusSlope
            loans reserves deposits ω s *
              bankValue (t + 1) 1 (childHistory h s) := by
        by_cases hreturnZero : bankRealPortfolioReturnAt P X t h deficitSlope
            surplusSlope loans reserves deposits ω s = 0
        · have hvalueZero := hhomogeneous 2 0 s (by norm_num) (by norm_num)
            hpositive
          simp only [mul_zero] at hvalueZero
          rw [hreturnZero]
          nlinarith
        · have hreturnPositive : 0 < bankRealPortfolioReturnAt P X t h
              deficitSlope surplusSlope loans reserves deposits ω s :=
            lt_of_le_of_ne hreturn (Ne.symm hreturnZero)
          simpa using hhomogeneous
            (bankRealPortfolioReturnAt P X t h deficitSlope surplusSlope
              loans reserves deposits ω s) 1 s hreturnPositive (by norm_num)
              hpositive
      rw [hvalue]
      unfold bankRealPortfolioReturnAt
      ring
  unfold bankBellmanContinuationAt
  calc
    _ = ∑ ω ∈ P.paymentSupport, P.paymentProbability ω *
          (bankBellmanContinuationWeightAt P X t h (bankValue (t + 1)) *
            bankReducedPortfolioReturn P X t h deficitSlope surplusSlope
              loans reserves deposits ω) := by
        apply Finset.sum_congr rfl
        intro ω hω
        rw [hinner ω hω]
    _ = bankBellmanContinuationWeightAt P X t h (bankValue (t + 1)) *
          bankStaticPortfolioPayoffAt P X t h deficitSlope surplusSlope
            loans reserves deposits := by
        unfold bankStaticPortfolioPayoffAt finiteSupportExpectation
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro ω _
        ring

/-- The literal Bellman inequality reduces to the static
portfolio comparison after degree-one homogeneity, payment/continuation
independence, and division by the positive common continuation weight. -/
theorem bankStaticPortfolioOptimal_of_bellman
    (P : Primitives S) (X : Allocation S) (p : BankPlan S)
    (t : ℕ) (h : History S t) (tightness : ℝ)
    (bankValue : BankValueProcess S)
    (hhomogeneous : BankValueHomogeneousAt P t h bankValue)
    (henvironment : BankBellmanLocalEnvironmentAt P X t h p tightness bankValue) :
    BankStaticPortfolioOptimalAt P X t h
      (bankOTCDeficitSlopeAt P X t h tightness)
      (bankOTCSurplusSlopeAt P X t h tightness)
      (p.retainedEquity t h) (p.loans t h) (p.reservesPre t h)
      (p.deposits t h) := by
  intro loans reserves deposits hfeasible
  rcases henvironment with ⟨_, _, _, _, _, hcandidateFeasible, hcandidateBellman,
    hdeviationBellman, hweight⟩
  have hdeviation := hdeviationBellman loans reserves deposits hfeasible
  rw [hcandidateBellman] at hdeviation
  rw [bankBellmanContinuation_eq_weight_mul_payoff P X t h
      (bankOTCDeficitSlopeAt P X t h tightness)
      (bankOTCSurplusSlopeAt P X t h tightness) (p.retainedEquity t h)
      loans reserves deposits bankValue hhomogeneous hfeasible] at hdeviation
  rw [bankBellmanContinuation_eq_weight_mul_payoff P X t h
      (bankOTCDeficitSlopeAt P X t h tightness)
      (bankOTCSurplusSlopeAt P X t h tightness) (p.retainedEquity t h)
      (p.loans t h) (p.reservesPre t h) (p.deposits t h) bankValue
      hhomogeneous hcandidateFeasible] at hdeviation
  nlinarith

/-- Source Bellman optimality over the recurrent tree.  Renewal/seed transfers
are intentionally absent: they remain in `BankRenewalFlows`, after the bank's
pre-exit return and exit decision. -/
def BankOptimalWithValue (P : Primitives S) (I : InheritedState)
    (X : Allocation S) (p : BankPlan S) (bankValue : BankValueProcess S) : Prop :=
  BankFeasible P I X p ∧
  ∀ t h, FirmHistoryAdmissible P t h →
    BankValueHomogeneousAt P t h bankValue ∧
    BankBellmanLocalEnvironmentAt P X t h p (X.bankTightness t h) bankValue ∧
    ∃ candidate : BankContinuationPolicy S P.paymentSupport,
      BankContinuationStartsWithPlanAt p t h candidate ∧
      BankContinuationOptimalAt P X t h (p.equity t h) candidate ∧
      bankContinuationPayoffAt P X t h candidate = bankValue t (p.equity t h) h

def BankOptimal (P : Primitives S) (I : InheritedState) (X : Allocation S) : Prop :=
  ∃ (p : BankPlan S) (bankValue : BankValueProcess S),
    BankOptimalWithValue P I X p bankValue

/-- A finite population of bank types.  Each type has its own nominal initial
face, payment law, per-bank plan and dynamic value; prices, aggregate shocks
and policy instruments remain common. -/
structure BankPopulationCandidate (S J : Type*) where
  mass : J → ℝ
  initialFace : J → ℝ
  paymentLaw : J → BankPaymentLaw
  plan : J → BankPlan S
  value : J → BankValueProcess S

/-- The one ex-ante bank type of the frozen finite-law construction.  Its
mass and inherited nominal face aggregate exactly; individual payment-history
equity is still generated by the continuation policy, not identified with an
aggregate realized payment path. -/
noncomputable def massOneFullRetentionBankPopulation
    (P : Primitives S) (I : InheritedState) (X : Allocation S)
    (bankValue : BankValueProcess S) : BankPopulationCandidate S (Fin 1) where
  mass := fun _ ↦ 1
  initialFace := fun _ ↦ I.bankFace
  paymentLaw := fun _ ↦ P.primitiveBankPaymentLaw
  plan := fun _ ↦ fullRetentionCommonBankPlan P X
  value := fun _ ↦ bankValue

theorem massOneFullRetentionBankPopulation_initialFace
    (P : Primitives S) (I : InheritedState) (X : Allocation S)
    (bankValue : BankValueProcess S) :
    ∑ j, (massOneFullRetentionBankPopulation P I X bankValue).mass j *
      (massOneFullRetentionBankPopulation P I X bankValue).initialFace j =
        I.bankFace := by
  simp [massOneFullRetentionBankPopulation]

/-- The six aggregate plan identities reduce to literal field equalities for
the mass-one common plan.  Zero dividends and full retention are displayed as
the two economic premises rather than hidden in the candidate record. -/
theorem massOneFullRetentionBankPopulation_aggregates
    (P : Primitives S) (I : InheritedState) (X : Allocation S)
    (bankValue : BankValueProcess S) (t : ℕ) (h : History S t)
    (hdividend : X.bankDividend t h = 0)
    (hretained : X.bankRetainedEquity t h = X.bankEquity t h) :
    X.bankEquity t h =
        ∑ j, (massOneFullRetentionBankPopulation P I X bankValue).mass j *
          ((massOneFullRetentionBankPopulation P I X bankValue).plan j).equity t h ∧
    X.bankDividend t h =
        ∑ j, (massOneFullRetentionBankPopulation P I X bankValue).mass j *
          ((massOneFullRetentionBankPopulation P I X bankValue).plan j).dividend t h ∧
    X.bankRetainedEquity t h =
        ∑ j, (massOneFullRetentionBankPopulation P I X bankValue).mass j *
          ((massOneFullRetentionBankPopulation P I X bankValue).plan j).retainedEquity t h ∧
    X.bankLoans t h =
        ∑ j, (massOneFullRetentionBankPopulation P I X bankValue).mass j *
          ((massOneFullRetentionBankPopulation P I X bankValue).plan j).loans t h ∧
    X.reservesPrePayment t h =
        ∑ j, (massOneFullRetentionBankPopulation P I X bankValue).mass j *
          ((massOneFullRetentionBankPopulation P I X bankValue).plan j).reservesPre t h ∧
    X.bankDeposits t h =
        ∑ j, (massOneFullRetentionBankPopulation P I X bankValue).mass j *
          ((massOneFullRetentionBankPopulation P I X bankValue).plan j).deposits t h := by
  simp [massOneFullRetentionBankPopulation, fullRetentionCommonBankPlan,
    hdividend, hretained]

/-- Type-by-type dynamic data for the finite bank population at one history.
It is intentionally separate from `BankPopulationEquilibriumFor`: the latter's
legacy local Bellman fields cannot serve as a proof of the dynamic-to-local
implication. -/
def BankPopulationDynamicBellmanDataAt {J : Type*}
    [Fintype J] [DecidableEq J]
    (P : Primitives S) (X : Allocation S) (B : BankPopulationCandidate S J)
    (t : ℕ) (h : History S t) : Prop :=
  ∀ j, BankDynamicBellmanDataAt
    (P.withBankPaymentLaw (B.paymentLaw j)) X (B.plan j) t h (B.value j)

noncomputable def bankPopulationExpectedFacilityAt {J : Type*} [Fintype J]
    (B : BankPopulationCandidate S J) (t : ℕ) (h : History S t) : ℝ :=
  ∑ j, B.mass j * finiteSupportExpectation (B.paymentLaw j).support
    (B.paymentLaw j).probability (fun ω ↦ (B.plan j).facility ω t h)

noncomputable def bankPopulationExpectedPostReservesAt {J : Type*} [Fintype J]
    (B : BankPopulationCandidate S J) (t : ℕ) (h : History S t) : ℝ :=
  ∑ j, B.mass j * finiteSupportExpectation (B.paymentLaw j).support
    (B.paymentLaw j).probability (fun ω ↦ (B.plan j).reservesPost ω t h)

noncomputable def bankPopulationExpectedInterbankAt {J : Type*} [Fintype J]
    (B : BankPopulationCandidate S J) (t : ℕ) (h : History S t) : ℝ :=
  ∑ j, B.mass j * finiteSupportExpectation (B.paymentLaw j).support
    (B.paymentLaw j).probability (fun ω ↦ (B.plan j).interbank ω t h)

noncomputable def bankPopulationExpectedGrossReturnAt {J : Type*} [Fintype J]
    (P : Primitives S) (X : Allocation S) (B : BankPopulationCandidate S J)
    (t : ℕ) (h : History S t) : ℝ :=
  ∑ j, B.mass j * expectedBankGrossReturn
    (P.withBankPaymentLaw (B.paymentLaw j)) X (B.plan j) t h

/-- Mean-zero payment shocks imply that gross deposit repayment aggregates to
the promised deposit face for each bank type. -/
theorem bankPaymentLaw_expectedDepositRepayment
    (L : BankPaymentLaw) (deposits : ℝ) :
    finiteSupportExpectation L.support L.probability
        (fun ω ↦ deposits * (1 + L.shock ω)) = deposits := by
  unfold finiteSupportExpectation
  calc
    (∑ ω ∈ L.support, L.probability ω * (deposits * (1 + L.shock ω))) =
        deposits * (∑ ω ∈ L.support, L.probability ω) +
          deposits * (∑ ω ∈ L.support, L.probability ω * L.shock ω) := by
            rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
            apply Finset.sum_congr rfl
            intro ω _
            ring
    _ = deposits := by rw [L.probability_sum_one, L.shock_mean_zero]; ring

/-- Expanding one type's expected nominal bank return leaves exactly the five
source components: loans, post-payment reserves, promised deposits, OTC and
the standing facility. -/
theorem expectedBankGrossReturn_eq_components
    (P : Primitives S) (X : Allocation S) (L : BankPaymentLaw) (p : BankPlan S)
    (t : ℕ) (h : History S t) :
    expectedBankGrossReturn (P.withBankPaymentLaw L) X p t h =
      X.loanRate t h * p.loans t h +
      X.reserveRate t h * finiteSupportExpectation L.support L.probability
        (fun ω ↦ p.reservesPost ω t h) -
      X.depositRate t h * p.deposits t h -
      X.interbankRate t h * finiteSupportExpectation L.support L.probability
        (fun ω ↦ p.interbank ω t h) -
      X.facilityRate t h * finiteSupportExpectation L.support L.probability
        (fun ω ↦ p.facility ω t h) := by
  let loanPart := fun _ω : BankPayment ↦ X.loanRate t h * p.loans t h
  let reservePart := fun ω : BankPayment ↦ X.reserveRate t h * p.reservesPost ω t h
  let depositPart := fun ω : BankPayment ↦
    X.depositRate t h * p.deposits t h * (1 + L.shock ω)
  let interbankPart := fun ω : BankPayment ↦ X.interbankRate t h * p.interbank ω t h
  let facilityPart := fun ω : BankPayment ↦ X.facilityRate t h * p.facility ω t h
  unfold expectedBankGrossReturn bankGrossReturn
  simp only [Primitives.withBankPaymentLaw]
  change finiteSupportExpectation L.support L.probability
      (fun ω ↦ loanPart ω + reservePart ω - depositPart ω -
        interbankPart ω - facilityPart ω) = _
  rw [finiteSupportExpectation_sub, finiteSupportExpectation_sub,
    finiteSupportExpectation_sub, finiteSupportExpectation_add]
  have hloan : finiteSupportExpectation L.support L.probability loanPart =
      X.loanRate t h * p.loans t h := by
    unfold loanPart finiteSupportExpectation
    rw [← Finset.sum_mul, L.probability_sum_one]
    ring
  have hreserve : finiteSupportExpectation L.support L.probability reservePart =
      X.reserveRate t h * finiteSupportExpectation L.support L.probability
        (fun ω ↦ p.reservesPost ω t h) := by
    exact finiteSupportExpectation_const_mul L.support L.probability
      (X.reserveRate t h) (fun ω ↦ p.reservesPost ω t h)
  have hdeposit : finiteSupportExpectation L.support L.probability depositPart =
      X.depositRate t h * p.deposits t h := by
    unfold depositPart
    rw [finiteSupportExpectation_const_mul]
    have hone : finiteSupportExpectation L.support L.probability
        (fun ω ↦ 1 + L.shock ω) = 1 := by
      simpa using bankPaymentLaw_expectedDepositRepayment L 1
    rw [hone]
    ring
  have hinterbank : finiteSupportExpectation L.support L.probability interbankPart =
      X.interbankRate t h * finiteSupportExpectation L.support L.probability
        (fun ω ↦ p.interbank ω t h) := by
    exact finiteSupportExpectation_const_mul L.support L.probability
      (X.interbankRate t h) (fun ω ↦ p.interbank ω t h)
  have hfacility : finiteSupportExpectation L.support L.probability facilityPart =
      X.facilityRate t h * finiteSupportExpectation L.support L.probability
        (fun ω ↦ p.facility ω t h) := by
    exact finiteSupportExpectation_const_mul L.support L.probability
      (X.facilityRate t h) (fun ω ↦ p.facility ω t h)
  rw [hloan, hreserve, hdeposit, hinterbank, hfacility]

/-- One type's pre-exit real equity, before the source renewal/seed split. -/
noncomputable def bankTypePreExitEquity (P : Primitives S)
    (I : InheritedState) (X : Allocation S) (p : BankPlan S) : AdaptedProcess S
  | 0, h => I.bankFace / (bankRenewalFactor P * X.inflation 0 h)
  | t + 1, h =>
      expectedBankGrossReturn P X p t (previousHistory h) / X.inflation (t + 1) h

/-- Renewal is imposed separately for every bank type, as in source equation
`E_{j,t+1}=a_B E^{ret}_{j,t+1}`. -/
def BankTypeRenewalFlows (P : Primitives S) (I : InheritedState)
    (X : Allocation S) (p : BankPlan S) : Prop :=
  ∀ t h, FirmHistoryAdmissible P t h →
    p.equity t h = bankRenewalFactor P * bankTypePreExitEquity P I X p t h

noncomputable def bankTypeOwnerIncome (P : Primitives S) (I : InheritedState)
    (X : Allocation S) (p : BankPlan S) (t : ℕ) (h : History S t) : ℝ :=
  p.dividend t h + P.bankExit * (1 - P.bankSeedShare) *
    bankTypePreExitEquity P I X p t h

/-- Settlement when no bank supplies a reserve deficit: there is no OTC loan
and no facility use. -/
def BankNoDeficitSettlementAt (P : Primitives S) (X : Allocation S)
    (p : BankPlan S) (t : ℕ) (h : History S t) : Prop :=
  ∀ ω, ω ∈ P.paymentSupport →
    p.interbank ω t h = 0 ∧ p.facility ω t h = 0 ∧
    p.reservesPost ω t h = p.reservesPre t h +
      (X.depositRate t h / X.reserveRate t h) * P.paymentShock ω *
        p.deposits t h

/-- Settlement when no bank supplies reserves OTC: deficit banks use the
facility for their entire shortfall, while zero-surplus banks do nothing. -/
def BankNoSurplusSettlementAt (P : Primitives S) (X : Allocation S)
    (p : BankPlan S) (t : ℕ) (h : History S t) : Prop :=
  ∀ ω, ω ∈ P.paymentSupport →
    let surplus := bankSettlementSurplus (p.reservesPre t h)
      (P.reserveRequirementPath t h) (X.depositRate t h / X.reserveRate t h)
      (p.deposits t h) (P.paymentShock ω)
    p.interbank ω t h = 0 ∧ p.facility ω t h = max (-surplus) 0 ∧
    p.reservesPost ω t h = p.reservesPre t h +
      (X.depositRate t h / X.reserveRate t h) * P.paymentShock ω *
        p.deposits t h + p.facility ω t h

/-- Complete OTC regime disjunction at one aggregate history.  The active
bilateral branch uses matching and negotiated pricing; the two corner branches
retain the source's no-trade and full-facility settlements without inventing a
positive tightness or an untraded interbank price. -/
def BankPopulationOTCRegimeAt {J : Type*} [Fintype J] [DecidableEq J]
    (P : Primitives S) (X : Allocation S) (B : BankPopulationCandidate S J)
    (t : ℕ) (h : History S t) : Prop :=
  let deficitSupply := bankDeficitSupplyAt P X t h B.mass
    (fun j ↦ (B.plan j).reservesPre t h)
    (fun j ↦ (B.plan j).deposits t h)
    (fun j ↦ (B.paymentLaw j).support)
    (fun j ↦ (B.paymentLaw j).probability)
    (fun j ↦ (B.paymentLaw j).shock)
  let surplusSupply := bankSurplusSupplyAt P X t h B.mass
    (fun j ↦ (B.plan j).reservesPre t h)
    (fun j ↦ (B.plan j).deposits t h)
    (fun j ↦ (B.paymentLaw j).support)
    (fun j ↦ (B.paymentLaw j).probability)
    (fun j ↦ (B.paymentLaw j).shock)
  (BilateralOTCActivity deficitSupply surplusSupply (X.bankTightness t h) ∧
    (∀ j, BankCandidateOTCFlowsAt
      (P.withBankPaymentLaw (B.paymentLaw j)) X (B.plan j) t h
        (X.bankTightness t h)) ∧
    X.interbankRate t h =
      otcNegotiatedRate (X.reserveRate t h) (X.facilityRate t h)
        P.matchingIntensity (X.bankTightness t h)) ∨
  (deficitSupply = 0 ∧ ∀ j, BankNoDeficitSettlementAt
    (P.withBankPaymentLaw (B.paymentLaw j)) X (B.plan j) t h) ∨
  (surplusSupply = 0 ∧ ∀ j, BankNoSurplusSettlementAt
    (P.withBankPaymentLaw (B.paymentLaw j)) X (B.plan j) t h)

/-- Positive aggregate deficit and surplus supplies eliminate both no-trade
corners of the exhaustive OTC settlement regime. -/
theorem bankPopulationOTCRegimeAt_bilateral
    {J : Type*} [Fintype J] [DecidableEq J]
    (P : Primitives S) (X : Allocation S) (B : BankPopulationCandidate S J)
    (t : ℕ) (h : History S t)
    (H : BankPopulationOTCRegimeAt P X B t h)
    (hdeficit : 0 < bankDeficitSupplyAt P X t h B.mass
      (fun j ↦ (B.plan j).reservesPre t h)
      (fun j ↦ (B.plan j).deposits t h)
      (fun j ↦ (B.paymentLaw j).support)
      (fun j ↦ (B.paymentLaw j).probability)
      (fun j ↦ (B.paymentLaw j).shock))
    (hsurplus : 0 < bankSurplusSupplyAt P X t h B.mass
      (fun j ↦ (B.plan j).reservesPre t h)
      (fun j ↦ (B.plan j).deposits t h)
      (fun j ↦ (B.paymentLaw j).support)
      (fun j ↦ (B.paymentLaw j).probability)
      (fun j ↦ (B.paymentLaw j).shock)) :
    BilateralOTCActivity
      (bankDeficitSupplyAt P X t h B.mass
        (fun j ↦ (B.plan j).reservesPre t h)
        (fun j ↦ (B.plan j).deposits t h)
        (fun j ↦ (B.paymentLaw j).support)
        (fun j ↦ (B.paymentLaw j).probability)
        (fun j ↦ (B.paymentLaw j).shock))
      (bankSurplusSupplyAt P X t h B.mass
        (fun j ↦ (B.plan j).reservesPre t h)
        (fun j ↦ (B.plan j).deposits t h)
        (fun j ↦ (B.paymentLaw j).support)
        (fun j ↦ (B.paymentLaw j).probability)
        (fun j ↦ (B.paymentLaw j).shock)) (X.bankTightness t h) ∧
    (∀ j, BankCandidateOTCFlowsAt
      (P.withBankPaymentLaw (B.paymentLaw j)) X (B.plan j) t h
        (X.bankTightness t h)) ∧
    X.interbankRate t h = otcNegotiatedRate (X.reserveRate t h)
      (X.facilityRate t h) P.matchingIntensity (X.bankTightness t h) := by
  rcases H with hactive | hnoDeficit | hnoSurplus
  · exact hactive
  · exact (ne_of_gt hdeficit hnoDeficit.1).elim
  · exact (ne_of_gt hsurplus hnoSurplus.1).elim

/-- Population OTC positions cancel in every source settlement regime.  In the
active branch this is bilateral clearing; in either no-trade corner every
individual interbank position is zero. -/
theorem bankPopulationExpectedInterbankAt_eq_zero_of_otcRegime
    {J : Type*} [Fintype J] [DecidableEq J]
    (P : Primitives S) (X : Allocation S) (B : BankPopulationCandidate S J)
    (t : ℕ) (h : History S t) (H : BankPopulationOTCRegimeAt P X B t h) :
    bankPopulationExpectedInterbankAt B t h = 0 := by
  classical
  dsimp only [BankPopulationOTCRegimeAt] at H
  rcases H with hactive | hnodeficit | hnosurplus
  · rcases hactive with ⟨hactivity, hflows, _hrate⟩
    have hclears := bankTypeSettlementClearsAt_of_bilateral P X t h B.mass
      (fun j ↦ (B.plan j).reservesPre t h) (fun j ↦ (B.plan j).deposits t h)
      (fun j ↦ (B.paymentLaw j).support)
      (fun j ↦ (B.paymentLaw j).probability) (fun j ↦ (B.paymentLaw j).shock)
      (X.bankTightness t h) hactivity
    unfold bankPopulationExpectedInterbankAt
    calc
      (∑ j, B.mass j * finiteSupportExpectation (B.paymentLaw j).support
          (B.paymentLaw j).probability (fun ω ↦ (B.plan j).interbank ω t h)) =
          ∑ j, B.mass j * finiteSupportExpectation (B.paymentLaw j).support
            (B.paymentLaw j).probability (fun ω ↦
              bankTypeOTCInterbankAt P (X.bankTightness t h)
                (bankSettlementSurplus ((B.plan j).reservesPre t h)
                  (P.reserveRequirementPath t h)
                  (X.depositRate t h / X.reserveRate t h)
                  ((B.plan j).deposits t h) ((B.paymentLaw j).shock ω))) := by
            apply Finset.sum_congr rfl
            intro j _
            congr 1
            unfold finiteSupportExpectation
            apply Finset.sum_congr rfl
            intro ω hω
            change (B.paymentLaw j).probability ω * (B.plan j).interbank ω t h = _
            rw [(hflows j ω hω).1]
            simp only [bankOTCInterbankAt, bankTypeOTCInterbankAt,
              Primitives.withBankPaymentLaw]
      _ = 0 := hclears
  · rcases hnodeficit with ⟨_hzero, hsettlement⟩
    unfold bankPopulationExpectedInterbankAt finiteSupportExpectation
    apply Finset.sum_eq_zero
    intro j _
    apply mul_eq_zero_of_right
    apply Finset.sum_eq_zero
    intro ω hω
    change (B.paymentLaw j).probability ω * (B.plan j).interbank ω t h = 0
    rw [(hsettlement j ω hω).1]
    ring
  · rcases hnosurplus with ⟨_hzero, hsettlement⟩
    unfold bankPopulationExpectedInterbankAt finiteSupportExpectation
    apply Finset.sum_eq_zero
    intro j _
    apply mul_eq_zero_of_right
    apply Finset.sum_eq_zero
    intro ω hω
    change (B.paymentLaw j).probability ω * (B.plan j).interbank ω t h = 0
    rw [(hsettlement j ω hω).1]
    ring

/-- Every branch of the source OTC regime satisfies the same bank-level
post-payment reserve identity; only the formulas selecting OTC and facility
quantities differ across branches. -/
theorem bankPlanSettlementIdentity_of_otcRegime
    {J : Type*} [Fintype J] [DecidableEq J]
    (P : Primitives S) (X : Allocation S) (B : BankPopulationCandidate S J)
    (t : ℕ) (h : History S t) (H : BankPopulationOTCRegimeAt P X B t h) :
    ∀ j ω, ω ∈ (B.paymentLaw j).support →
      (B.plan j).reservesPost ω t h = (B.plan j).reservesPre t h +
        (X.depositRate t h / X.reserveRate t h) * (B.paymentLaw j).shock ω *
          (B.plan j).deposits t h +
        (B.plan j).interbank ω t h + (B.plan j).facility ω t h := by
  classical
  dsimp only [BankPopulationOTCRegimeAt] at H
  rcases H with hactive | hnodeficit | hnosurplus
  · rcases hactive with ⟨_hactivity, hflows, _hrate⟩
    intro j ω hω
    rcases hflows j ω hω with ⟨hinterbank, hfacility, hpost⟩
    rw [hinterbank, hfacility, hpost]
    simp only [bankPostSettlementReservesAt, Primitives.withBankPaymentLaw]
  · rcases hnodeficit with ⟨_hzero, hsettlement⟩
    intro j ω hω
    rcases hsettlement j ω hω with ⟨hinterbank, hfacility, hpost⟩
    rw [hinterbank, hfacility, hpost]
    simp only [Primitives.withBankPaymentLaw]
    ring
  · rcases hnosurplus with ⟨_hzero, hsettlement⟩
    intro j ω hω
    rcases hsettlement j ω hω with ⟨hinterbank, _hfacility, hpost⟩
    rw [hinterbank, hpost]
    simp only [Primitives.withBankPaymentLaw]
    ring

/-- Facility nonnegativity follows from the regime formulas and matching
fractions; it is not taken from the bank feasibility record. -/
theorem bankPlanFacility_nonneg_of_otcRegime
    {J : Type*} [Fintype J] [DecidableEq J]
    (P : Primitives S) (X : Allocation S) (B : BankPopulationCandidate S J)
    (t : ℕ) (h : History S t) (H : BankPopulationOTCRegimeAt P X B t h) :
    ∀ j ω, ω ∈ (B.paymentLaw j).support →
      0 ≤ (B.plan j).facility ω t h := by
  classical
  dsimp only [BankPopulationOTCRegimeAt] at H
  rcases H with hactive | hnodeficit | hnosurplus
  · rcases hactive with ⟨hactivity, hflows, _hrate⟩
    have htightness : 0 < X.bankTightness t h := by
      rcases hactivity with ⟨hdeficit, hsurplus, htightnessEq⟩
      rw [htightnessEq]
      exact div_pos hdeficit hsurplus
    intro j ω hω
    rw [(hflows j ω hω).2.1]
    exact bankFacilityBorrowingAt_nonneg
      (P.withBankPaymentLaw (B.paymentLaw j)) X t h (X.bankTightness t h)
      ((B.plan j).reservesPre t h) ((B.plan j).deposits t h) htightness ω
  · rcases hnodeficit with ⟨_hzero, hsettlement⟩
    intro j ω hω
    rw [(hsettlement j ω hω).2.1]
  · rcases hnosurplus with ⟨_hzero, hsettlement⟩
    intro j ω hω
    rw [(hsettlement j ω hω).2.1]
    exact le_max_right _ _

/-- Type-by-type bank optimality, matching quantities, aggregation and OTC
clearing for the recurrent economy.  This removes the former gap in which an
unrelated single bank could witness `BankOptimal` while aggregate portfolios
in `X` were left uncontrolled. -/
def BankPopulationEquilibriumFor {J : Type*} [Fintype J] [DecidableEq J]
    (P : Primitives S) (I : InheritedState) (X : Allocation S)
    (B : BankPopulationCandidate S J) : Prop :=
  (∀ j, 0 < B.mass j ∧ 0 < B.initialFace j) ∧
  (∑ j, B.mass j * B.initialFace j = I.bankFace) ∧
  (∀ j, BankOptimalWithValue
    (P.withBankPaymentLaw (B.paymentLaw j))
    (I.withBankFace (B.initialFace j)) X (B.plan j) (B.value j)) ∧
  (∀ j, BankTypeRenewalFlows
    (P.withBankPaymentLaw (B.paymentLaw j))
    (I.withBankFace (B.initialFace j)) X (B.plan j)) ∧
  (∀ t h, FirmHistoryAdmissible P t h →
    X.bankEquity t h = ∑ j, B.mass j * (B.plan j).equity t h ∧
    X.bankDividend t h = ∑ j, B.mass j * (B.plan j).dividend t h ∧
    X.bankRetainedEquity t h =
      ∑ j, B.mass j * (B.plan j).retainedEquity t h ∧
    X.bankLoans t h = ∑ j, B.mass j * (B.plan j).loans t h ∧
    X.reservesPrePayment t h =
      ∑ j, B.mass j * (B.plan j).reservesPre t h ∧
    X.bankDeposits t h = ∑ j, B.mass j * (B.plan j).deposits t h) ∧
  (∀ t h, FirmHistoryAdmissible P t h →
    X.bankNetIncome t h = ∑ j, B.mass j * bankTypeOwnerIncome
      (P.withBankPaymentLaw (B.paymentLaw j))
      (I.withBankFace (B.initialFace j)) X (B.plan j) t h) ∧
  (∀ t h, FirmHistoryAdmissible P t h → BankPopulationOTCRegimeAt P X B t h) ∧
  (∀ t h, FirmHistoryAdmissible P t h →
    expectedFacilityBorrowing P X t h =
      bankPopulationExpectedFacilityAt B t h ∧
    expectedPostReserves P X t h =
      bankPopulationExpectedPostReservesAt B t h ∧
    X.interbankPosition t h = bankPopulationExpectedInterbankAt B t h)

/-- The non-circular population data needed by the finite reduced bank rows.
Unlike `BankPopulationEquilibriumFor`, this predicate asks only for literal
bank feasibility, type aggregation and the OTC regime.  In particular it does
not contain value homogeneity, a local Bellman environment, FOCs or KKT data. -/
def BankPopulationFiniteRowEnvironmentFor {J : Type*}
    [Fintype J] [DecidableEq J]
    (P : Primitives S) (I : InheritedState) (X : Allocation S)
    (B : BankPopulationCandidate S J) : Prop :=
  (∀ j, 0 < B.mass j ∧ 0 < B.initialFace j) ∧
  (∀ j, BankFeasible
    (P.withBankPaymentLaw (B.paymentLaw j))
    (I.withBankFace (B.initialFace j)) X (B.plan j)) ∧
  (∀ t h, FirmHistoryAdmissible P t h →
    X.bankEquity t h = ∑ j, B.mass j * (B.plan j).equity t h ∧
    X.bankDividend t h = ∑ j, B.mass j * (B.plan j).dividend t h ∧
    X.bankRetainedEquity t h =
      ∑ j, B.mass j * (B.plan j).retainedEquity t h ∧
    X.bankLoans t h = ∑ j, B.mass j * (B.plan j).loans t h ∧
    X.reservesPrePayment t h =
      ∑ j, B.mass j * (B.plan j).reservesPre t h ∧
    X.bankDeposits t h = ∑ j, B.mass j * (B.plan j).deposits t h) ∧
  (∀ t h, FirmHistoryAdmissible P t h → BankPopulationOTCRegimeAt P X B t h)

theorem bankPopulationFiniteRowEnvironmentFor_of_equilibriumFor
    {J : Type*} [Fintype J] [DecidableEq J]
    (P : Primitives S) (I : InheritedState) (X : Allocation S)
    (B : BankPopulationCandidate S J)
    (H : BankPopulationEquilibriumFor P I X B) :
    BankPopulationFiniteRowEnvironmentFor P I X B := by
  rcases H with ⟨hmass, _hfaces, hoptimal, _htypeRenewal, haggregate,
    _hincome, hotc, _hbridges⟩
  exact ⟨hmass, fun j ↦ (hoptimal j).1, haggregate, hotc⟩

/-- Aggregating the bank-level settlement identity, using each type's
probability-one/mean-zero payment law and OTC clearing, gives
`Mpost = Mpre + W`. -/
theorem bankPopulationExpectedPostReserves_eq_pre_add_facility
    {J : Type*} [Fintype J] [DecidableEq J]
    (P : Primitives S) (I : InheritedState) (X : Allocation S)
    (B : BankPopulationCandidate S J)
    (H : BankPopulationEquilibriumFor P I X B)
    (t : ℕ) (h : History S t) (hs : FirmHistoryAdmissible P t h) :
    bankPopulationExpectedPostReservesAt B t h =
      X.reservesPrePayment t h + bankPopulationExpectedFacilityAt B t h := by
  classical
  rcases H with ⟨_hmass, _hfaces, _hoptimal, _htypeRenewal, haggregate,
    _hincome, hotc, _hbridges⟩
  rcases haggregate t h hs with
    ⟨_hequity, _hdividend, _hretained, _hloans, hreserves, _hdeposits⟩
  have hsettle := bankPlanSettlementIdentity_of_otcRegime P X B t h (hotc t h hs)
  have hinterbank := bankPopulationExpectedInterbankAt_eq_zero_of_otcRegime
    P X B t h (hotc t h hs)
  have htype : ∀ j,
      finiteSupportExpectation (B.paymentLaw j).support
          (B.paymentLaw j).probability (fun ω ↦ (B.plan j).reservesPost ω t h) =
        (B.plan j).reservesPre t h +
          finiteSupportExpectation (B.paymentLaw j).support
            (B.paymentLaw j).probability (fun ω ↦ (B.plan j).interbank ω t h) +
          finiteSupportExpectation (B.paymentLaw j).support
            (B.paymentLaw j).probability (fun ω ↦ (B.plan j).facility ω t h) := by
    intro j
    let transfer := fun ω : BankPayment ↦
      (X.depositRate t h / X.reserveRate t h) * (B.paymentLaw j).shock ω *
        (B.plan j).deposits t h
    have htransfer : finiteSupportExpectation (B.paymentLaw j).support
        (B.paymentLaw j).probability transfer = 0 := by
      unfold transfer finiteSupportExpectation
      calc
        (∑ ω ∈ (B.paymentLaw j).support,
          (B.paymentLaw j).probability ω *
            ((X.depositRate t h / X.reserveRate t h) *
              (B.paymentLaw j).shock ω * (B.plan j).deposits t h)) =
            ((X.depositRate t h / X.reserveRate t h) *
              (B.plan j).deposits t h) *
              (∑ ω ∈ (B.paymentLaw j).support,
                (B.paymentLaw j).probability ω * (B.paymentLaw j).shock ω) := by
                  rw [Finset.mul_sum]
                  apply Finset.sum_congr rfl
                  intro ω _
                  ring
        _ = 0 := by rw [(B.paymentLaw j).shock_mean_zero]; ring
    calc
      finiteSupportExpectation (B.paymentLaw j).support
          (B.paymentLaw j).probability (fun ω ↦ (B.plan j).reservesPost ω t h) =
        finiteSupportExpectation (B.paymentLaw j).support
          (B.paymentLaw j).probability (fun ω ↦
            (B.plan j).reservesPre t h + transfer ω +
              (B.plan j).interbank ω t h + (B.plan j).facility ω t h) := by
                unfold finiteSupportExpectation
                apply Finset.sum_congr rfl
                intro ω hω
                change (B.paymentLaw j).probability ω *
                    (B.plan j).reservesPost ω t h = _
                rw [hsettle j ω hω]
      _ = finiteSupportExpectation (B.paymentLaw j).support
            (B.paymentLaw j).probability (fun _ω ↦ (B.plan j).reservesPre t h) +
          finiteSupportExpectation (B.paymentLaw j).support
            (B.paymentLaw j).probability transfer +
          finiteSupportExpectation (B.paymentLaw j).support
            (B.paymentLaw j).probability (fun ω ↦ (B.plan j).interbank ω t h) +
          finiteSupportExpectation (B.paymentLaw j).support
            (B.paymentLaw j).probability (fun ω ↦ (B.plan j).facility ω t h) := by
              rw [finiteSupportExpectation_add, finiteSupportExpectation_add,
                finiteSupportExpectation_add]
      _ = (B.plan j).reservesPre t h +
          finiteSupportExpectation (B.paymentLaw j).support
            (B.paymentLaw j).probability (fun ω ↦ (B.plan j).interbank ω t h) +
          finiteSupportExpectation (B.paymentLaw j).support
            (B.paymentLaw j).probability (fun ω ↦ (B.plan j).facility ω t h) := by
              rw [finiteSupportExpectation_const _ _
                (B.paymentLaw j).probability_sum_one, htransfer]
              ring
  unfold bankPopulationExpectedPostReservesAt
  simp_rw [htype]
  simp_rw [mul_add]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  change (∑ j, B.mass j * (B.plan j).reservesPre t h) +
      bankPopulationExpectedInterbankAt B t h +
      bankPopulationExpectedFacilityAt B t h =
    X.reservesPrePayment t h + bankPopulationExpectedFacilityAt B t h
  rw [← hreserves, hinterbank]
  ring

/-- Facility use is nonnegative after aggregation because masses,
probabilities and every bank-level facility position are nonnegative. -/
theorem bankPopulationExpectedFacility_nonneg
    {J : Type*} [Fintype J] [DecidableEq J]
    (P : Primitives S) (I : InheritedState) (X : Allocation S)
    (B : BankPopulationCandidate S J)
    (H : BankPopulationEquilibriumFor P I X B)
    (t : ℕ) (h : History S t) (hs : FirmHistoryAdmissible P t h) :
    0 ≤ bankPopulationExpectedFacilityAt B t h := by
  classical
  rcases H with ⟨hmass, _hfaces, _hoptimal, _htypeRenewal, _haggregate,
    _hincome, hotc, _hbridges⟩
  have hfacility := bankPlanFacility_nonneg_of_otcRegime P X B t h (hotc t h hs)
  unfold bankPopulationExpectedFacilityAt finiteSupportExpectation
  apply Finset.sum_nonneg
  intro j _
  apply mul_nonneg (hmass j).1.le
  apply Finset.sum_nonneg
  intro ω hω
  apply mul_nonneg ((B.paymentLaw j).probability_nonneg ω)
  exact hfacility j ω hω

/-- Population aggregation proves the aggregate settlement equations; they do
not have to be supplied again as an independent equilibrium certificate. -/
theorem settlementClears_of_bankPopulationFor
    {J : Type*} [Fintype J] [DecidableEq J]
    (P : Primitives S) (I : InheritedState) (X : Allocation S)
    (B : BankPopulationCandidate S J)
    (H : BankPopulationEquilibriumFor P I X B) : SettlementClears P X := by
  intro t h hs
  have hpostAggregate := bankPopulationExpectedPostReserves_eq_pre_add_facility
    P I X B H t h hs
  have hfacilityNonneg := bankPopulationExpectedFacility_nonneg P I X B H t h hs
  rcases H with ⟨_hmass, _hfaces, _hoptimal, _htypeRenewal, _haggregate,
    _hincome, hotc, hbridges⟩
  rcases hbridges t h hs with ⟨hfacility, hpost, hinterbankBridge⟩
  have hinterbank := bankPopulationExpectedInterbankAt_eq_zero_of_otcRegime
    P X B t h (hotc t h hs)
  have hinterbankZero : X.interbankPosition t h = 0 := by
    rw [hinterbankBridge, hinterbank]
  refine ⟨hinterbankZero, ?_, ?_⟩
  · change 0 ≤ expectedFacilityBorrowing P X t h
    rw [hfacility]
    exact hfacilityNonneg
  · calc
      X.reservesPostPayment t h = expectedPostReserves P X t h := rfl
      _ = bankPopulationExpectedPostReservesAt B t h := hpost
      _ = X.reservesPrePayment t h + bankPopulationExpectedFacilityAt B t h :=
        hpostAggregate
      _ = X.reservesPrePayment t h + expectedFacilityBorrowing P X t h := by
        rw [hfacility]
      _ = X.reservesPrePayment t h + X.interbankPosition t h +
          X.facilityBorrowing t h := by
            simp only [expectedFacilityBorrowing, hinterbankZero, add_zero]

/-- The source permits any nonempty finite collection of bank types. -/
def BankPopulationEquilibrium (P : Primitives S) (I : InheritedState)
    (X : Allocation S) : Prop :=
  ∃ n : ℕ, ∃ B : BankPopulationCandidate S (Fin (n + 1)),
    BankPopulationEquilibriumFor P I X B

theorem settlementClears_of_bankPopulation
    (P : Primitives S) (I : InheritedState) (X : Allocation S)
    (H : BankPopulationEquilibrium P I X) : SettlementClears P X := by
  rcases H with ⟨n, B, hB⟩
  exact settlementClears_of_bankPopulationFor P I X B hB

/-- The aggregate bank return is a theorem of type aggregation, mean-zero
payment transfers, OTC clearing and the facility/post-reserve bridges.  It is
not an independently selectable equilibrium conjunct. -/
theorem bankPopulationExpectedGrossReturn_eq_aggregate
    {J : Type*} [Fintype J] [DecidableEq J]
    (P : Primitives S) (I : InheritedState) (X : Allocation S)
    (B : BankPopulationCandidate S J)
    (H : BankPopulationEquilibriumFor P I X B)
    (t : ℕ) (h : History S t) (hs : FirmHistoryAdmissible P t h) :
    bankPopulationExpectedGrossReturnAt P X B t h =
      expectedAggregateBankGrossReturn P X t h := by
  classical
  rcases H with ⟨_hmass, _hfaces, _hoptimal, _htypeRenewal, haggregate,
    _hincome, hotc, hbridges⟩
  rcases haggregate t h hs with
    ⟨_hequity, _hdividend, _hretained, hloans, _hreserves, hdeposits⟩
  rcases hbridges t h hs with ⟨hfacility, hpost, hinterbankBridge⟩
  have hinterbank := bankPopulationExpectedInterbankAt_eq_zero_of_otcRegime
    P X B t h (hotc t h hs)
  have hloanTerm :
      (∑ j, B.mass j * (X.loanRate t h * (B.plan j).loans t h)) =
        X.loanRate t h * X.bankLoans t h := by
    rw [hloans, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hdepositTerm :
      (∑ j, B.mass j * (X.depositRate t h * (B.plan j).deposits t h)) =
        X.depositRate t h * X.bankDeposits t h := by
    rw [hdeposits, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hpostTerm :
      (∑ j, B.mass j *
        (X.reserveRate t h * finiteSupportExpectation (B.paymentLaw j).support
          (B.paymentLaw j).probability
          (fun ω ↦ (B.plan j).reservesPost ω t h))) =
        X.reserveRate t h * X.reservesPostPayment t h := by
    calc
      (∑ j, B.mass j *
        (X.reserveRate t h * finiteSupportExpectation (B.paymentLaw j).support
          (B.paymentLaw j).probability
          (fun ω ↦ (B.plan j).reservesPost ω t h))) =
          X.reserveRate t h * bankPopulationExpectedPostReservesAt B t h := by
            unfold bankPopulationExpectedPostReservesAt
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro j _
            ring
      _ = X.reserveRate t h * expectedPostReserves P X t h := by rw [hpost]
      _ = X.reserveRate t h * X.reservesPostPayment t h := rfl
  have hinterbankTerm :
      (∑ j, B.mass j *
        (X.interbankRate t h * finiteSupportExpectation (B.paymentLaw j).support
          (B.paymentLaw j).probability
          (fun ω ↦ (B.plan j).interbank ω t h))) =
        X.interbankRate t h * X.interbankPosition t h := by
    calc
      (∑ j, B.mass j *
        (X.interbankRate t h * finiteSupportExpectation (B.paymentLaw j).support
          (B.paymentLaw j).probability
          (fun ω ↦ (B.plan j).interbank ω t h))) =
          X.interbankRate t h * bankPopulationExpectedInterbankAt B t h := by
            unfold bankPopulationExpectedInterbankAt
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro j _
            ring
      _ = 0 := by rw [hinterbank]; ring
      _ = X.interbankRate t h * X.interbankPosition t h := by
            rw [hinterbankBridge, hinterbank]
            ring
  have hfacilityTerm :
      (∑ j, B.mass j *
        (X.facilityRate t h * finiteSupportExpectation (B.paymentLaw j).support
          (B.paymentLaw j).probability
          (fun ω ↦ (B.plan j).facility ω t h))) =
        X.facilityRate t h * X.facilityBorrowing t h := by
    calc
      (∑ j, B.mass j *
        (X.facilityRate t h * finiteSupportExpectation (B.paymentLaw j).support
          (B.paymentLaw j).probability
          (fun ω ↦ (B.plan j).facility ω t h))) =
          X.facilityRate t h * bankPopulationExpectedFacilityAt B t h := by
            unfold bankPopulationExpectedFacilityAt
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro j _
            ring
      _ = X.facilityRate t h * expectedFacilityBorrowing P X t h := by rw [hfacility]
      _ = X.facilityRate t h * X.facilityBorrowing t h := rfl
  unfold bankPopulationExpectedGrossReturnAt
  simp_rw [expectedBankGrossReturn_eq_components]
  simp_rw [mul_sub, mul_add]
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib,
    Finset.sum_sub_distrib, Finset.sum_add_distrib]
  rw [hloanTerm, hpostTerm, hdepositTerm, hinterbankTerm, hfacilityTerm]
  rfl

/-- Type renewal, population aggregation and the return bridge imply the
aggregate renewal/owner-income identities on every supported history.  The
aggregate law is therefore a theorem, not an independently selectable
equilibrium field. -/
theorem bankRenewalFlows_of_populationFor {J : Type*} [Fintype J] [DecidableEq J]
    (P : Primitives S) (I : InheritedState) (X : Allocation S)
    (B : BankPopulationCandidate S J) (hfactor : 0 < bankRenewalFactor P)
    (H : BankPopulationEquilibriumFor P I X B) :
    BankRenewalFlows P I X := by
  classical
  have hreturnBridge := bankPopulationExpectedGrossReturn_eq_aggregate
    P I X B H
  rcases H with ⟨_hmass, hfaces, hoptimal, htypeRenewal, haggregate,
    hincome, _hotc, hbridges⟩
  have hpreExit : ∀ t h, FirmHistoryAdmissible P t h →
      (∑ j, B.mass j * bankTypePreExitEquity
        (P.withBankPaymentLaw (B.paymentLaw j))
        (I.withBankFace (B.initialFace j)) X (B.plan j) t h) =
        bankPreExitEquity P I X t h := by
    intro t h hs
    cases t with
    | zero =>
        simp only [bankTypePreExitEquity, InheritedState.withBankFace,
          bankPreExitEquity]
        calc
          (∑ j, B.mass j *
              (B.initialFace j / (bankRenewalFactor P * X.inflation 0 h))) =
              (∑ j, B.mass j * B.initialFace j) /
                (bankRenewalFactor P * X.inflation 0 h) := by
                simp only [div_eq_mul_inv]
                rw [Finset.sum_mul]
                apply Finset.sum_congr rfl
                intro j _
                ring
          _ = I.bankFace / (bankRenewalFactor P * X.inflation 0 h) := by
                rw [hfaces]
    | succ t =>
        have hparent : FirmHistoryAdmissible P t (previousHistory h) := by
          unfold FirmHistoryAdmissible at hs ⊢
          simp only [FiniteMarkovTree.historyWeight] at hs
          have htransition := P.tree.transition_nonneg
            (currentState (previousHistory h)) (currentState h)
          nlinarith
        have hreturn := hreturnBridge t (previousHistory h) hparent
        simp only [bankTypePreExitEquity, bankPreExitEquity]
        calc
          (∑ j, B.mass j *
              (expectedBankGrossReturn
                (P.withBankPaymentLaw (B.paymentLaw j)) X (B.plan j) t
                  (previousHistory h) / X.inflation (t + 1) h)) =
              bankPopulationExpectedGrossReturnAt P X B t (previousHistory h) /
                X.inflation (t + 1) h := by
                unfold bankPopulationExpectedGrossReturnAt
                simp only [div_eq_mul_inv]
                rw [Finset.sum_mul]
                apply Finset.sum_congr rfl
                intro j _
                ring
          _ = expectedAggregateBankGrossReturn P X t (previousHistory h) /
                X.inflation (t + 1) h := by rw [hreturn]
  refine ⟨?_, ?_, ?_⟩
  · intro t h hs
    rcases haggregate t h hs with
      ⟨hequity, hdividend, hretained, _hloans, _hreserves, _hdeposits⟩
    rw [hretained, hequity, hdividend, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    have hj := (hoptimal j).1.2.1 t h hs
    rw [hj]
    ring
  · intro t h hs
    rcases haggregate t h hs with
      ⟨hequity, _hdividend, _hretained, _hloans, _hreserves, _hdeposits⟩
    rw [hequity]
    calc
      (∑ j, B.mass j * (B.plan j).equity t h) =
          ∑ j, B.mass j * (bankRenewalFactor P * bankTypePreExitEquity
            (P.withBankPaymentLaw (B.paymentLaw j))
            (I.withBankFace (B.initialFace j)) X (B.plan j) t h) := by
              apply Finset.sum_congr rfl
              intro j _
              rw [htypeRenewal j t h hs]
              simp [bankRenewalFactor, Primitives.withBankPaymentLaw]
      _ = bankRenewalFactor P *
          (∑ j, B.mass j * bankTypePreExitEquity
            (P.withBankPaymentLaw (B.paymentLaw j))
            (I.withBankFace (B.initialFace j)) X (B.plan j) t h) := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro j _
              ring
      _ = bankRenewalFactor P * bankPreExitEquity P I X t h := by
              rw [hpreExit t h hs]
  · intro t h hs
    rcases haggregate t h hs with
      ⟨_hequity, hdividend, _hretained, _hloans, _hreserves, _hdeposits⟩
    rw [hincome t h hs, hdividend]
    unfold bankTypeOwnerIncome
    calc
      (∑ j, B.mass j *
        ((B.plan j).dividend t h + P.bankExit * (1 - P.bankSeedShare) *
          bankTypePreExitEquity (P.withBankPaymentLaw (B.paymentLaw j))
            (I.withBankFace (B.initialFace j)) X (B.plan j) t h)) =
          (∑ j, B.mass j * (B.plan j).dividend t h) +
            P.bankExit * (1 - P.bankSeedShare) *
              (∑ j, B.mass j * bankTypePreExitEquity
                (P.withBankPaymentLaw (B.paymentLaw j))
                (I.withBankFace (B.initialFace j)) X (B.plan j) t h) := by
                  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
                  apply Finset.sum_congr rfl
                  intro j _
                  ring
      _ = (∑ j, B.mass j * (B.plan j).dividend t h) +
          P.bankExit * (1 - P.bankSeedShare) * bankPreExitEquity P I X t h := by
            rw [hpreExit t h hs]

theorem bankRenewalFlows_of_population
    (P : Primitives S) (I : InheritedState) (X : Allocation S)
    (hfactor : 0 < bankRenewalFactor P)
    (H : BankPopulationEquilibrium P I X) : BankRenewalFlows P I X := by
  rcases H with ⟨n, B, hB⟩
  exact bankRenewalFlows_of_populationFor P I X B hfactor hB

/-- The history-local source regime used by Proposition 3.8.  Population and
matching objects determine the two OTC slopes, while only the candidate's
static feasibility, interiority, positive payment support, strict solvency on
positive-transition successors, and literal local Bellman environment enter
the portfolio FOCs.  No optimality or feasibility claim at another history is
hidden here. -/
def BankInteriorSpreadLocalRegime {J : Type*} [Fintype J]
    (P : Primitives S) (X : Allocation S)
    (candidatePlan : BankPlan S) (t : ℕ) (h : History S t)
    (mass retainedEquityByType loansByType reservesByType depositsByType : J → ℝ)
    (depositCapByType loanCapByType : J → ℝ)
    (paymentSupportByType : J → Finset BankPayment)
    (paymentProbabilityByType paymentShockByType : J → BankPayment → ℝ)
    (candidateType : J) (bankValue : BankValueProcess S)
    (deficitSupply surplusSupply tightness : ℝ) : Prop :=
  BankPopulationAt P X t h mass retainedEquityByType loansByType reservesByType
    depositsByType depositCapByType loanCapByType paymentSupportByType
    paymentProbabilityByType
    paymentShockByType candidateType ∧
  retainedEquityByType candidateType = candidatePlan.retainedEquity t h ∧
  loansByType candidateType = candidatePlan.loans t h ∧
  reservesByType candidateType = candidatePlan.reservesPre t h ∧
  depositsByType candidateType = candidatePlan.deposits t h ∧
  deficitSupply = bankDeficitSupplyAt P X t h mass reservesByType depositsByType
    paymentSupportByType paymentProbabilityByType paymentShockByType ∧
  surplusSupply = bankSurplusSupplyAt P X t h mass reservesByType depositsByType
    paymentSupportByType paymentProbabilityByType paymentShockByType ∧
  BilateralOTCActivity deficitSupply surplusSupply tightness ∧
  X.bankTightness t h = tightness ∧
  0 < P.matchingIntensity ∧
  X.interbankRate t h = otcNegotiatedRate (X.reserveRate t h)
    (X.facilityRate t h) P.matchingIntensity tightness ∧
  BankCandidateOTCFlowsAt P X candidatePlan t h tightness ∧
  (∀ j, BankStaticPortfolioFeasibleOnAt P X t h
    (bankOTCDeficitSlopeAt P X t h tightness)
    (bankOTCSurplusSlopeAt P X t h tightness)
    (retainedEquityByType j) (loansByType j) (reservesByType j)
    (depositsByType j) (depositCapByType j) (loanCapByType j)
      (paymentSupportByType j) (paymentShockByType j)) ∧
  BankStaticPortfolioFeasibleAt P X t h
    (bankOTCDeficitSlopeAt P X t h tightness)
    (bankOTCSurplusSlopeAt P X t h tightness)
    (candidatePlan.retainedEquity t h) (candidatePlan.loans t h)
    (candidatePlan.reservesPre t h) (candidatePlan.deposits t h) ∧
  0 < candidatePlan.retainedEquity t h ∧ 0 < candidatePlan.loans t h ∧
  0 < candidatePlan.reservesPre t h ∧ 0 < candidatePlan.deposits t h ∧
  (∀ ω ∈ P.paymentSupport, 0 < P.paymentProbability ω) ∧
  (∀ s, 0 < P.tree.transition (currentState h) s →
    0 < X.inflation (t + 1) (childHistory h s)) ∧
  (∀ ω ∈ P.paymentSupport, ∀ s,
    0 < P.tree.transition (currentState h) s →
      0 < bankRealPortfolioReturnAt P X t h
        (bankOTCDeficitSlopeAt P X t h tightness)
        (bankOTCSurplusSlopeAt P X t h tightness)
        (candidatePlan.loans t h) (candidatePlan.reservesPre t h)
        (candidatePlan.deposits t h) ω s) ∧
  BankValueHomogeneousAt P t h bankValue ∧
  BankBellmanLocalEnvironmentAt P X t h candidatePlan tightness bankValue

/-- Exact source regime for deriving the normalized bank FOCs.  The finite
population generates `S⁻,S⁺`; `bankValue` supplies the textual Bellman/SDF
environment as a hypothesis; and every local feasible triple is compared
literally.  The regulatory caps may bind. -/
def BankInteriorSpreadRegime {J : Type*} [Fintype J]
    (P : Primitives S) (I : InheritedState) (X : Allocation S)
    (candidatePlan : BankPlan S) (t : ℕ) (h : History S t)
    (mass retainedEquityByType loansByType reservesByType depositsByType : J → ℝ)
    (depositCapByType loanCapByType : J → ℝ)
    (paymentSupportByType : J → Finset BankPayment)
    (paymentProbabilityByType paymentShockByType : J → BankPayment → ℝ)
    (candidateType : J) (bankValue : BankValueProcess S)
    (deficitSupply surplusSupply tightness : ℝ) : Prop :=
  FirmHistoryAdmissible P t h ∧
  BankPopulationAt P X t h mass retainedEquityByType loansByType reservesByType
    depositsByType depositCapByType loanCapByType paymentSupportByType
    paymentProbabilityByType
    paymentShockByType candidateType ∧
  retainedEquityByType candidateType = candidatePlan.retainedEquity t h ∧
  loansByType candidateType = candidatePlan.loans t h ∧
  reservesByType candidateType = candidatePlan.reservesPre t h ∧
  depositsByType candidateType = candidatePlan.deposits t h ∧
  deficitSupply = bankDeficitSupplyAt P X t h mass reservesByType depositsByType
    paymentSupportByType paymentProbabilityByType paymentShockByType ∧
  surplusSupply = bankSurplusSupplyAt P X t h mass reservesByType depositsByType
    paymentSupportByType paymentProbabilityByType paymentShockByType ∧
  BilateralOTCActivity deficitSupply surplusSupply tightness ∧
  X.bankTightness t h = tightness ∧
  0 < P.matchingIntensity ∧
  X.interbankRate t h = otcNegotiatedRate (X.reserveRate t h)
    (X.facilityRate t h) P.matchingIntensity tightness ∧
  BankCandidateOTCFlowsAt P X candidatePlan t h tightness ∧
  (∀ j, BankStaticPortfolioFeasibleOnAt P X t h
    (bankOTCDeficitSlopeAt P X t h tightness)
    (bankOTCSurplusSlopeAt P X t h tightness)
    (retainedEquityByType j) (loansByType j) (reservesByType j)
    (depositsByType j) (depositCapByType j) (loanCapByType j)
      (paymentSupportByType j) (paymentShockByType j)) ∧
  BankStaticPortfolioFeasibleAt P X t h
    (bankOTCDeficitSlopeAt P X t h tightness)
    (bankOTCSurplusSlopeAt P X t h tightness)
    (candidatePlan.retainedEquity t h) (candidatePlan.loans t h)
    (candidatePlan.reservesPre t h) (candidatePlan.deposits t h) ∧
  0 < candidatePlan.retainedEquity t h ∧ 0 < candidatePlan.loans t h ∧
  0 < candidatePlan.reservesPre t h ∧ 0 < candidatePlan.deposits t h ∧
  (∀ s, 0 < P.tree.transition (currentState h) s →
    0 < X.inflation (t + 1) (childHistory h s)) ∧
  (∀ ω ∈ P.paymentSupport, ∀ s,
    0 < P.tree.transition (currentState h) s →
      0 < bankReducedPortfolioReturn P X t h
      (bankOTCDeficitSlopeAt P X t h tightness)
      (bankOTCSurplusSlopeAt P X t h tightness)
      (candidatePlan.loans t h) (candidatePlan.reservesPre t h)
      (candidatePlan.deposits t h) ω /
        X.inflation (t + 1) (childHistory h s)) ∧
  BankOptimalWithValue P I X candidatePlan bankValue

/-- The global recurrent-tree regime implies the local history regime used by
Proposition 3.8.  This bridge is deliberately separate: the proposition itself
does not ask for bank optimality or population feasibility at other histories. -/
theorem bankInteriorSpreadLocalRegime_of_global {J : Type*} [Fintype J]
    (P : Primitives S) (I : InheritedState) (X : Allocation S)
    (candidatePlan : BankPlan S) (t : ℕ) (h : History S t)
    (mass retainedEquityByType loansByType reservesByType depositsByType : J → ℝ)
    (depositCapByType loanCapByType : J → ℝ)
    (paymentSupportByType : J → Finset BankPayment)
    (paymentProbabilityByType paymentShockByType : J → BankPayment → ℝ)
    (candidateType : J) (bankValue : BankValueProcess S)
    (deficitSupply surplusSupply tightness : ℝ)
    (H : BankInteriorSpreadRegime P I X candidatePlan t h mass
      retainedEquityByType loansByType reservesByType depositsByType
      depositCapByType loanCapByType
      paymentSupportByType paymentProbabilityByType paymentShockByType
      candidateType bankValue deficitSupply surplusSupply tightness) :
    BankInteriorSpreadLocalRegime P X candidatePlan t h mass
      retainedEquityByType loansByType reservesByType depositsByType
      depositCapByType loanCapByType
      paymentSupportByType paymentProbabilityByType paymentShockByType
      candidateType bankValue deficitSupply surplusSupply tightness := by
  rcases H with ⟨hhistory, hpopulation, hretained, hloans, hreserves, hdeposits,
    hdeficit, hsurplus, hactivity, htightness, hmatching, hrate,
    hflows, hpopulationFeasible, hcandidateFeasible, hretainedPos, hloansPos,
    hreservesPos, hdepositsPos, hinflation, hstrictSolvency, hglobalOptimal⟩
  rcases hglobalOptimal with ⟨_, hlocalBellman⟩
  rcases hlocalBellman t h hhistory with
    ⟨hdynamicHomogeneity, henvironment, _dynamicCandidate⟩
  have hhomogeneous := hdynamicHomogeneity
  rw [htightness] at henvironment
  exact ⟨hpopulation, hretained, hloans, hreserves, hdeposits, hdeficit,
    hsurplus, hactivity, htightness, hmatching, hrate, hflows,
    hpopulationFeasible, hcandidateFeasible, hretainedPos, hloansPos,
    hreservesPos, hdepositsPos,
    P.payment_probability_pos_on_support,
    hinflation,
    hstrictSolvency,
    hhomogeneous, henvironment⟩

/-- Slater-style qualification for the static concave program. -/
def BankStaticKKTConstraintQualificationAt
    (P : Primitives S) (X : Allocation S) (t : ℕ) (h : History S t)
    (deficitSlope surplusSlope retainedEquity : ℝ) : Prop :=
  ∃ loans reserves deposits,
    0 < loans ∧ 0 < reserves ∧ 0 < deposits ∧
    loans + reserves = deposits + retainedEquity ∧
    deposits < P.bankDepositCap * retainedEquity ∧
    loans < P.bankLoanCap * retainedEquity ∧
    ∀ ω ∈ P.paymentSupport, ∀ s,
      0 < P.tree.transition (currentState h) s →
      0 < bankRealPortfolioReturnAt P X t h deficitSlope surplusSlope
        loans reserves deposits ω s

theorem otcLiquidityPayoff_midpoint_reserve
    (deficitSlope surplusSlope settlement retainedEquity : ℝ)
    (hslopes : surplusSlope ≤ deficitSlope) (hequity : 0 ≤ retainedEquity) :
    (otcLiquidityPayoff deficitSlope surplusSlope settlement +
        otcLiquidityPayoff deficitSlope surplusSlope retainedEquity) / 2 ≤
      otcLiquidityPayoff deficitSlope surplusSlope
        ((settlement + retainedEquity) / 2) := by
  by_cases hs : settlement < 0
  · by_cases hm : (settlement + retainedEquity) / 2 < 0
    · simp [otcLiquidityPayoff, hs, hm, not_lt.mpr hequity]
      nlinarith
    · have hm0 : 0 ≤ (settlement + retainedEquity) / 2 := le_of_not_gt hm
      simp [otcLiquidityPayoff, hs, not_lt.mpr hequity, not_lt.mpr hm0]
      nlinarith
  · have hs0 : 0 ≤ settlement := le_of_not_gt hs
    have hm0 : 0 ≤ (settlement + retainedEquity) / 2 := by positivity
    simp [otcLiquidityPayoff, hs, not_lt.mpr hequity, not_lt.mpr hm0]
    exact le_of_eq (by ring)

theorem bankReducedPortfolioReturn_midpoint_reserve
    (P : Primitives S) (X : Allocation S) (t : ℕ) (h : History S t)
    (deficitSlope surplusSlope retainedEquity loans reserves deposits : ℝ)
    (hslopes : surplusSlope ≤ deficitSlope) (hequity : 0 ≤ retainedEquity)
    (ω : BankPayment) :
    (bankReducedPortfolioReturn P X t h deficitSlope surplusSlope
        loans reserves deposits ω +
      bankReducedPortfolioReturn P X t h deficitSlope surplusSlope
        0 retainedEquity 0 ω) / 2 ≤
      bankReducedPortfolioReturn P X t h deficitSlope surplusSlope
        (loans / 2) ((reserves + retainedEquity) / 2) (deposits / 2) ω := by
  have hchi := otcLiquidityPayoff_midpoint_reserve deficitSlope surplusSlope
    (bankSettlementSurplus reserves (P.reserveRequirementPath t h)
      (X.depositRate t h / X.reserveRate t h) deposits (P.paymentShock ω))
    retainedEquity hslopes hequity
  have hsettlement :
      bankSettlementSurplus ((reserves + retainedEquity) / 2)
          (P.reserveRequirementPath t h) (X.depositRate t h / X.reserveRate t h)
          (deposits / 2) (P.paymentShock ω) =
        (bankSettlementSurplus reserves (P.reserveRequirementPath t h)
            (X.depositRate t h / X.reserveRate t h) deposits (P.paymentShock ω) +
          retainedEquity) / 2 := by
    unfold bankSettlementSurplus
    ring
  unfold bankReducedPortfolioReturn bankReducedPortfolioReturnWithShock at *
  rw [hsettlement]
  simp only [bankSettlementSurplus, mul_zero, sub_zero, add_zero] at hchi ⊢
  nlinarith

/-- The source qualification is derived, not added: mix the strictly solvent
interior candidate with the reserves-only portfolio `(0,x,0)`. -/
theorem bankStaticKKTConstraintQualification_of_interior
    (P : Primitives S) (X : Allocation S) (t : ℕ) (h : History S t)
    (deficitSlope surplusSlope retainedEquity candidateLoans candidateReserves
      candidateDeposits : ℝ)
    (hreserveRate : 0 < X.reserveRate t h)
    (hsurplusSlope : 0 ≤ surplusSlope)
    (hconcave : surplusSlope ≤ deficitSlope)
    (hfeasible : BankStaticPortfolioFeasibleAt P X t h deficitSlope surplusSlope
      retainedEquity candidateLoans candidateReserves candidateDeposits)
    (hequity : 0 < retainedEquity)
    (hinterior : 0 < candidateLoans ∧ 0 < candidateReserves ∧
      0 < candidateDeposits)
    (hinflation : ∀ s, 0 < P.tree.transition (currentState h) s →
      0 < X.inflation (t + 1) (childHistory h s))
    (hstrictSolvency : ∀ ω ∈ P.paymentSupport, ∀ s,
      0 < P.tree.transition (currentState h) s →
      0 < bankRealPortfolioReturnAt P X t h deficitSlope surplusSlope
        candidateLoans candidateReserves candidateDeposits ω s) :
    BankStaticKKTConstraintQualificationAt P X t h deficitSlope surplusSlope
      retainedEquity := by
  rcases hfeasible with ⟨hloans, hreserves, hdeposits, hbalance, hdepositCap,
    hloanCap, _⟩
  refine ⟨candidateLoans / 2, (candidateReserves + retainedEquity) / 2,
    candidateDeposits / 2, by nlinarith [hinterior.1],
    by nlinarith [hinterior.2.1, hequity], by nlinarith [hinterior.2.2],
    ?_, ?_, ?_, ?_⟩
  · nlinarith
  · have hcapPos : 0 < P.bankDepositCap * retainedEquity := lt_of_lt_of_le
      hinterior.2.2 hdepositCap
    nlinarith
  · have hcapPos : 0 < P.bankLoanCap * retainedEquity :=
      lt_of_lt_of_le hinterior.1 hloanCap
    nlinarith
  · intro ω hω s hs
    have hcandidate := hstrictSolvency ω hω s hs
    have hinfl := hinflation s hs
    have hreserveNominal : 0 < bankReducedPortfolioReturn P X t h
        deficitSlope surplusSlope 0 retainedEquity 0 ω := by
      unfold bankReducedPortfolioReturn bankReducedPortfolioReturnWithShock
      simp [bankSettlementSurplus, otcLiquidityPayoff, not_lt.mpr hequity.le]
      nlinarith [mul_pos hreserveRate hequity]
    have hmix := bankReducedPortfolioReturn_midpoint_reserve P X t h
      deficitSlope surplusSlope retainedEquity candidateLoans candidateReserves
      candidateDeposits hconcave hequity.le ω
    unfold bankRealPortfolioReturnAt at hcandidate ⊢
    have hcandidateNominal : 0 < bankReducedPortfolioReturn P X t h
        deficitSlope surplusSlope candidateLoans candidateReserves
        candidateDeposits ω := by
      have heq : bankReducedPortfolioReturn P X t h deficitSlope surplusSlope
          candidateLoans candidateReserves candidateDeposits ω =
          (bankReducedPortfolioReturn P X t h deficitSlope surplusSlope
            candidateLoans candidateReserves candidateDeposits ω /
              X.inflation (t + 1) (childHistory h s)) *
            X.inflation (t + 1) (childHistory h s) := by
        field_simp [hinfl.ne']
      rw [heq]
      positivity
    have hmixNominal : 0 < bankReducedPortfolioReturn P X t h
        deficitSlope surplusSlope (candidateLoans / 2)
        ((candidateReserves + retainedEquity) / 2) (candidateDeposits / 2) ω := by
      nlinarith
    exact div_pos hmixNominal hinfl

/-- The two normalized source FOCs, pointwise liquidity supergradient, and the
two regulatory-cap dual conditions from source lines 794--804.  Monotonicity of
a tie-consistent marginal selection is a derived covariance-proof fact and is
kept out of this source-facing predicate. -/
def BankStaticFOCConditionsAt
    (P : Primitives S) (X : Allocation S) (t : ℕ) (h : History S t)
    (deficitSlope surplusSlope retainedEquity candidateLoans candidateReserves
      candidateDeposits : ℝ)
    (marginalLiquidity : BankPayment → ℝ)
    (loanCapDual depositCapDual : ℝ) : Prop :=
  let probability := P.paymentProbability
  let shock := P.paymentShock
  let rho := (P.reserveRequirementPath t h)
  let xi := X.depositRate t h / X.reserveRate t h
  let settlementSurplus := fun ω ↦
    bankSettlementSurplus candidateReserves rho xi candidateDeposits (shock ω)
  0 ≤ loanCapDual ∧ 0 ≤ depositCapDual ∧
  (∀ ω ∈ P.paymentSupport, IsOTCLiquiditySupergradient deficitSlope surplusSlope
    (settlementSurplus ω) (marginalLiquidity ω)) ∧
  X.loanRate t h - X.reserveRate t h =
    finiteSupportExpectation P.paymentSupport probability marginalLiquidity + loanCapDual ∧
  X.depositRate t h - X.reserveRate t h =
    finiteSupportExpectation P.paymentSupport probability (fun ω ↦
      marginalLiquidity ω * (1 - rho + (xi - rho) * shock ω)) - depositCapDual ∧
  loanCapDual *
    (P.bankLoanCap * retainedEquity - candidateLoans) = 0 ∧
  depositCapDual *
    (P.bankDepositCap * retainedEquity - candidateDeposits) = 0

/-- Proof support for Proposition 3.8: the exact source FOC/cap-dual system
together with antitonicity of the constructed tie-consistent marginal selector.
The second conjunct is derived from concavity and settlement monotonicity. -/
def BankStaticKKTConditionsAt
    (P : Primitives S) (X : Allocation S) (t : ℕ) (h : History S t)
    (deficitSlope surplusSlope retainedEquity candidateLoans candidateReserves
      candidateDeposits : ℝ)
    (marginalLiquidity : BankPayment → ℝ)
    (loanCapDual depositCapDual : ℝ) : Prop :=
  BankStaticFOCConditionsAt P X t h deficitSlope surplusSlope retainedEquity
    candidateLoans candidateReserves candidateDeposits marginalLiquidity
    loanCapDual depositCapDual ∧
  ∀ ω ∈ P.paymentSupport, ∀ ω' ∈ P.paymentSupport,
    P.paymentShock ω ≤ P.paymentShock ω' →
      marginalLiquidity ω' ≤ marginalLiquidity ω

/-- A two-control deviation preserves the balance sheet by adjusting reserves. -/
theorem bankSettlementSurplus_portfolioPerturbation
    (reserves rho xi deposits shock step loanDirection depositDirection : ℝ) :
    bankSettlementSurplus (reserves + step * (depositDirection - loanDirection))
        rho xi (deposits + step * depositDirection) shock =
      bankSettlementSurplus reserves rho xi deposits shock +
        step * (-loanDirection + (1 - rho + (xi - rho) * shock) * depositDirection) := by
  unfold bankSettlementSurplus
  ring

/-- All zero-settlement atoms have the same two-control kink direction.
This follows from balance and positive deposits, not a shock-selection premise. -/
theorem bankSettlementSurplus_zero_directionCoefficient
    (loans reserves deposits equity rho xi shock : ℝ)
    (hbalance : loans + reserves = deposits + equity)
    (hdeposits : deposits ≠ 0)
    (hzero : bankSettlementSurplus reserves rho xi deposits shock = 0) :
    1 - rho + (xi - rho) * shock = (loans - equity) / deposits := by
  apply (eq_div_iff hdeposits).2
  unfold bankSettlementSurplus at hzero
  nlinarith

/-- A two-dimensional piecewise-linear directional condition gives a common
kink slope and the normal cone of the two upper bounds. -/
theorem kinkSlope_of_noImprovingDirections
    (lo hi a b c loanSlack depositSlack : ℝ)
    (hslopes : lo ≤ hi)
    (hdir : ∀ u v : ℝ,
      (loanSlack = 0 → u ≤ 0) → (depositSlack = 0 → v ≤ 0) →
      a * u + b * v + min (lo * (-u + c * v)) (hi * (-u + c * v)) ≤ 0) :
    ∃ k : ℝ, lo ≤ k ∧ k ≤ hi ∧ 0 ≤ a - k ∧ 0 ≤ b + c * k ∧
      (a - k) * loanSlack = 0 ∧ (b + c * k) * depositSlack = 0 := by
  have hnegL := hdir (-1) 0 (by intros; norm_num) (by intros; norm_num)
  have haLower : lo ≤ a := by
    simp only [neg_neg, mul_zero, add_zero, mul_one, min_eq_left hslopes,
      mul_neg_one] at hnegL
    linarith
  by_cases hL : loanSlack = 0
  · by_cases hD : depositSlack = 0
    · by_cases hc : 0 < c
      · have hnegD := hdir 0 (-1) (by intros; norm_num) (by intros; norm_num)
        have htop : 0 ≤ b + c * hi := by
          have hm : hi * (-c) ≤ lo * (-c) :=
            mul_le_mul_of_nonpos_right hslopes (by linarith)
          simp only [neg_zero, mul_neg_one, zero_add, mul_zero, zero_add,
            min_eq_right hm] at hnegD
          nlinarith
        have hdiagonal := hdir (-c) (-1) (by intros; linarith) (by intros; norm_num)
        have hcross : 0 ≤ b + c * a := by
          have hz : -(-c) + c * (-1) = 0 := by ring
          rw [hz] at hdiagonal
          simp only [mul_zero, min_self, add_zero, mul_neg] at hdiagonal
          nlinarith
        refine ⟨min a hi, le_min haLower hslopes, min_le_right _ _, ?_, ?_, ?_, ?_⟩
        · exact sub_nonneg.mpr (min_le_left _ _)
        · rcases le_total a hi with hx | hx
          · simpa only [min_eq_left hx] using hcross
          · simpa only [min_eq_right hx] using htop
        · simp [hL]
        · simp [hD]
      · have hc0 : c ≤ 0 := le_of_not_gt hc
        have hnegD := hdir 0 (-1) (by intros; norm_num) (by intros; norm_num)
        have hm : lo * (-c) ≤ hi * (-c) :=
          mul_le_mul_of_nonneg_right hslopes (by linarith)
        have hb : 0 ≤ b + c * lo := by
          simp only [neg_zero, mul_neg_one, zero_add, mul_zero, zero_add,
            min_eq_left hm] at hnegD
          nlinarith
        exact ⟨lo, le_rfl, hslopes, sub_nonneg.mpr haLower, hb,
          by simp [hL], by simp [hD]⟩
    · have hposD := hdir 0 1 (by intros; norm_num) (by intro hz; exact (hD hz).elim)
      have hnegD := hdir 0 (-1) (by intros; norm_num) (by intros; norm_num)
      by_cases hc : c = 0
      · have hb : b = 0 := by
          simp [hc] at hposD hnegD
          linarith
        exact ⟨lo, le_rfl, hslopes, sub_nonneg.mpr haLower,
          by simp [hc, hb], by simp [hL], by simp [hc, hb]⟩
      · have hroot : b + c * (-b / c) = 0 := by field_simp; ring
        have hklo : lo ≤ -b / c := by
          by_cases hcpos : 0 < c
          · have hm : lo * c ≤ hi * c := mul_le_mul_of_nonneg_right hslopes hcpos.le
            simp only [neg_zero, mul_one, zero_add, mul_zero, zero_add,
              min_eq_left hm] at hposD
            apply (le_div_iff₀ hcpos).2
            nlinarith
          · have hcneg : c < 0 := lt_of_le_of_ne (le_of_not_gt hcpos) hc
            have hm : lo * (-c) ≤ hi * (-c) :=
              mul_le_mul_of_nonneg_right hslopes (by linarith)
            simp only [neg_zero, mul_neg_one, zero_add, mul_zero, zero_add,
              min_eq_left hm] at hnegD
            apply (le_div_iff_of_neg hcneg).2
            nlinarith
        have hkhi : -b / c ≤ hi := by
          by_cases hcpos : 0 < c
          · have hm : hi * (-c) ≤ lo * (-c) :=
              mul_le_mul_of_nonpos_right hslopes (by linarith)
            simp only [neg_zero, mul_neg_one, zero_add, mul_zero, zero_add,
              min_eq_right hm] at hnegD
            apply (div_le_iff₀ hcpos).2
            nlinarith
          · have hcneg : c < 0 := lt_of_le_of_ne (le_of_not_gt hcpos) hc
            have hm : hi * c ≤ lo * c := mul_le_mul_of_nonpos_right hslopes hcneg.le
            simp only [neg_zero, mul_one, zero_add, mul_zero, zero_add,
              min_eq_right hm] at hposD
            apply (div_le_iff_of_neg hcneg).2
            nlinarith
        have hka : -b / c ≤ a := by
          by_cases hcpos : 0 < c
          · have hh := hdir (-c) (-1) (by intros; linarith) (by intros; norm_num)
            have hz : -(-c) + c * (-1) = 0 := by ring
            rw [hz] at hh
            simp only [mul_zero, min_self, add_zero, mul_neg] at hh
            apply (div_le_iff₀ hcpos).2
            nlinarith
          · have hcneg : c < 0 := lt_of_le_of_ne (le_of_not_gt hcpos) hc
            have hh := hdir c 1 (by intros; linarith) (by intro hz; exact (hD hz).elim)
            have hz : -c + c * 1 = 0 := by ring
            rw [hz] at hh
            simp only [mul_zero, min_self, add_zero, mul_one] at hh
            apply (div_le_iff_of_neg hcneg).2
            nlinarith
        exact ⟨-b/c, hklo, hkhi, sub_nonneg.mpr hka, hroot.ge,
          by simp [hL], by rw [hroot]; simp⟩
  · have hposL := hdir 1 0 (by intro hz; exact (hL hz).elim) (by intros; norm_num)
    have hm : -hi ≤ -lo := neg_le_neg hslopes
    have haUpper : a ≤ hi := by
      simp only [mul_zero, add_zero, mul_neg_one, min_eq_right hm,
        mul_one] at hposL
      linarith
    have hneg := hdir (-c) (-1) (by intro hz; exact (hL hz).elim) (by intros; norm_num)
    have hz : -(-c) + c * (-1) = 0 := by ring
    rw [hz] at hneg
    simp only [mul_zero, min_self, add_zero, mul_neg] at hneg
    have hb : 0 ≤ b + c * a := by nlinarith
    refine ⟨a, haLower, haUpper, by simp, hb, by simp, ?_⟩
    by_cases hD : depositSlack = 0
    · simp [hD]
    · have hp := hdir c 1 (by intro hz; exact (hL hz).elim)
          (by intro hz; exact (hD hz).elim)
      have hz : -c + c * 1 = 0 := by ring
      rw [hz] at hp
      simp only [mul_zero, min_self, add_zero, mul_one] at hp
      have heq : b + c * a = 0 := by nlinarith
      rw [heq]; simp

/-! The following local lemmas turn actual static optimality into the exact
finite-support directional condition used by the nonsmooth bank KKT proof. -/

theorem otcLiquidityPayoff_eq_min
    (lo hi surplus : ℝ) (h : lo ≤ hi) :
    otcLiquidityPayoff hi lo surplus = min (lo * surplus) (hi * surplus) := by
  by_cases hs : surplus < 0
  · have hm : hi * surplus ≤ lo * surplus :=
      mul_le_mul_of_nonpos_right h hs.le
    simp [otcLiquidityPayoff, hs, min_eq_right hm]
  · have hs0 : 0 ≤ surplus := le_of_not_gt hs
    have hm : lo * surplus ≤ hi * surplus :=
      mul_le_mul_of_nonneg_right h hs0
    simp [otcLiquidityPayoff, hs, min_eq_left hm]

theorem continuous_otcLiquidityPayoff (lo hi : ℝ) (h : lo ≤ hi) :
    Continuous (otcLiquidityPayoff hi lo) := by
  rw [show otcLiquidityPayoff hi lo = fun surplus : ℝ =>
      min (lo * surplus) (hi * surplus) by
    funext surplus
    exact otcLiquidityPayoff_eq_min lo hi surplus h]
  fun_prop

variable {S : Type*} [Fintype S] [DecidableEq S]

omit [DecidableEq S] in
theorem continuous_bankRealPortfolioReturnAt_perturbation
    (P : Primitives S) (X : Allocation S) (t : ℕ) (h : History S t)
    (deficitSlope surplusSlope loans reserves deposits u v : ℝ)
    (hconcave : surplusSlope ≤ deficitSlope) (ω : BankPayment) (s : S) :
    Continuous (fun step : ℝ =>
      bankRealPortfolioReturnAt P X t h deficitSlope surplusSlope
        (loans + step * u) (reserves + step * (v - u))
        (deposits + step * v) ω s) := by
  unfold bankRealPortfolioReturnAt bankReducedPortfolioReturn
    bankReducedPortfolioReturnWithShock bankSettlementSurplus
  have hchi := continuous_otcLiquidityPayoff surplusSlope deficitSlope hconcave
  fun_prop

theorem eventually_bankStaticPortfolioFeasibleAt_perturbation
    (P : Primitives S) (X : Allocation S) (t : ℕ) (h : History S t)
    (deficitSlope surplusSlope retainedEquity candidateLoans candidateReserves
      candidateDeposits u v : ℝ)
    (hconcave : surplusSlope ≤ deficitSlope)
    (hfeasible : BankStaticPortfolioFeasibleAt P X t h deficitSlope surplusSlope
      retainedEquity candidateLoans candidateReserves candidateDeposits)
    (hinterior : 0 < candidateLoans ∧ 0 < candidateReserves ∧
      0 < candidateDeposits)
    (hstrictSolvency : ∀ ω ∈ P.paymentSupport, ∀ s,
      0 < P.tree.transition (currentState h) s →
      0 < bankRealPortfolioReturnAt P X t h deficitSlope surplusSlope
        candidateLoans candidateReserves candidateDeposits ω s)
    (hu : P.bankLoanCap * retainedEquity - candidateLoans = 0 → u ≤ 0)
    (hv : P.bankDepositCap * retainedEquity - candidateDeposits = 0 → v ≤ 0) :
    ∀ᶠ (step : ℝ) in nhdsWithin 0 (Set.Ioi 0),
      BankStaticPortfolioFeasibleAt P X t h deficitSlope surplusSlope
        retainedEquity (candidateLoans + step * u)
        (candidateReserves + step * (v - u))
        (candidateDeposits + step * v) := by
  rcases hfeasible with ⟨hloans, hreserves, hdeposits, hbalance,
    hdepositCap, hloanCap, hsolvent⟩
  have hfilter : nhdsWithin (0 : ℝ) (Set.Ioi 0) ≤ nhds 0 := inf_le_left
  have hloanPos : ∀ᶠ (step : ℝ) in nhdsWithin 0 (Set.Ioi 0),
      0 < candidateLoans + step * u := by
    have hc : Continuous (fun step : ℝ => candidateLoans + step * u) := by fun_prop
    have ht := (hc.tendsto 0).mono_left hfilter
    have h0 : 0 < candidateLoans + 0 * u := by simpa using hinterior.1
    exact ht.eventually (eventually_gt_nhds h0)
  have hreservePos : ∀ᶠ (step : ℝ) in nhdsWithin 0 (Set.Ioi 0),
      0 < candidateReserves + step * (v - u) := by
    have hc : Continuous (fun step : ℝ => candidateReserves + step * (v - u)) := by
      fun_prop
    have ht := (hc.tendsto 0).mono_left hfilter
    have h0 : 0 < candidateReserves + 0 * (v - u) := by
      simpa using hinterior.2.1
    exact ht.eventually (eventually_gt_nhds h0)
  have hdepositPos : ∀ᶠ (step : ℝ) in nhdsWithin 0 (Set.Ioi 0),
      0 < candidateDeposits + step * v := by
    have hc : Continuous (fun step : ℝ => candidateDeposits + step * v) := by fun_prop
    have ht := (hc.tendsto 0).mono_left hfilter
    have h0 : 0 < candidateDeposits + 0 * v := by simpa using hinterior.2.2
    exact ht.eventually (eventually_gt_nhds h0)
  have hloanCapEventually : ∀ᶠ (step : ℝ) in nhdsWithin 0 (Set.Ioi 0),
      candidateLoans + step * u ≤ P.bankLoanCap * retainedEquity := by
    by_cases hslack : P.bankLoanCap * retainedEquity - candidateLoans = 0
    · filter_upwards [self_mem_nhdsWithin] with step hstep
      have hstepPos : 0 < step := hstep
      nlinarith [hu hslack]
    · have hstrict : candidateLoans < P.bankLoanCap * retainedEquity := by
        have hnonneg : 0 ≤ P.bankLoanCap * retainedEquity - candidateLoans := by
          linarith
        exact sub_pos.mp (lt_of_le_of_ne hnonneg (Ne.symm hslack))
      have hc : Continuous (fun step : ℝ => candidateLoans + step * u) := by fun_prop
      have ht := (hc.tendsto 0).mono_left hfilter
      have h0 : candidateLoans + 0 * u < P.bankLoanCap * retainedEquity := by
        simpa using hstrict
      exact (ht.eventually (eventually_lt_nhds h0)).mono (fun step hs => hs.le)
  have hdepositCapEventually : ∀ᶠ (step : ℝ) in nhdsWithin 0 (Set.Ioi 0),
      candidateDeposits + step * v ≤ P.bankDepositCap * retainedEquity := by
    by_cases hslack : P.bankDepositCap * retainedEquity - candidateDeposits = 0
    · filter_upwards [self_mem_nhdsWithin] with step hstep
      have hstepPos : 0 < step := hstep
      nlinarith [hv hslack]
    · have hstrict : candidateDeposits < P.bankDepositCap * retainedEquity := by
        have hnonneg : 0 ≤ P.bankDepositCap * retainedEquity - candidateDeposits := by
          linarith
        exact sub_pos.mp (lt_of_le_of_ne hnonneg (Ne.symm hslack))
      have hc : Continuous (fun step : ℝ => candidateDeposits + step * v) := by fun_prop
      have ht := (hc.tendsto 0).mono_left hfilter
      have h0 : candidateDeposits + 0 * v < P.bankDepositCap * retainedEquity := by
        simpa using hstrict
      exact (ht.eventually (eventually_lt_nhds h0)).mono (fun step hs => hs.le)
  have hsolventEventually : ∀ᶠ (step : ℝ) in nhdsWithin 0 (Set.Ioi 0),
      ∀ ω ∈ P.paymentSupport, ∀ s,
        0 < P.tree.transition (currentState h) s →
        0 ≤ bankRealPortfolioReturnAt P X t h deficitSlope surplusSlope
          (candidateLoans + step * u)
          (candidateReserves + step * (v - u))
          (candidateDeposits + step * v) ω s := by
    rw [eventually_all_finset]
    intro ω hω
    rw [eventually_all]
    intro s
    by_cases hs : 0 < P.tree.transition (currentState h) s
    · have hc := continuous_bankRealPortfolioReturnAt_perturbation
          P X t h deficitSlope surplusSlope candidateLoans candidateReserves
          candidateDeposits u v hconcave ω s
      have ht := (hc.tendsto 0).mono_left hfilter
      have h0 : 0 < bankRealPortfolioReturnAt P X t h deficitSlope surplusSlope
          (candidateLoans + 0 * u) (candidateReserves + 0 * (v - u))
          (candidateDeposits + 0 * v) ω s := by
        simpa using hstrictSolvency ω hω s hs
      have hevent := ht.eventually (eventually_gt_nhds h0)
      exact hevent.mono (fun step hpos _ => hpos.le)
    · exact Filter.Eventually.of_forall (fun _ htransition => (hs htransition).elim)
  filter_upwards [hloanPos, hreservePos, hdepositPos, hloanCapEventually,
    hdepositCapEventually, hsolventEventually] with step hl hr hd hlcap hdcap hsolv
  refine ⟨hl.le, hr.le, hd.le, ?_, hdcap, hlcap, hsolv⟩
  nlinarith

theorem otcLiquidityPayoff_perturbation_eq
    (deficitSlope surplusSlope settlement direction kinkDirection step : ℝ)
    (hconcave : surplusSlope ≤ deficitSlope) (hstep : 0 < step)
    (hzeroDirection : settlement = 0 → direction = kinkDirection)
    (hnegative : settlement < 0 → settlement + step * direction < 0)
    (hpositive : 0 < settlement → 0 < settlement + step * direction) :
    otcLiquidityPayoff deficitSlope surplusSlope
        (settlement + step * direction) =
      otcLiquidityPayoff deficitSlope surplusSlope settlement + step *
        ((if settlement = 0 then 0
          else if settlement < 0 then deficitSlope else surplusSlope) * direction +
        if settlement = 0 then
          min (surplusSlope * kinkDirection) (deficitSlope * kinkDirection)
        else 0) := by
  by_cases hzero : settlement = 0
  · subst settlement
    have hdirection := hzeroDirection rfl
    rw [hdirection]
    rw [show 0 + step * kinkDirection = step * kinkDirection by ring]
    rw [otcLiquidityPayoff_scale deficitSlope surplusSlope kinkDirection step hstep]
    rw [otcLiquidityPayoff_eq_min surplusSlope deficitSlope kinkDirection hconcave]
    simp [otcLiquidityPayoff]
  · by_cases hnegativeBase : settlement < 0
    · have hnegativePerturbed := hnegative hnegativeBase
      simp [otcLiquidityPayoff, hzero, hnegativeBase, hnegativePerturbed]
      ring
    · have hpositiveBase : 0 < settlement := lt_of_le_of_ne
          (le_of_not_gt hnegativeBase) (Ne.symm hzero)
      have hpositivePerturbed := hpositive hpositiveBase
      have hnonnegativePerturbed : ¬ settlement + step * direction < 0 :=
        not_lt.mpr hpositivePerturbed.le
      simp [otcLiquidityPayoff, hzero, hnegativeBase, hnonnegativePerturbed]
      ring

theorem finiteSupportLiquidityPayoff_perturbation_eq
    {Ω : Type*} [DecidableEq Ω] (support : Finset Ω) (probability : Ω → ℝ)
    (settlement coefficient : Ω → ℝ)
    (deficitSlope surplusSlope u v commonCoefficient step : ℝ)
    (hconcave : surplusSlope ≤ deficitSlope)
    (hprobability : ∀ ω ∈ support, 0 ≤ probability ω)
    (hstep : 0 < step)
    (hzeroCoefficient : ∀ ω ∈ support, settlement ω = 0 →
      coefficient ω = commonCoefficient)
    (hnegative : ∀ ω ∈ support, settlement ω < 0 →
      settlement ω + step * (-u + coefficient ω * v) < 0)
    (hpositive : ∀ ω ∈ support, 0 < settlement ω →
      0 < settlement ω + step * (-u + coefficient ω * v)) :
    finiteSupportExpectation support probability (fun ω ↦
        otcLiquidityPayoff deficitSlope surplusSlope
          (settlement ω + step * (-u + coefficient ω * v))) =
      finiteSupportExpectation support probability (fun ω ↦
        otcLiquidityPayoff deficitSlope surplusSlope (settlement ω)) + step *
        (finiteSupportExpectation support probability (fun ω ↦
          (if settlement ω = 0 then 0
            else if settlement ω < 0 then deficitSlope else surplusSlope) *
              (-u + coefficient ω * v)) +
        min
          ((finiteSupportExpectation support probability (fun ω ↦
              if settlement ω = 0 then 1 else 0)) * surplusSlope *
            (-u + commonCoefficient * v))
          ((finiteSupportExpectation support probability (fun ω ↦
              if settlement ω = 0 then 1 else 0)) * deficitSlope *
            (-u + commonCoefficient * v))) := by
  let q := finiteSupportExpectation support probability (fun ω ↦
    if settlement ω = 0 then 1 else 0)
  let kinkTerm := min (surplusSlope * (-u + commonCoefficient * v))
    (deficitSlope * (-u + commonCoefficient * v))
  have hq : 0 ≤ q := by
    unfold q finiteSupportExpectation
    apply Finset.sum_nonneg
    intro ω hω
    exact mul_nonneg (hprobability ω hω) (by positivity)
  have hpoint : ∀ ω ∈ support,
      otcLiquidityPayoff deficitSlope surplusSlope
          (settlement ω + step * (-u + coefficient ω * v)) =
        otcLiquidityPayoff deficitSlope surplusSlope (settlement ω) + step *
          (((if settlement ω = 0 then 0
              else if settlement ω < 0 then deficitSlope else surplusSlope) *
                (-u + coefficient ω * v)) +
            if settlement ω = 0 then kinkTerm else 0) := by
    intro ω hω
    exact otcLiquidityPayoff_perturbation_eq deficitSlope surplusSlope
      (settlement ω) (-u + coefficient ω * v)
      (-u + commonCoefficient * v) step hconcave hstep
      (fun hz => by rw [hzeroCoefficient ω hω hz])
      (hnegative ω hω) (hpositive ω hω)
  have hsumKink :
      (∑ ω ∈ support, probability ω *
        (if settlement ω = 0 then kinkTerm else 0)) = q * kinkTerm := by
    unfold q finiteSupportExpectation
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro ω hω
    by_cases hz : settlement ω = 0 <;> simp [hz]
  have hsumDirection :
      (∑ ω ∈ support, probability ω * (step *
        (((if settlement ω = 0 then 0
            else if settlement ω < 0 then deficitSlope else surplusSlope) *
              (-u + coefficient ω * v)) +
          if settlement ω = 0 then kinkTerm else 0))) =
        step * ((∑ ω ∈ support, probability ω *
          ((if settlement ω = 0 then 0
            else if settlement ω < 0 then deficitSlope else surplusSlope) *
              (-u + coefficient ω * v))) + q * kinkTerm) := by
    calc
      _ = step * (∑ ω ∈ support, probability ω *
          (((if settlement ω = 0 then 0
              else if settlement ω < 0 then deficitSlope else surplusSlope) *
                (-u + coefficient ω * v)) +
            if settlement ω = 0 then kinkTerm else 0)) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro ω hω
          ring
      _ = step * ((∑ ω ∈ support, probability ω *
            ((if settlement ω = 0 then 0
              else if settlement ω < 0 then deficitSlope else surplusSlope) *
                (-u + coefficient ω * v))) +
          (∑ ω ∈ support, probability ω *
            (if settlement ω = 0 then kinkTerm else 0))) := by
          congr 1
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro ω hω
          ring
      _ = _ := by rw [hsumKink]
  have hscaledKink : q * kinkTerm =
      min (q * surplusSlope * (-u + commonCoefficient * v))
        (q * deficitSlope * (-u + commonCoefficient * v)) := by
    have hmin := mul_min_of_nonneg
      (surplusSlope * (-u + commonCoefficient * v))
      (deficitSlope * (-u + commonCoefficient * v)) hq
    dsimp [kinkTerm]
    rw [hmin]
    congr 1 <;> ring
  unfold finiteSupportExpectation
  calc
    (∑ ω ∈ support, probability ω *
        otcLiquidityPayoff deficitSlope surplusSlope
          (settlement ω + step * (-u + coefficient ω * v))) =
      ∑ ω ∈ support, probability ω *
        (otcLiquidityPayoff deficitSlope surplusSlope (settlement ω) + step *
          (((if settlement ω = 0 then 0
              else if settlement ω < 0 then deficitSlope else surplusSlope) *
                (-u + coefficient ω * v)) +
            if settlement ω = 0 then kinkTerm else 0)) := by
        apply Finset.sum_congr rfl
        intro ω hω
        rw [hpoint ω hω]
    _ = (∑ ω ∈ support, probability ω *
          otcLiquidityPayoff deficitSlope surplusSlope (settlement ω)) + step *
        ((∑ ω ∈ support, probability ω *
          ((if settlement ω = 0 then 0
            else if settlement ω < 0 then deficitSlope else surplusSlope) *
              (-u + coefficient ω * v))) + q * kinkTerm) := by
        rw [show (∑ ω ∈ support, probability ω *
            (otcLiquidityPayoff deficitSlope surplusSlope (settlement ω) +
              step * (((if settlement ω = 0 then 0
                else if settlement ω < 0 then deficitSlope else surplusSlope) *
                  (-u + coefficient ω * v)) +
                if settlement ω = 0 then kinkTerm else 0))) =
            (∑ ω ∈ support, probability ω *
              otcLiquidityPayoff deficitSlope surplusSlope (settlement ω)) +
            (∑ ω ∈ support, probability ω * (step *
              (((if settlement ω = 0 then 0
                else if settlement ω < 0 then deficitSlope else surplusSlope) *
                  (-u + coefficient ω * v)) +
                if settlement ω = 0 then kinkTerm else 0))) by
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro ω hω
          ring]
        rw [hsumDirection]
    _ = (∑ ω ∈ support, probability ω *
          otcLiquidityPayoff deficitSlope surplusSlope (settlement ω)) + step *
        ((∑ ω ∈ support, probability ω *
          ((if settlement ω = 0 then 0
            else if settlement ω < 0 then deficitSlope else surplusSlope) *
              (-u + coefficient ω * v))) +
          min (q * surplusSlope * (-u + commonCoefficient * v))
            (q * deficitSlope * (-u + commonCoefficient * v))) := by
        rw [hscaledKink]
    _ = _ := by rfl

theorem eventually_affine_preserves_sign_on_finset
    {Ω : Type*} [DecidableEq Ω] (support : Finset Ω)
    (base direction : Ω → ℝ) :
    ∀ᶠ (step : ℝ) in nhdsWithin 0 (Set.Ioi 0), ∀ ω ∈ support,
      (base ω < 0 → base ω + step * direction ω < 0) ∧
      (0 < base ω → 0 < base ω + step * direction ω) := by
  rw [eventually_all_finset]
  intro ω hω
  have hfilter : nhdsWithin (0 : ℝ) (Set.Ioi 0) ≤ nhds 0 := inf_le_left
  have hc : Continuous (fun step : ℝ => base ω + step * direction ω) := by
    fun_prop
  have ht := (hc.tendsto 0).mono_left hfilter
  have hnegative : ∀ᶠ (step : ℝ) in nhdsWithin 0 (Set.Ioi 0),
      base ω < 0 → base ω + step * direction ω < 0 := by
    by_cases hb : base ω < 0
    · have h0 : base ω + 0 * direction ω < 0 := by simpa using hb
      exact (ht.eventually (eventually_lt_nhds h0)).mono (fun _ hs _ => hs)
    · exact Filter.Eventually.of_forall (fun _ hs => (hb hs).elim)
  have hpositive : ∀ᶠ (step : ℝ) in nhdsWithin 0 (Set.Ioi 0),
      0 < base ω → 0 < base ω + step * direction ω := by
    by_cases hb : 0 < base ω
    · have h0 : 0 < base ω + 0 * direction ω := by simpa using hb
      exact (ht.eventually (eventually_gt_nhds h0)).mono (fun _ hs _ => hs)
    · exact Filter.Eventually.of_forall (fun _ hs => (hb hs).elim)
  exact hnegative.and hpositive

theorem finiteSupportSelectedMarginal_eq
    {Ω : Type*} [DecidableEq Ω] (support : Finset Ω)
    (probability : Ω → ℝ) (settlement : Ω → ℝ)
    (deficitSlope surplusSlope kinkSlope : ℝ) :
    finiteSupportExpectation support probability (fun ω ↦
        selectedOTCLiquidityMarginal deficitSlope surplusSlope kinkSlope
          (settlement ω)) =
      finiteSupportExpectation support probability (fun ω ↦
        if settlement ω = 0 then 0
        else if settlement ω < 0 then deficitSlope else surplusSlope) +
      finiteSupportExpectation support probability (fun ω ↦
        if settlement ω = 0 then 1 else 0) * kinkSlope := by
  unfold finiteSupportExpectation
  rw [Finset.sum_mul, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro ω hω
  by_cases hz : settlement ω = 0
  · simp [hz, selectedOTCLiquidityMarginal]
  · by_cases hn : settlement ω < 0
    · simp [hz, hn, selectedOTCLiquidityMarginal]
    · have hp : 0 < settlement ω := lt_of_le_of_ne (le_of_not_gt hn) (Ne.symm hz)
      simp [hz, hn, hp, selectedOTCLiquidityMarginal]

theorem finiteSupportSelectedMarginal_mul_coefficient_eq
    {Ω : Type*} [DecidableEq Ω] (support : Finset Ω)
    (probability : Ω → ℝ) (settlement coefficient : Ω → ℝ)
    (commonCoefficient deficitSlope surplusSlope kinkSlope : ℝ)
    (hzeroCoefficient : ∀ ω ∈ support, settlement ω = 0 →
      coefficient ω = commonCoefficient) :
    finiteSupportExpectation support probability (fun ω ↦
        selectedOTCLiquidityMarginal deficitSlope surplusSlope kinkSlope
          (settlement ω) * coefficient ω) =
      finiteSupportExpectation support probability (fun ω ↦
        (if settlement ω = 0 then 0
          else if settlement ω < 0 then deficitSlope else surplusSlope) *
            coefficient ω) +
      finiteSupportExpectation support probability (fun ω ↦
        if settlement ω = 0 then 1 else 0) * kinkSlope * commonCoefficient := by
  unfold finiteSupportExpectation
  rw [Finset.sum_mul, Finset.sum_mul, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro ω hω
  by_cases hz : settlement ω = 0
  · have hc := hzeroCoefficient ω hω hz
    simp [hz, hc, selectedOTCLiquidityMarginal]
    ring
  · by_cases hn : settlement ω < 0
    · simp [hz, hn, selectedOTCLiquidityMarginal]
    · have hp : 0 < settlement ω := lt_of_le_of_ne (le_of_not_gt hn) (Ne.symm hz)
      simp [hz, hn, hp, selectedOTCLiquidityMarginal]



/-- Once the single tie-consistent kink slope has been obtained from local
optimality, all pointwise supergradient, monotonicity, stationarity and cap-dual
clauses of the bank KKT system are algebraic consequences.  This lemma isolates
the remaining optimization seam without treating its scalar inequalities as a
source assumption. -/
theorem bankStaticKKTConditions_of_kinkSlope
    (P : Primitives S) (X : Allocation S) (t : ℕ) (h : History S t)
    (deficitSlope surplusSlope retainedEquity candidateLoans candidateReserves
      candidateDeposits kinkSlope : ℝ)
    (hconcave : surplusSlope ≤ deficitSlope)
    (hxi : P.reserveRequirementPath t h <
      X.depositRate t h / X.reserveRate t h)
    (hdeposits : 0 < candidateDeposits)
    (hkinkLower : surplusSlope ≤ kinkSlope)
    (hkinkUpper : kinkSlope ≤ deficitSlope)
    (hloanDual : 0 ≤ X.loanRate t h - X.reserveRate t h -
      finiteSupportExpectation P.paymentSupport P.paymentProbability (fun ω ↦
        selectedOTCLiquidityMarginal deficitSlope surplusSlope kinkSlope
          (bankSettlementSurplus candidateReserves
            (P.reserveRequirementPath t h)
            (X.depositRate t h / X.reserveRate t h) candidateDeposits
            (P.paymentShock ω))))
    (hdepositDual : 0 ≤
      finiteSupportExpectation P.paymentSupport P.paymentProbability (fun ω ↦
        selectedOTCLiquidityMarginal deficitSlope surplusSlope kinkSlope
            (bankSettlementSurplus candidateReserves
              (P.reserveRequirementPath t h)
              (X.depositRate t h / X.reserveRate t h) candidateDeposits
              (P.paymentShock ω)) *
          (1 - P.reserveRequirementPath t h +
            (X.depositRate t h / X.reserveRate t h -
              P.reserveRequirementPath t h) * P.paymentShock ω)) -
        (X.depositRate t h - X.reserveRate t h))
    (hloanComp :
      (X.loanRate t h - X.reserveRate t h -
        finiteSupportExpectation P.paymentSupport P.paymentProbability (fun ω ↦
          selectedOTCLiquidityMarginal deficitSlope surplusSlope kinkSlope
            (bankSettlementSurplus candidateReserves
              (P.reserveRequirementPath t h)
              (X.depositRate t h / X.reserveRate t h) candidateDeposits
              (P.paymentShock ω)))) *
        (P.bankLoanCap * retainedEquity - candidateLoans) = 0)
    (hdepositComp :
      (finiteSupportExpectation P.paymentSupport P.paymentProbability (fun ω ↦
          selectedOTCLiquidityMarginal deficitSlope surplusSlope kinkSlope
              (bankSettlementSurplus candidateReserves
                (P.reserveRequirementPath t h)
                (X.depositRate t h / X.reserveRate t h) candidateDeposits
                (P.paymentShock ω)) *
            (1 - P.reserveRequirementPath t h +
              (X.depositRate t h / X.reserveRate t h -
                P.reserveRequirementPath t h) * P.paymentShock ω)) -
          (X.depositRate t h - X.reserveRate t h)) *
        (P.bankDepositCap * retainedEquity - candidateDeposits) = 0) :
    ∃ (marginalLiquidity : BankPayment → ℝ) (loanCapDual depositCapDual : ℝ),
      BankStaticKKTConditionsAt P X t h deficitSlope surplusSlope retainedEquity
        candidateLoans candidateReserves candidateDeposits marginalLiquidity
        loanCapDual depositCapDual := by
  let marginalLiquidity : BankPayment → ℝ := fun ω ↦
    selectedOTCLiquidityMarginal deficitSlope surplusSlope kinkSlope
      (bankSettlementSurplus candidateReserves (P.reserveRequirementPath t h)
        (X.depositRate t h / X.reserveRate t h) candidateDeposits
        (P.paymentShock ω))
  let loanCapDual := X.loanRate t h - X.reserveRate t h -
    finiteSupportExpectation P.paymentSupport P.paymentProbability marginalLiquidity
  let depositCapDual :=
    finiteSupportExpectation P.paymentSupport P.paymentProbability (fun ω ↦
      marginalLiquidity ω *
        (1 - P.reserveRequirementPath t h +
          (X.depositRate t h / X.reserveRate t h -
            P.reserveRequirementPath t h) * P.paymentShock ω)) -
      (X.depositRate t h - X.reserveRate t h)
  refine ⟨marginalLiquidity, loanCapDual, depositCapDual, ?_⟩
  dsimp [BankStaticKKTConditionsAt]
  refine ⟨?_, ?_⟩
  · dsimp [BankStaticFOCConditionsAt]
    refine ⟨hloanDual, hdepositDual, ?_, ?_, ?_, hloanComp, hdepositComp⟩
    · intro ω hω
      exact selectedOTCLiquidityMarginal_isSupergradient hconcave hkinkLower hkinkUpper
    · dsimp [loanCapDual]
      ring
    · dsimp [depositCapDual]
      ring
  · intro ω hω ω' hω' hshock
    apply selectedOTCLiquidityMarginal_antitone hconcave hkinkLower hkinkUpper
    exact bankSettlementSurplus_mono_in_shock hxi hdeposits hshock

/-- OPEN helper: static optimality plus the explicit qualification should yield
the supergradient selection and both cap multipliers.  This is a genuine KKT
obligation, not a certificate field of the economic regime. -/
theorem bankStaticKKT_of_localOptimality
    (P : Primitives S) (X : Allocation S) (t : ℕ) (h : History S t)
    (deficitSlope surplusSlope retainedEquity candidateLoans candidateReserves
      candidateDeposits : ℝ)
    (hconcave : surplusSlope ≤ deficitSlope)
    (hxi : (P.reserveRequirementPath t h) < X.depositRate t h / X.reserveRate t h)
    (hfeasible : BankStaticPortfolioFeasibleAt P X t h deficitSlope surplusSlope
      retainedEquity candidateLoans candidateReserves candidateDeposits)
    (hinterior : 0 < candidateLoans ∧ 0 < candidateReserves ∧
      0 < candidateDeposits)
    (hstrictSolvency : ∀ ω ∈ P.paymentSupport, ∀ s,
      0 < P.tree.transition (currentState h) s →
      0 < bankRealPortfolioReturnAt P X t h deficitSlope surplusSlope
        candidateLoans candidateReserves candidateDeposits ω s)
    (hoptimal : BankStaticPortfolioOptimalAt P X t h deficitSlope surplusSlope
      retainedEquity candidateLoans candidateReserves candidateDeposits)
    (hqualification : BankStaticKKTConstraintQualificationAt P X t h
      deficitSlope surplusSlope retainedEquity) :
    ∃ (marginalLiquidity : BankPayment → ℝ) (loanCapDual depositCapDual : ℝ),
      BankStaticKKTConditionsAt P X t h deficitSlope surplusSlope retainedEquity
        candidateLoans candidateReserves candidateDeposits
        marginalLiquidity loanCapDual depositCapDual := by
  let rho := P.reserveRequirementPath t h
  let xi := X.depositRate t h / X.reserveRate t h
  let settlement : BankPayment → ℝ := fun ω ↦
    bankSettlementSurplus candidateReserves rho xi candidateDeposits
      (P.paymentShock ω)
  let coefficient : BankPayment → ℝ := fun ω ↦
    1 - rho + (xi - rho) * P.paymentShock ω
  let commonCoefficient := (candidateLoans - retainedEquity) / candidateDeposits
  let smoothMarginal : BankPayment → ℝ := fun ω ↦
    if settlement ω = 0 then 0
    else if settlement ω < 0 then deficitSlope else surplusSlope
  let kinkMass := finiteSupportExpectation P.paymentSupport P.paymentProbability
    (fun ω ↦ if settlement ω = 0 then 1 else 0)
  let loanCoefficient := X.loanRate t h - X.reserveRate t h -
    finiteSupportExpectation P.paymentSupport P.paymentProbability smoothMarginal
  let depositCoefficient := X.reserveRate t h - X.depositRate t h +
    finiteSupportExpectation P.paymentSupport P.paymentProbability
      (fun ω ↦ smoothMarginal ω * coefficient ω)
  let loanSlack := P.bankLoanCap * retainedEquity - candidateLoans
  let depositSlack := P.bankDepositCap * retainedEquity - candidateDeposits
  have hfeasibleParts := hfeasible
  rcases hfeasibleParts with ⟨_hloans, _hreserves, _hdeposits, hbalance,
    _hdepositCap, _hloanCap, _hsolvent⟩
  have hzeroCoefficient : ∀ ω ∈ P.paymentSupport, settlement ω = 0 →
      coefficient ω = commonCoefficient := by
    intro ω hω hzero
    exact bankSettlementSurplus_zero_directionCoefficient candidateLoans
      candidateReserves candidateDeposits retainedEquity rho xi
      (P.paymentShock ω) hbalance hinterior.2.2.ne' hzero
  have hdir : ∀ u v : ℝ,
      (loanSlack = 0 → u ≤ 0) → (depositSlack = 0 → v ≤ 0) →
      loanCoefficient * u + depositCoefficient * v +
        min ((kinkMass * surplusSlope) * (-u + commonCoefficient * v))
          ((kinkMass * deficitSlope) * (-u + commonCoefficient * v)) ≤ 0 := by
    intro u v hu hv
    have hfeasibleEventually :=
      eventually_bankStaticPortfolioFeasibleAt_perturbation P X t h
        deficitSlope surplusSlope retainedEquity candidateLoans candidateReserves
        candidateDeposits u v hconcave hfeasible hinterior hstrictSolvency
        (by simpa [loanSlack] using hu) (by simpa [depositSlack] using hv)
    have hsideEventually := eventually_affine_preserves_sign_on_finset
      P.paymentSupport settlement (fun ω ↦ -u + coefficient ω * v)
    have hpositiveStep : ∀ᶠ (step : ℝ) in nhdsWithin 0 (Set.Ioi 0),
        0 < step := self_mem_nhdsWithin
    have hall := hfeasibleEventually.and (hsideEventually.and hpositiveStep)
    rcases hall.exists with ⟨step, hstepFeasible, hstepSide, hstep⟩
    have hcomparison := hoptimal
      (candidateLoans + step * u)
      (candidateReserves + step * (v - u))
      (candidateDeposits + step * v) hstepFeasible
    have hliquidity := finiteSupportLiquidityPayoff_perturbation_eq
      P.paymentSupport P.paymentProbability settlement coefficient
      deficitSlope surplusSlope u v commonCoefficient step hconcave
      (fun ω hω ↦ (P.payment_probability_pos_on_support ω hω).le) hstep
      hzeroCoefficient
      (fun ω hω hs ↦ (hstepSide ω hω).1 hs)
      (fun ω hω hs ↦ (hstepSide ω hω).2 hs)
    have hsettlementPerturbation : ∀ ω,
        bankSettlementSurplus (candidateReserves + step * (v - u)) rho xi
            (candidateDeposits + step * v) (P.paymentShock ω) =
          settlement ω + step * (-u + coefficient ω * v) := by
      intro ω
      exact bankSettlementSurplus_portfolioPerturbation candidateReserves rho xi
        candidateDeposits (P.paymentShock ω) step u v
    have hliquidityModel :
        finiteSupportExpectation P.paymentSupport P.paymentProbability (fun ω ↦
          otcLiquidityPayoff deficitSlope surplusSlope
            (bankSettlementSurplus (candidateReserves + step * (v - u)) rho xi
              (candidateDeposits + step * v) (P.paymentShock ω))) =
        finiteSupportExpectation P.paymentSupport P.paymentProbability (fun ω ↦
          otcLiquidityPayoff deficitSlope surplusSlope (settlement ω)) + step *
          (finiteSupportExpectation P.paymentSupport P.paymentProbability (fun ω ↦
            smoothMarginal ω * (-u + coefficient ω * v)) +
          min ((kinkMass * surplusSlope) * (-u + commonCoefficient * v))
              ((kinkMass * deficitSlope) * (-u + commonCoefficient * v))) := by
      simpa only [hsettlementPerturbation, smoothMarginal, kinkMass] using hliquidity
    have hdirectionExpectation :
        finiteSupportExpectation P.paymentSupport P.paymentProbability (fun ω ↦
          smoothMarginal ω * (-u + coefficient ω * v)) =
        -u * finiteSupportExpectation P.paymentSupport P.paymentProbability
            smoothMarginal +
          v * finiteSupportExpectation P.paymentSupport P.paymentProbability
            (fun ω ↦ smoothMarginal ω * coefficient ω) := by
      calc
        _ = finiteSupportExpectation P.paymentSupport P.paymentProbability
            (fun ω ↦ (-u) * smoothMarginal ω +
              v * (smoothMarginal ω * coefficient ω)) := by
              apply congrArg (finiteSupportExpectation P.paymentSupport
                P.paymentProbability)
              funext ω
              ring
        _ = _ := by
              rw [finiteSupportExpectation_add,
                finiteSupportExpectation_const_mul,
                finiteSupportExpectation_const_mul]
    simp only [settlement, rho, xi] at hliquidityModel
    have hpayoffEquality :
        bankStaticPortfolioPayoffAt P X t h deficitSlope surplusSlope
            (candidateLoans + step * u)
            (candidateReserves + step * (v - u))
            (candidateDeposits + step * v) =
          bankStaticPortfolioPayoffAt P X t h deficitSlope surplusSlope
              candidateLoans candidateReserves candidateDeposits + step *
            (loanCoefficient * u + depositCoefficient * v +
              min ((kinkMass * surplusSlope) * (-u + commonCoefficient * v))
                ((kinkMass * deficitSlope) *
                  (-u + commonCoefficient * v))) := by
      unfold bankStaticPortfolioPayoffAt bankReducedPortfolioReturn
        bankReducedPortfolioReturnWithShock
      rw [finiteSupportExpectation_add, finiteSupportExpectation_add]
      rw [finiteSupportExpectation_const _ _ P.payment_probability_sum_one,
        finiteSupportExpectation_const _ _ P.payment_probability_sum_one]
      rw [hliquidityModel, hdirectionExpectation]
      unfold loanCoefficient depositCoefficient smoothMarginal coefficient
      ring
    rw [hpayoffEquality] at hcomparison
    nlinarith
  have hkinkMass : 0 ≤ kinkMass := by
    unfold kinkMass finiteSupportExpectation
    apply Finset.sum_nonneg
    intro ω hω
    exact mul_nonneg (P.payment_probability_pos_on_support ω hω).le (by positivity)
  have haggregatedSlopes : kinkMass * surplusSlope ≤ kinkMass * deficitSlope :=
    mul_le_mul_of_nonneg_left hconcave hkinkMass
  obtain ⟨aggregatedSlope, haggLower, haggUpper, hloanAgg, hdepositAgg,
      hloanCompAgg, hdepositCompAgg⟩ :=
    kinkSlope_of_noImprovingDirections (kinkMass * surplusSlope)
      (kinkMass * deficitSlope) loanCoefficient depositCoefficient
      commonCoefficient loanSlack depositSlack haggregatedSlopes hdir
  have hnormalized : ∃ kinkSlope : ℝ,
      surplusSlope ≤ kinkSlope ∧ kinkSlope ≤ deficitSlope ∧
      0 ≤ loanCoefficient - kinkMass * kinkSlope ∧
      0 ≤ depositCoefficient + commonCoefficient * (kinkMass * kinkSlope) ∧
      (loanCoefficient - kinkMass * kinkSlope) * loanSlack = 0 ∧
      (depositCoefficient + commonCoefficient * (kinkMass * kinkSlope)) *
        depositSlack = 0 := by
    by_cases hmassZero : kinkMass = 0
    · have haggZero : aggregatedSlope = 0 := by
        have hlower : 0 ≤ aggregatedSlope := by simpa [hmassZero] using haggLower
        have hupper : aggregatedSlope ≤ 0 := by simpa [hmassZero] using haggUpper
        exact le_antisymm hupper hlower
      refine ⟨surplusSlope, le_rfl, hconcave, ?_, ?_, ?_, ?_⟩
      · simpa [hmassZero, haggZero] using hloanAgg
      · simpa [hmassZero, haggZero] using hdepositAgg
      · simpa [hmassZero, haggZero] using hloanCompAgg
      · simpa [hmassZero, haggZero] using hdepositCompAgg
    · have hmassPositive : 0 < kinkMass := lt_of_le_of_ne hkinkMass (Ne.symm hmassZero)
      have hscale : kinkMass * (aggregatedSlope / kinkMass) = aggregatedSlope := by
        field_simp
      refine ⟨aggregatedSlope / kinkMass, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · apply (le_div_iff₀ hmassPositive).2
        nlinarith
      · apply (div_le_iff₀ hmassPositive).2
        nlinarith
      · rw [hscale]
        exact hloanAgg
      · rw [hscale]
        exact hdepositAgg
      · rw [hscale]
        exact hloanCompAgg
      · rw [hscale]
        exact hdepositCompAgg
  obtain ⟨kinkSlope, hkinkLower, hkinkUpper, hloanResidual,
    hdepositResidual, hloanComplementarity, hdepositComplementarity⟩ := hnormalized
  have hselected := finiteSupportSelectedMarginal_eq P.paymentSupport
    P.paymentProbability settlement deficitSlope surplusSlope kinkSlope
  have hselectedCoefficient :=
    finiteSupportSelectedMarginal_mul_coefficient_eq P.paymentSupport
      P.paymentProbability settlement coefficient commonCoefficient
      deficitSlope surplusSlope kinkSlope hzeroCoefficient
  have hselectedModel :
      finiteSupportExpectation P.paymentSupport P.paymentProbability (fun ω ↦
        selectedOTCLiquidityMarginal deficitSlope surplusSlope kinkSlope
          (bankSettlementSurplus candidateReserves
            (P.reserveRequirementPath t h)
            (X.depositRate t h / X.reserveRate t h) candidateDeposits
            (P.paymentShock ω))) =
        finiteSupportExpectation P.paymentSupport P.paymentProbability
          smoothMarginal + kinkMass * kinkSlope := by
    simpa only [settlement, rho, xi] using hselected
  have hselectedCoefficientModel :
      finiteSupportExpectation P.paymentSupport P.paymentProbability (fun ω ↦
        selectedOTCLiquidityMarginal deficitSlope surplusSlope kinkSlope
            (bankSettlementSurplus candidateReserves
              (P.reserveRequirementPath t h)
              (X.depositRate t h / X.reserveRate t h) candidateDeposits
              (P.paymentShock ω)) *
          (1 - P.reserveRequirementPath t h +
            (X.depositRate t h / X.reserveRate t h -
              P.reserveRequirementPath t h) * P.paymentShock ω)) =
        finiteSupportExpectation P.paymentSupport P.paymentProbability
          (fun ω ↦ smoothMarginal ω * coefficient ω) +
            kinkMass * kinkSlope * commonCoefficient := by
    simpa only [settlement, coefficient, rho, xi] using hselectedCoefficient
  apply bankStaticKKTConditions_of_kinkSlope P X t h deficitSlope surplusSlope
    retainedEquity candidateLoans candidateReserves candidateDeposits kinkSlope
    hconcave hxi hinterior.2.2 hkinkLower hkinkUpper
  · rw [hselectedModel]
    unfold loanCoefficient at hloanResidual
    linarith
  · rw [hselectedCoefficientModel]
    unfold depositCoefficient at hdepositResidual
    nlinarith
  · rw [hselectedModel]
    unfold loanCoefficient loanSlack at hloanComplementarity
    convert hloanComplementarity using 1 <;> ring
  · rw [hselectedCoefficientModel]
    unfold depositCoefficient depositSlack at hdepositComplementarity
    convert hdepositComplementarity using 1 <;> ring


/-- The source-facing Bellman reduction consumes finite attained dynamic value
and the exact continuation-policy problem; homogeneity is derived before the
OPEN Bellman-to-static helper is invoked. -/
theorem bankStaticPortfolioOptimal_of_dynamicBellman
    (P : Primitives S) (X : Allocation S) (p : BankPlan S)
    (t : ℕ) (h : History S t) (tightness : ℝ)
    (bankValue : BankValueProcess S)
    (hhomogeneous : BankValueHomogeneousAt P t h bankValue)
    (henvironment : BankBellmanLocalEnvironmentAt P X t h p tightness bankValue) :
    BankStaticPortfolioOptimalAt P X t h
      (bankOTCDeficitSlopeAt P X t h tightness)
      (bankOTCSurplusSlopeAt P X t h tightness)
      (p.retainedEquity t h) (p.loans t h) (p.reservesPre t h)
      (p.deposits t h) := by
  exact bankStaticPortfolioOptimal_of_bellman P X p t h tightness bankValue
    hhomogeneous henvironment

/-- KKT support with the source qualification discharged by the proved
reserves-only mixture lemma. -/
theorem bankStaticKKT_of_interior
    (P : Primitives S) (X : Allocation S) (t : ℕ) (h : History S t)
    (deficitSlope surplusSlope retainedEquity candidateLoans candidateReserves
      candidateDeposits : ℝ)
    (hreserveRate : 0 < X.reserveRate t h)
    (hsurplusSlope : 0 ≤ surplusSlope)
    (hconcave : surplusSlope ≤ deficitSlope)
    (hxi : (P.reserveRequirementPath t h) < X.depositRate t h / X.reserveRate t h)
    (hfeasible : BankStaticPortfolioFeasibleAt P X t h deficitSlope surplusSlope
      retainedEquity candidateLoans candidateReserves candidateDeposits)
    (hequity : 0 < retainedEquity)
    (hinterior : 0 < candidateLoans ∧ 0 < candidateReserves ∧
      0 < candidateDeposits)
    (hinflation : ∀ s, 0 < P.tree.transition (currentState h) s →
      0 < X.inflation (t + 1) (childHistory h s))
    (hstrictSolvency : ∀ ω ∈ P.paymentSupport, ∀ s,
      0 < P.tree.transition (currentState h) s →
      0 < bankRealPortfolioReturnAt P X t h deficitSlope surplusSlope
        candidateLoans candidateReserves candidateDeposits ω s)
    (hoptimal : BankStaticPortfolioOptimalAt P X t h deficitSlope surplusSlope
      retainedEquity candidateLoans candidateReserves candidateDeposits) :
    ∃ (marginalLiquidity : BankPayment → ℝ) (loanCapDual depositCapDual : ℝ),
      BankStaticKKTConditionsAt P X t h deficitSlope surplusSlope retainedEquity
        candidateLoans candidateReserves candidateDeposits
        marginalLiquidity loanCapDual depositCapDual := by
  apply bankStaticKKT_of_localOptimality P X t h deficitSlope surplusSlope
    retainedEquity candidateLoans candidateReserves candidateDeposits
    hconcave hxi hfeasible hinterior hstrictSolvency hoptimal
  exact bankStaticKKTConstraintQualification_of_interior P X t h deficitSlope
    surplusSlope retainedEquity candidateLoans candidateReserves candidateDeposits
    hreserveRate hsurplusSlope hconcave hfeasible hequity hinterior hinflation
    hstrictSolvency

/-- Support package for Proposition 3.8.  It is intentionally separate from
the exact Proposition Spec: kink supergradients, cap-dual signs and
complementarity, the covariance sign, and the two normalized FOCs are the
derivation of the displayed spread identity, not additional claims of the
numbered proposition. -/
def BankSpreadKKTSupportAt
    (P : Primitives S) (X : Allocation S) (t : ℕ) (h : History S t)
    (deficitSlope surplusSlope retainedEquity candidateLoans candidateReserves
      candidateDeposits : ℝ)
    (marginalLiquidity : BankPayment → ℝ)
    (loanCapDual depositCapDual : ℝ) : Prop :=
  BankStaticKKTConditionsAt P X t h deficitSlope surplusSlope retainedEquity
    candidateLoans candidateReserves candidateDeposits marginalLiquidity
    loanCapDual depositCapDual ∧
  finiteSupportCovariance P.paymentSupport P.paymentProbability
      marginalLiquidity P.paymentShock =
    finiteSupportExpectation P.paymentSupport P.paymentProbability
      (fun ω ↦ marginalLiquidity ω * P.paymentShock ω) ∧
  finiteSupportCovariance P.paymentSupport P.paymentProbability
      marginalLiquidity P.paymentShock ≤ 0 ∧
  finiteSupportExpectation P.paymentSupport P.paymentProbability
      (fun ω ↦ marginalLiquidity ω * P.paymentShock ω) ≤ 0 ∧
  X.loanRate t h - X.depositRate t h =
    (P.reserveRequirementPath t h) * finiteSupportExpectation P.paymentSupport
        P.paymentProbability marginalLiquidity -
      (X.depositRate t h / X.reserveRate t h - (P.reserveRequirementPath t h)) *
        finiteSupportExpectation P.paymentSupport P.paymentProbability
          (fun ω ↦ marginalLiquidity ω * P.paymentShock ω) +
      loanCapDual + depositCapDual

/-- Nonsmooth KKT/covariance bridge with all candidate feasibility,
interiority and strict-solvency hypotheses explicit. -/
theorem bankSpreadKKTSupport_of_interior
    (P : Primitives S) (X : Allocation S) (t : ℕ) (h : History S t)
    (deficitSlope surplusSlope retainedEquity candidateLoans candidateReserves
      candidateDeposits : ℝ)
    (hreserveRate : 0 < X.reserveRate t h)
    (hsurplusSlope : 0 ≤ surplusSlope)
    (hconcave : surplusSlope ≤ deficitSlope)
    (hxi : (P.reserveRequirementPath t h) < X.depositRate t h / X.reserveRate t h)
    (hfeasible : BankStaticPortfolioFeasibleAt P X t h deficitSlope surplusSlope
      retainedEquity candidateLoans candidateReserves candidateDeposits)
    (hequity : 0 < retainedEquity)
    (hinterior : 0 < candidateLoans ∧ 0 < candidateReserves ∧
      0 < candidateDeposits)
    (hinflation : ∀ s, 0 < P.tree.transition (currentState h) s →
      0 < X.inflation (t + 1) (childHistory h s))
    (hstrictSolvency : ∀ ω ∈ P.paymentSupport, ∀ s,
      0 < P.tree.transition (currentState h) s →
      0 < bankRealPortfolioReturnAt P X t h deficitSlope surplusSlope
        candidateLoans candidateReserves candidateDeposits ω s)
    (hoptimal : BankStaticPortfolioOptimalAt P X t h deficitSlope surplusSlope
      retainedEquity candidateLoans candidateReserves candidateDeposits) :
    ∃ (marginalLiquidity : BankPayment → ℝ) (loanCapDual depositCapDual : ℝ),
      BankSpreadKKTSupportAt P X t h deficitSlope surplusSlope retainedEquity
        candidateLoans candidateReserves candidateDeposits marginalLiquidity
        loanCapDual depositCapDual := by
  obtain ⟨_marginalLiquidity, _loanCapDual, _depositCapDual, _hstaticKKT⟩ :=
    bankStaticKKT_of_interior P X t h deficitSlope surplusSlope retainedEquity
      candidateLoans candidateReserves candidateDeposits hreserveRate
      hsurplusSlope hconcave hxi hfeasible hequity hinterior hinflation
      hstrictSolvency hoptimal
  refine ⟨_marginalLiquidity, _loanCapDual, _depositCapDual, _hstaticKKT, ?_, ?_,
    ?_, ?_⟩
  · have hshockMean : finiteSupportExpectation P.paymentSupport
        P.paymentProbability P.paymentShock = 0 := by
      simpa [finiteSupportExpectation] using P.payment_shock_mean_zero
    unfold finiteSupportCovariance
    rw [hshockMean, mul_zero, sub_zero]
  · have hkkt := _hstaticKKT
    dsimp [BankStaticKKTConditionsAt] at hkkt
    rcases hkkt with ⟨_, hmonotone⟩
    exact finiteSupportCovariance_nonpos_of_antitone P.paymentSupport
      P.paymentProbability _marginalLiquidity P.paymentShock
      (fun ω hω ↦ (P.payment_probability_pos_on_support ω hω).le)
      P.payment_probability_sum_one hmonotone
  · have hshockMean : finiteSupportExpectation P.paymentSupport
        P.paymentProbability P.paymentShock = 0 := by
      simpa [finiteSupportExpectation] using P.payment_shock_mean_zero
    have hcovariance : finiteSupportCovariance P.paymentSupport
        P.paymentProbability _marginalLiquidity P.paymentShock ≤ 0 := by
      have hkkt := _hstaticKKT
      dsimp [BankStaticKKTConditionsAt] at hkkt
      rcases hkkt with ⟨_, hmonotone⟩
      exact finiteSupportCovariance_nonpos_of_antitone P.paymentSupport
        P.paymentProbability _marginalLiquidity P.paymentShock
        (fun ω hω ↦ (P.payment_probability_pos_on_support ω hω).le)
        P.payment_probability_sum_one hmonotone
    unfold finiteSupportCovariance at hcovariance
    rw [hshockMean, mul_zero, sub_zero] at hcovariance
    exact hcovariance
  · have hkkt := _hstaticKKT
    dsimp [BankStaticKKTConditionsAt] at hkkt
    rcases hkkt with ⟨hfoc, _⟩
    dsimp [BankStaticFOCConditionsAt] at hfoc
    rcases hfoc with ⟨_, _, _, hloanFOC, hdepositFOC, _, _⟩
    have hexpectation :
        finiteSupportExpectation P.paymentSupport P.paymentProbability
            (fun ω ↦ _marginalLiquidity ω *
              (1 - P.reserveRequirementPath t h +
                (X.depositRate t h / X.reserveRate t h -
                  P.reserveRequirementPath t h) * P.paymentShock ω)) =
          (1 - P.reserveRequirementPath t h) *
              finiteSupportExpectation P.paymentSupport P.paymentProbability
                _marginalLiquidity +
            (X.depositRate t h / X.reserveRate t h -
              P.reserveRequirementPath t h) *
              finiteSupportExpectation P.paymentSupport P.paymentProbability
                (fun ω ↦ _marginalLiquidity ω * P.paymentShock ω) := by
      calc
        _ = finiteSupportExpectation P.paymentSupport P.paymentProbability
              (fun ω ↦
                (1 - P.reserveRequirementPath t h) * _marginalLiquidity ω +
                (X.depositRate t h / X.reserveRate t h -
                  P.reserveRequirementPath t h) *
                    (_marginalLiquidity ω * P.paymentShock ω)) := by
              apply congrArg (finiteSupportExpectation P.paymentSupport
                P.paymentProbability)
              funext ω
              ring
        _ = finiteSupportExpectation P.paymentSupport P.paymentProbability
              (fun ω ↦ (1 - P.reserveRequirementPath t h) *
                _marginalLiquidity ω) +
            finiteSupportExpectation P.paymentSupport P.paymentProbability
              (fun ω ↦ (X.depositRate t h / X.reserveRate t h -
                P.reserveRequirementPath t h) *
                  (_marginalLiquidity ω * P.paymentShock ω)) :=
              finiteSupportExpectation_add _ _ _ _
        _ = _ := by
              rw [finiteSupportExpectation_const_mul,
                finiteSupportExpectation_const_mul]
    rw [hexpectation] at hdepositFOC
    linarith

structure RetailerPlan (S : Type*) where
  logRelativePrice : AdaptedProcess S

def retailerPlanOfAllocation (X : Allocation S) : RetailerPlan S where
  logRelativePrice := X.retailerLogRelativePrice

def previousRetailLog (p : RetailerPlan S) :
    (t : ℕ) → History S t → ℝ
  | 0, _ => 0
  | t + 1, h => p.logRelativePrice t (previousHistory h)

noncomputable def retailerProfit (P : Primitives S) (X : Allocation S)
    (p : RetailerPlan S) (t : ℕ) (h : History S t) : ℝ :=
  let x := p.logRelativePrice t h
  let xp := previousRetailLog p t h
  X.output t h * (Real.exp ((1 - P.priceElasticity) * x) -
    X.inputPrice t h * Real.exp (-P.priceElasticity * x) -
    P.priceAdjustmentCost / 2 *
      (X.inflation t h * Real.exp (x - xp) - 1) ^ 2)

noncomputable def crraMarginal (sigma c : ℝ) : ℝ := c ^ (-sigma)

def rootHistory (T : FiniteMarkovTree S) : History S 0 := fun _ => T.initial

noncomputable def retailerPayoffTerm (P : Primitives S) (X : Allocation S)
    (p : RetailerPlan S) (t : ℕ) : ℝ :=
  P.workerDiscount ^ t * P.tree.expectationAt t (fun h ↦
    crraMarginal P.workerRiskAversion (X.workerConsumption t h) /
      crraMarginal P.workerRiskAversion
        (X.workerConsumption 0 (rootHistory P.tree)) * retailerProfit P X p t h)

def RetailObjectiveWellDefined (P : Primitives S) (X : Allocation S)
    (p : RetailerPlan S) : Prop := Summable (retailerPayoffTerm P X p)

noncomputable def RetailPayoff (P : Primitives S) (X : Allocation S)
    (p : RetailerPlan S) : ℝ := ∑' t, retailerPayoffTerm P X p t

def RetailOptimal (P : Primitives S) (X : Allocation S) : Prop :=
  let x := retailerPlanOfAllocation X
  RetailObjectiveWellDefined P X x ∧
    ∀ p, RetailObjectiveWellDefined P X p → RetailPayoff P X p ≤ RetailPayoff P X x

noncomputable def capitalCreationTechnology (P : Primitives S) (investment installed : ℝ) : ℝ :=
  investment + P.capitalAdjustmentCost * investment ^ 2 / (2 * installed)

def CapitalProducerOptimal (P : Primitives S) (X : Allocation S) : Prop :=
  (∀ t h, FirmHistoryAdmissible P t h →
    0 < X.aggregateCapital t h ∧ 0 ≤ X.investment t h ∧
    X.capitalCreationCost t h =
      capitalCreationTechnology P (X.investment t h) (X.aggregateCapital t h) ∧
    X.capitalProducerNetIncome t h =
      X.capitalPrice t h * X.investment t h - X.capitalCreationCost t h) ∧
  (∀ t h, FirmHistoryAdmissible P t h → ∀ (j : ℝ), 0 ≤ j →
    X.capitalPrice t h * j - capitalCreationTechnology P j (X.aggregateCapital t h) ≤
      X.capitalPrice t h * X.investment t h - X.capitalCreationCost t h)

/-- The entrepreneur budget and nominal-to-real wealth-flow identities used in
the aggregate-flow consolidation.  No collateral or optimality conclusion is
smuggled into this accounting premise. -/
def FirmBudgetFlows (P : Primitives S) (I : InheritedState)
    (X : Allocation S) : Prop :=
  (∀ i t h, FirmHistoryAdmissible P t h →
    X.firmConsumption i t h + X.capitalPrice t h * X.capital i t h +
        X.firmDeposit i t h = X.firmWealth i t h + X.loan i t h) ∧
  (∀ i h, FirmHistoryAdmissible P 0 h →
    X.firmWealth i 0 h =
      operatingProfit (X.inputPrice 0 h)
        (P.aggregateProductivity (currentState h) * P.productivity i) (I.capital i)
          (X.labor i 0 h) P.alpha P.beta (X.wage 0 h) +
        X.capitalPrice 0 h * (1 - P.depreciation) * I.capital i -
        realRepayment (I.firmFace i) (X.inflation 0 h)) ∧
  ∀ i t h s, FirmHistoryAdmissible P (t + 1) (childHistory h s) →
    X.firmWealth i (t + 1) (childHistory h s) =
      operatingProfit (X.inputPrice (t + 1) (childHistory h s))
          (P.aggregateProductivity s * P.productivity i) (X.capital i t h)
          (X.labor i (t + 1) (childHistory h s)) P.alpha P.beta
          (X.wage (t + 1) (childHistory h s)) +
        X.capitalPrice (t + 1) (childHistory h s) *
          (1 - P.depreciation) * X.capital i t h -
        realRepayment (X.firmFace i t h)
          (X.inflation (t + 1) (childHistory h s))

/-- The household's exact current and inherited nominal budget identities,
without adding positivity or an optimality premise. -/
def HouseholdBudgetFlows (P : Primitives S) (I : InheritedState)
    (X : Allocation S) : Prop :=
  (∀ h, FirmHistoryAdmissible P 0 h →
    X.workerConsumption 0 h + X.householdDeposits 0 h + X.householdBonds 0 h =
      X.wage 0 h * X.workerLabor 0 h +
      (I.depositRateLag * I.householdDeposits +
        I.governmentBondRateLag * I.householdBonds) / X.inflation 0 h +
      X.retailerNetIncome 0 h + X.capitalProducerNetIncome 0 h +
      X.bankNetIncome 0 h - X.tax 0 h) ∧
  ∀ t h s, FirmHistoryAdmissible P (t + 1) (childHistory h s) →
    X.workerConsumption (t + 1) (childHistory h s) +
        X.householdDeposits (t + 1) (childHistory h s) +
        X.householdBonds (t + 1) (childHistory h s) =
      X.wage (t + 1) (childHistory h s) *
          X.workerLabor (t + 1) (childHistory h s) +
      (X.depositRate t h * X.householdDeposits t h +
        X.governmentBondRate t h * X.householdBonds t h) /
          X.inflation (t + 1) (childHistory h s) +
      X.retailerNetIncome (t + 1) (childHistory h s) +
      X.capitalProducerNetIncome (t + 1) (childHistory h s) +
      X.bankNetIncome (t + 1) (childHistory h s) -
      X.tax (t + 1) (childHistory h s)

/-- Aggregate production uses predetermined installed capital: inherited
capital at date zero and the parent history's capital choice at a successor. -/
def AggregateProduction (P : Primitives S) (I : InheritedState)
    (X : Allocation S) : Prop :=
  (∀ h, FirmHistoryAdmissible P 0 h →
    X.output 0 h = ∑ i, P.mass i *
      operatingOutput
        (P.aggregateProductivity (currentState h) * P.productivity i)
        (I.capital i) (X.labor i 0 h)
        P.alpha P.beta) ∧
  ∀ t h s, FirmHistoryAdmissible P (t + 1) (childHistory h s) →
    X.output (t + 1) (childHistory h s) = ∑ i, P.mass i *
      operatingOutput (P.aggregateProductivity s * P.productivity i)
        (X.capital i t h)
        (X.labor i (t + 1) (childHistory h s)) P.alpha P.beta

/-- Capital-producer technology and ownership income used in the resource
consolidation.  The resource cost is literally the source's `Γ(I_t,K_t)`. -/
def CapitalProducerAccounts (P : Primitives S) (X : Allocation S) : Prop :=
  ∀ t h, FirmHistoryAdmissible P t h →
    0 < X.aggregateCapital t h ∧ 0 ≤ X.investment t h ∧
    X.capitalCreationCost t h =
      capitalCreationTechnology P (X.investment t h) (X.aggregateCapital t h) ∧
    X.capitalProducerNetIncome t h =
      X.capitalPrice t h * X.investment t h - X.capitalCreationCost t h

def AccountingIdentities (P : Primitives S) (X : Allocation S) : Prop :=
  (∀ t h, FirmHistoryAdmissible P t h →
    X.priceAdjustmentResourceCost t h =
      P.priceAdjustmentCost / 2 * (X.inflation t h - 1) ^ 2 * X.output t h) ∧
  ∀ t h, FirmHistoryAdmissible P t h →
    X.retailerNetIncome t h =
      (1 - X.inputPrice t h) * X.output t h - X.priceAdjustmentResourceCost t h

/-! ### Source fiscal residual completion -/

/-- Central-bank bond holdings prescribed by the source balance-sheet
identity. -/
noncomputable def sourceFiscalCentralBankBonds
    (X : Allocation S) : AdaptedProcess S :=
  X.reservesPrePayment

/-- Household government-bond holdings are the residual supply after the
central bank holds the reserves-backed portion. -/
noncomputable def sourceFiscalHouseholdBonds
    (P : Primitives S) (X : Allocation S) : AdaptedProcess S :=
  fun t h ↦ P.governmentBondSupply - X.reservesPrePayment t h

/-- Taxes obtained by solving the literal consolidated fiscal budget at each
history.  Date zero uses inherited nominal claims; positive dates use the
parent history's rates and positions. -/
noncomputable def sourceFiscalTax
    (P : Primitives S) (I : InheritedState) (X : Allocation S) : AdaptedProcess S
  | 0, h =>
      (I.governmentBondRateLag * I.householdBonds +
          I.reserveRateLag * I.reservesLag -
          I.facilityRateLag * I.facilityBorrowingLag) / X.inflation 0 h -
        sourceFiscalHouseholdBonds P X 0 h -
        X.reservesPostPayment 0 h + X.facilityBorrowing 0 h
  | t + 1, h =>
      let hp := previousHistory h
      (X.governmentBondRate t hp * sourceFiscalHouseholdBonds P X t hp +
          X.reserveRate t hp * X.reservesPostPayment t hp -
          X.facilityRate t hp * X.facilityBorrowing t hp) /
            X.inflation (t + 1) h -
        sourceFiscalHouseholdBonds P X (t + 1) h -
        X.reservesPostPayment (t + 1) h +
        X.facilityBorrowing (t + 1) h

/-- Construct the three omitted fiscal fields while preserving every real,
firm, bank and price field of the supplied partial allocation.  This is a
literal source residual construction, not an equilibrium or optimality
certificate. -/
noncomputable def withSourceFiscalAccounts
    (P : Primitives S) (I : InheritedState) (X : Allocation S) : Allocation S :=
  { X with
    householdBonds := sourceFiscalHouseholdBonds P X
    centralBankBonds := sourceFiscalCentralBankBonds X
    tax := sourceFiscalTax P I X }

/-- Household-budget compatibility after eliminating taxes and government
bonds with the source fiscal identities.  This displays the remaining flow
equation rather than hiding it in an assumed household-feasibility record. -/
def SourceFiscalHouseholdCompatibility
    (P : Primitives S) (I : InheritedState) (X : Allocation S) : Prop :=
  (∀ h, FirmHistoryAdmissible P 0 h →
    X.workerConsumption 0 h + X.householdDeposits 0 h =
      X.wage 0 h * X.workerLabor 0 h +
      I.depositRateLag * I.householdDeposits / X.inflation 0 h +
      X.retailerNetIncome 0 h + X.capitalProducerNetIncome 0 h +
      X.bankNetIncome 0 h -
      (I.reserveRateLag * I.reservesLag -
        I.facilityRateLag * I.facilityBorrowingLag) / X.inflation 0 h +
      X.reservesPostPayment 0 h - X.facilityBorrowing 0 h) ∧
  ∀ t h s, FirmHistoryAdmissible P (t + 1) (childHistory h s) →
    X.workerConsumption (t + 1) (childHistory h s) +
        X.householdDeposits (t + 1) (childHistory h s) =
      X.wage (t + 1) (childHistory h s) *
          X.workerLabor (t + 1) (childHistory h s) +
      X.depositRate t h * X.householdDeposits t h /
          X.inflation (t + 1) (childHistory h s) +
      X.retailerNetIncome (t + 1) (childHistory h s) +
      X.capitalProducerNetIncome (t + 1) (childHistory h s) +
      X.bankNetIncome (t + 1) (childHistory h s) -
      (X.reserveRate t h * X.reservesPostPayment t h -
        X.facilityRate t h * X.facilityBorrowing t h) /
          X.inflation (t + 1) (childHistory h s) +
      X.reservesPostPayment (t + 1) (childHistory h s) -
      X.facilityBorrowing (t + 1) (childHistory h s)

/-- Settlement clearing supplies the one remaining central-bank balance
identity, so the residual construction satisfies every clause of literal
`FiscalClosure`. -/
theorem withSourceFiscalAccounts_fiscalClosure
    (P : Primitives S) (I : InheritedState) (X : Allocation S)
    (hsettlement : SettlementClears P X) :
    FiscalClosure P I (withSourceFiscalAccounts P I X) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro t h _hs
    simp [withSourceFiscalAccounts, sourceFiscalHouseholdBonds,
      sourceFiscalCentralBankBonds]
  · intro t h _hs
    rfl
  · intro t h hs
    rcases hsettlement t h hs with ⟨hinterbank, _hfacility, hpost⟩
    simp only [withSourceFiscalAccounts, sourceFiscalCentralBankBonds,
      expectedFacilityBorrowing, expectedPostReserves]
    rw [hinterbank] at hpost
    linarith
  · intro h _hs
    simp [withSourceFiscalAccounts, sourceFiscalTax,
      sourceFiscalHouseholdBonds, expectedFacilityBorrowing,
      expectedPostReserves]
    ring
  · intro t h s _hs
    have hprevious : previousHistory (childHistory h s) = h := by
      rfl
    simp [withSourceFiscalAccounts, sourceFiscalTax,
      sourceFiscalHouseholdBonds, expectedFacilityBorrowing,
      expectedPostReserves, hprevious]
    ring

/-- Substituting the source fiscal residuals into the literal household budget
is equivalent to the displayed tax/bond-free compatibility equation. -/
theorem householdBudgetFlows_withSourceFiscalAccounts_iff
    (P : Primitives S) (I : InheritedState) (X : Allocation S) :
    HouseholdBudgetFlows P I (withSourceFiscalAccounts P I X) ↔
      SourceFiscalHouseholdCompatibility P I X := by
  constructor
  · rintro ⟨hzero, hsucc⟩
    constructor
    · intro h hs
      have hbudget := hzero h hs
      simp only [withSourceFiscalAccounts, sourceFiscalHouseholdBonds,
        sourceFiscalTax] at hbudget
      linear_combination hbudget
    · intro t h s hs
      have hbudget := hsucc t h s hs
      have hprevious : previousHistory (childHistory h s) = h := by rfl
      simp only [withSourceFiscalAccounts, sourceFiscalHouseholdBonds,
        sourceFiscalTax, hprevious] at hbudget
      linear_combination hbudget
  · rintro ⟨hzero, hsucc⟩
    constructor
    · intro h hs
      have hcompat := hzero h hs
      simp only [withSourceFiscalAccounts, sourceFiscalHouseholdBonds,
        sourceFiscalTax]
      linear_combination hcompat
    · intro t h s hs
      have hcompat := hsucc t h s hs
      have hprevious : previousHistory (childHistory h s) = h := by rfl
      simp only [withSourceFiscalAccounts, sourceFiscalHouseholdBonds,
        sourceFiscalTax, hprevious]
      linear_combination hcompat

theorem withSourceFiscalAccounts_preserves_firmBudgetFlows
    (P : Primitives S) (I : InheritedState) (X : Allocation S) :
    FirmBudgetFlows P I (withSourceFiscalAccounts P I X) ↔
      FirmBudgetFlows P I X := by
  rfl

theorem withSourceFiscalAccounts_preserves_resourceClears
    (P : Primitives S) (I : InheritedState) (X : Allocation S) :
    ResourceClears P (withSourceFiscalAccounts P I X) ↔
      ResourceClears P X := by
  rfl

theorem withSourceFiscalAccounts_preserves_accountingIdentities
    (P : Primitives S) (I : InheritedState) (X : Allocation S) :
    AccountingIdentities P (withSourceFiscalAccounts P I X) ↔
      AccountingIdentities P X := by
  rfl

theorem withSourceFiscalAccounts_preserves_capitalProducerAccounts
    (P : Primitives S) (I : InheritedState) (X : Allocation S) :
    CapitalProducerAccounts P (withSourceFiscalAccounts P I X) ↔
      CapitalProducerAccounts P X := by
  rfl

/-! ### Source real-account residual completion -/

/-- Installed aggregate capital implied by inherited date-zero capital and by
the parent history's firm capital choices thereafter. -/
noncomputable def sourceAggregateCapital
    (P : Primitives S) (I : InheritedState) (X : Allocation S) : AdaptedProcess S
  | 0, _h => ∑ i, P.mass i * I.capital i
  | t + 1, h => ∑ i, P.mass i * X.capital i t (previousHistory h)

/-- Aggregate production evaluated from the literal installed capitals and
current labor choices. -/
noncomputable def sourceAggregateOutput
    (P : Primitives S) (I : InheritedState) (X : Allocation S) : AdaptedProcess S
  | 0, h => ∑ i, P.mass i * operatingOutput
      (P.aggregateProductivity (currentState h) * P.productivity i)
      (I.capital i) (X.labor i 0 h) P.alpha P.beta
  | t + 1, h => ∑ i, P.mass i * operatingOutput
      (P.aggregateProductivity (currentState h) * P.productivity i)
      (X.capital i t (previousHistory h)) (X.labor i (t + 1) h)
      P.alpha P.beta

/-- Investment is the residual of the literal aggregate capital law. -/
noncomputable def sourceInvestment
    (P : Primitives S) (I : InheritedState) (X : Allocation S) : AdaptedProcess S :=
  fun t h ↦ ∑ i, P.mass i * X.capital i t h -
    (1 - P.depreciation) * sourceAggregateCapital P I X t h

noncomputable def sourceCapitalCreationCost
    (P : Primitives S) (I : InheritedState) (X : Allocation S) : AdaptedProcess S :=
  fun t h ↦ capitalCreationTechnology P (sourceInvestment P I X t h)
    (sourceAggregateCapital P I X t h)

noncomputable def sourcePriceAdjustmentResourceCost
    (P : Primitives S) (I : InheritedState) (X : Allocation S) : AdaptedProcess S :=
  fun t h ↦ P.priceAdjustmentCost / 2 * (X.inflation t h - 1) ^ 2 *
    sourceAggregateOutput P I X t h

noncomputable def sourceCapitalProducerNetIncome
    (P : Primitives S) (I : InheritedState) (X : Allocation S) : AdaptedProcess S :=
  fun t h ↦ X.capitalPrice t h * sourceInvestment P I X t h -
    sourceCapitalCreationCost P I X t h

noncomputable def sourceRetailerNetIncome
    (P : Primitives S) (I : InheritedState) (X : Allocation S) : AdaptedProcess S :=
  fun t h ↦ (1 - X.inputPrice t h) * sourceAggregateOutput P I X t h -
    sourcePriceAdjustmentResourceCost P I X t h

/-- Fill the aggregate real-account fields from source production, capital,
adjustment-cost and ownership-income identities while preserving the supplied
private controls and prices. -/
noncomputable def withSourceRealAccounts
    (P : Primitives S) (I : InheritedState) (X : Allocation S) : Allocation S :=
  { X with
    aggregateCapital := sourceAggregateCapital P I X
    output := sourceAggregateOutput P I X
    investment := sourceInvestment P I X
    capitalCreationCost := sourceCapitalCreationCost P I X
    priceAdjustmentResourceCost := sourcePriceAdjustmentResourceCost P I X
    capitalProducerNetIncome := sourceCapitalProducerNetIncome P I X
    retailerNetIncome := sourceRetailerNetIncome P I X }

theorem withSourceRealAccounts_aggregateProduction
    (P : Primitives S) (I : InheritedState) (X : Allocation S) :
    AggregateProduction P I (withSourceRealAccounts P I X) := by
  constructor
  · intro h _hs
    rfl
  · intro t h s _hs
    rfl

theorem withSourceRealAccounts_capitalClears
    (P : Primitives S) (I : InheritedState) (X : Allocation S) :
    CapitalClears P I (withSourceRealAccounts P I X) := by
  refine ⟨?_, ?_, ?_⟩
  · intro h _hs
    rfl
  · intro t h s _hs
    rfl
  · intro t h _hs
    simp only [withSourceRealAccounts, sourceInvestment]
    ring

theorem withSourceRealAccounts_accountingIdentities
    (P : Primitives S) (I : InheritedState) (X : Allocation S) :
    AccountingIdentities P (withSourceRealAccounts P I X) := by
  constructor <;> intro t h _hs <;> rfl

/-- The exact resource equation left after the real-account fields are filled.
For the finite prefix this is the economic content of the named reduced
resource rows. -/
def SourceRealResourceCompatibility
    (P : Primitives S) (I : InheritedState) (X : Allocation S) : Prop :=
  ∀ t h, FirmHistoryAdmissible P t h →
    X.workerConsumption t h + ∑ i, P.mass i * X.firmConsumption i t h +
      sourceCapitalCreationCost P I X t h +
      sourcePriceAdjustmentResourceCost P I X t h =
    sourceAggregateOutput P I X t h

theorem resourceClears_withSourceRealAccounts_iff
    (P : Primitives S) (I : InheritedState) (X : Allocation S) :
    ResourceClears P (withSourceRealAccounts P I X) ↔
      SourceRealResourceCompatibility P I X := by
  rfl

theorem withSourceRealAccounts_capitalProducerAccounts
    (P : Primitives S) (I : InheritedState) (X : Allocation S)
    (hcapital : ∀ t h, FirmHistoryAdmissible P t h →
      0 < sourceAggregateCapital P I X t h)
    (hinvestment : ∀ t h, FirmHistoryAdmissible P t h →
      0 ≤ sourceInvestment P I X t h) :
    CapitalProducerAccounts P (withSourceRealAccounts P I X) := by
  intro t h hs
  exact ⟨hcapital t h hs, hinvestment t h hs, rfl, rfl⟩

/-- Compose the real and fiscal residual constructions.  This is the concrete
source accounting completion used by the branch reconstruction; it still
requires the private controls/prices and bank settlement fields supplied by
the reduced-to-literal map. -/
noncomputable def withSourceAccountingCompletion
    (P : Primitives S) (I : InheritedState) (X : Allocation S) : Allocation S :=
  withSourceFiscalAccounts P I (withSourceRealAccounts P I X)

theorem withSourceAccountingCompletion_fiscalClosure
    (P : Primitives S) (I : InheritedState) (X : Allocation S)
    (hsettlement : SettlementClears P X) :
    FiscalClosure P I (withSourceAccountingCompletion P I X) := by
  apply withSourceFiscalAccounts_fiscalClosure
  simpa [withSourceRealAccounts] using hsettlement

theorem resourceClears_withSourceAccountingCompletion_iff
    (P : Primitives S) (I : InheritedState) (X : Allocation S) :
    ResourceClears P (withSourceAccountingCompletion P I X) ↔
      SourceRealResourceCompatibility P I X := by
  rw [withSourceAccountingCompletion,
    withSourceFiscalAccounts_preserves_resourceClears,
    resourceClears_withSourceRealAccounts_iff]

theorem householdBudgetFlows_withSourceAccountingCompletion_iff
    (P : Primitives S) (I : InheritedState) (X : Allocation S) :
    HouseholdBudgetFlows P I (withSourceAccountingCompletion P I X) ↔
      SourceFiscalHouseholdCompatibility P I
        (withSourceRealAccounts P I X) := by
  exact householdBudgetFlows_withSourceFiscalAccounts_iff P I
    (withSourceRealAccounts P I X)

theorem sum_firmType_eq_H_add_L (f : FirmType → ℝ) :
    (∑ i, f i) = f .H + f .L := by
  rw [show (Finset.univ : Finset FirmType) = {.H, .L} by
    ext i
    cases i <;> simp]
  simp

/-- Retained bank equity plus current owner income exhausts pre-exit equity.
This is the exact exit/seed cancellation used in household-flow
consolidation, not an optimality statement. -/
theorem bankRetainedEquity_add_bankNetIncome_eq_preExit
    (P : Primitives S) (I : InheritedState) (X : Allocation S)
    (hrenewal : BankRenewalFlows P I X) :
    ∀ t h, FirmHistoryAdmissible P t h →
      X.bankRetainedEquity t h + X.bankNetIncome t h =
        bankPreExitEquity P I X t h := by
  intro t h hs
  rcases hrenewal with ⟨hretained, hequity, hnet⟩
  rw [hretained t h hs, hnet t h hs, hequity t h hs]
  simp only [bankRenewalFactor]
  ring

/-- The predecessor's household deposit return net of reserve/facility flows
equals aggregate firm faces net of the aggregate bank gross return. -/
theorem currentHouseholdFinancialFaceIdentity
    (P : Primitives S) (X : Allocation S)
    (hfaces : CurrentNominalFaceConsistency P X)
    (hcredit : CreditClears P X)
    (hdeposits : DepositsClear P X)
    (hsettlement : SettlementClears P X) :
    ∀ t h, FirmHistoryAdmissible P t h →
      X.depositRate t h * X.householdDeposits t h -
          X.reserveRate t h * X.reservesPostPayment t h +
          X.facilityRate t h * X.facilityBorrowing t h =
        (∑ i, P.mass i * X.firmFace i t h) -
          aggregateBankGrossReturn P X t h := by
  intro t h hs
  have hfaceH := hfaces .H t h hs
  have hfaceL := hfaces .L t h hs
  have hfaceHmass := congrArg (fun y : ℝ ↦ P.mass .H * y) hfaceH
  have hfaceLmass := congrArg (fun y : ℝ ↦ P.mass .L * y) hfaceL
  have hcredit' := hcredit t h hs
  have hdeposits' := hdeposits t h hs
  rcases hsettlement t h hs with ⟨hinterbank, _hfacility, _hpost⟩
  rw [sum_firmType_eq_H_add_L] at hcredit' hdeposits' ⊢
  have hcreditRate := congrArg (fun y : ℝ ↦ X.loanRate t h * y) hcredit'
  have hdepositRate := congrArg (fun y : ℝ ↦ X.depositRate t h * y) hdeposits'
  simp only [aggregateBankGrossReturn]
  rw [hinterbank]
  ring_nf at hfaceHmass hfaceLmass hcreditRate hdepositRate ⊢
  linarith

/-- Reconstruct every inherited real and financial position from one literal
parent history.  The inherited bank face is the nominal renewal face generated
by the parent's aggregate portfolio return; household public bonds are the
source fiscal residual, not an independently chosen initial condition. -/
noncomputable def sourcePredecessorStateAt
    (P : Primitives S) (X : Allocation S) (t : ℕ) (h : History S t) :
    InheritedState where
  capital := fun i ↦ X.capital i t h
  firmFace := fun i ↦ X.firmFace i t h
  bankFace := bankRenewalFactor P * aggregateBankGrossReturn P X t h
  householdDeposits := X.householdDeposits t h
  householdBonds := sourceFiscalHouseholdBonds P X t h
  depositRateLag := X.depositRate t h
  governmentBondRateLag := X.governmentBondRate t h
  reserveRateLag := X.reserveRate t h
  reservesPreLag := X.reservesPrePayment t h
  reservesLag := X.reservesPostPayment t h
  facilityRateLag := X.facilityRate t h
  facilityBorrowingLag := X.facilityBorrowing t h

/-- The reconstructed predecessor inherits the literal public-bond split and
post-payment settlement at its parent history.  Nonnegative household bonds
are exposed as the exact source condition `M^{pre} <= G`, not manufactured by
the constructor. -/
theorem sourcePredecessorStateAt_financialClosure
    (P : Primitives S) (X : Allocation S) (t : ℕ) (h : History S t)
    (hs : FirmHistoryAdmissible P t h)
    (hsettlement : SettlementClears P X)
    (hbonds : X.reservesPrePayment t h ≤ P.governmentBondSupply) :
    let I := sourcePredecessorStateAt P X t h
    0 ≤ I.householdBonds ∧
      0 ≤ I.facilityBorrowingLag ∧
      I.reservesLag = I.reservesPreLag + I.facilityBorrowingLag ∧
      I.householdBonds + I.reservesPreLag = P.governmentBondSupply := by
  dsimp only
  rcases hsettlement t h hs with ⟨hinterbank, hfacility, hpost⟩
  dsimp [sourcePredecessorStateAt, sourceFiscalHouseholdBonds]
  constructor
  · linarith
  constructor
  · exact hfacility
  constructor
  · linarith
  · ring

/-- Current face clearing makes the reconstructed parent a consistent
pre-date-zero financial state.  This derives, rather than assumes, the source
nominal-face identity used by the date-zero household cancellation. -/
theorem sourcePredecessorStateAt_nominalFaceConsistency
    (P : Primitives S) (X : Allocation S) (t : ℕ) (h : History S t)
    (hs : FirmHistoryAdmissible P t h)
    (hrenewal : 0 < bankRenewalFactor P)
    (hfaces : CurrentNominalFaceConsistency P X)
    (hcredit : CreditClears P X)
    (hdeposits : DepositsClear P X)
    (hsettlement : SettlementClears P X) :
    InheritedNominalFaceConsistency P (sourcePredecessorStateAt P X t h) := by
  constructor
  · exact hrenewal
  · have hfinancial := currentHouseholdFinancialFaceIdentity P X hfaces
      hcredit hdeposits hsettlement t h hs
    dsimp [sourcePredecessorStateAt]
    rw [mul_div_cancel_left₀ _ (ne_of_gt hrenewal)]
    linarith

/-- Date-zero household compatibility from inherited faces and the literal
source accounts.  Current-face consistency is deliberately absent: date zero
uses the pinned predecessor faces instead. -/
theorem sourceFiscalHouseholdCompatibility_zero_of_source_flows
    (P : Primitives S) (I : InheritedState) (X : Allocation S)
    (hfirm : FirmBudgetFlows P I X)
    (hproduction : AggregateProduction P I X)
    (hcapitalProducer : CapitalProducerAccounts P X)
    (haccounting : AccountingIdentities P X)
    (hresource : ResourceClears P X)
    (hcredit : CreditClears P X)
    (hdeposits : DepositsClear P X)
    (hcapital : CapitalClears P I X)
    (hlabor : LaborClears P X)
    (hbankBalance : BankBalance P X)
    (hsettlement : SettlementClears P X)
    (hrenewal : BankRenewalFlows P I X)
    (hinheritedFaces : InheritedNominalFaceConsistency P I) :
    ∀ h, FirmHistoryAdmissible P 0 h →
      X.workerConsumption 0 h + X.householdDeposits 0 h =
        X.wage 0 h * X.workerLabor 0 h +
        I.depositRateLag * I.householdDeposits / X.inflation 0 h +
        X.retailerNetIncome 0 h + X.capitalProducerNetIncome 0 h +
        X.bankNetIncome 0 h -
        (I.reserveRateLag * I.reservesLag -
          I.facilityRateLag * I.facilityBorrowingLag) / X.inflation 0 h +
        X.reservesPostPayment 0 h - X.facilityBorrowing 0 h := by
  intro h hs
  have hbudgetH := hfirm.1 .H 0 h hs
  have hbudgetL := hfirm.1 .L 0 h hs
  have hwealthH := hfirm.2.1 .H h hs
  have hwealthL := hfirm.2.1 .L h hs
  have hbudgetHmass := congrArg (fun y : ℝ ↦ P.mass .H * y) hbudgetH
  have hbudgetLmass := congrArg (fun y : ℝ ↦ P.mass .L * y) hbudgetL
  have hwealthHmass := congrArg (fun y : ℝ ↦ P.mass .H * y) hwealthH
  have hwealthLmass := congrArg (fun y : ℝ ↦ P.mass .L * y) hwealthL
  have hproduction' := hproduction.1 h hs
  have hproductionPrice :=
    congrArg (fun y : ℝ ↦ X.inputPrice 0 h * y) hproduction'
  have hlabor' := hlabor 0 h hs
  have hlaborWage := congrArg (fun y : ℝ ↦ X.wage 0 h * y) hlabor'
  have hcapitalInitial := hcapital.1 h hs
  have hcapitalInitialScaled := congrArg
    (fun y : ℝ ↦ (1 - P.depreciation) * y) hcapitalInitial
  have hcapitalLaw := hcapital.2.2 0 h hs
  rw [sum_firmType_eq_H_add_L] at hcapitalInitialScaled hcapitalLaw
  have hcapitalCombined :
      (∑ i, P.mass i * X.capital i 0 h) =
        (1 - P.depreciation) * (∑ i, P.mass i * I.capital i) +
          X.investment 0 h := by
    rw [sum_firmType_eq_H_add_L, sum_firmType_eq_H_add_L]
    ring_nf at hcapitalInitialScaled hcapitalLaw ⊢
    linarith
  have hcapitalPrice :=
    congrArg (fun y : ℝ ↦ X.capitalPrice 0 h * y) hcapitalCombined
  have hresource' := hresource 0 h hs
  have hcredit' := hcredit 0 h hs
  have hdeposits' := hdeposits 0 h hs
  have hbankBalance' := hbankBalance 0 h hs
  rcases hsettlement 0 h hs with
    ⟨hinterbank, _hfacilityNonneg, hsettlement'⟩
  have hbankRenewal :=
    bankRetainedEquity_add_bankNetIncome_eq_preExit P I X hrenewal 0 h hs
  have hinheritedReal := congrArg
    (fun y : ℝ ↦ y / X.inflation 0 h) hinheritedFaces.2
  have hretailer := haccounting.2 0 h hs
  rcases hcapitalProducer 0 h hs with
    ⟨_hcapitalPositive, _hinvestmentNonneg, _hcreation, hcapitalIncome⟩
  rw [sum_firmType_eq_H_add_L] at hproductionPrice hlaborWage hresource' hcredit' hdeposits' hinheritedReal
  rw [sum_firmType_eq_H_add_L, sum_firmType_eq_H_add_L] at hcapitalPrice
  simp only [bankPreExitEquity] at hbankRenewal
  dsimp [operatingProfit, realRepayment] at hwealthHmass hwealthLmass
  ring_nf at hbudgetHmass hbudgetLmass hwealthHmass hwealthLmass
  ring_nf at hproductionPrice hlaborWage hcapitalPrice hresource' hcredit' hdeposits'
  ring_nf at hbankBalance' hinterbank hsettlement' hbankRenewal hinheritedReal
  ring_nf at hretailer hcapitalIncome ⊢
  linarith

/-- Positive-date household compatibility from the predecessor's current
faces and portfolio return.  Inherited-face consistency is deliberately absent
because all successor repayments are generated by the parent allocation. -/
theorem sourceFiscalHouseholdCompatibility_succ_of_source_flows
    (P : Primitives S) (I : InheritedState) (X : Allocation S)
    (hfirm : FirmBudgetFlows P I X)
    (hproduction : AggregateProduction P I X)
    (hcapitalProducer : CapitalProducerAccounts P X)
    (haccounting : AccountingIdentities P X)
    (hresource : ResourceClears P X)
    (hcredit : CreditClears P X)
    (hdeposits : DepositsClear P X)
    (hcapital : CapitalClears P I X)
    (hlabor : LaborClears P X)
    (hbankBalance : BankBalance P X)
    (hsettlement : SettlementClears P X)
    (hrenewal : BankRenewalFlows P I X)
    (hcurrentFaces : CurrentNominalFaceConsistency P X) :
    ∀ t h s, FirmHistoryAdmissible P (t + 1) (childHistory h s) →
      X.workerConsumption (t + 1) (childHistory h s) +
          X.householdDeposits (t + 1) (childHistory h s) =
        X.wage (t + 1) (childHistory h s) *
            X.workerLabor (t + 1) (childHistory h s) +
        X.depositRate t h * X.householdDeposits t h /
            X.inflation (t + 1) (childHistory h s) +
        X.retailerNetIncome (t + 1) (childHistory h s) +
        X.capitalProducerNetIncome (t + 1) (childHistory h s) +
        X.bankNetIncome (t + 1) (childHistory h s) -
        (X.reserveRate t h * X.reservesPostPayment t h -
          X.facilityRate t h * X.facilityBorrowing t h) /
            X.inflation (t + 1) (childHistory h s) +
        X.reservesPostPayment (t + 1) (childHistory h s) -
        X.facilityBorrowing (t + 1) (childHistory h s) := by
  intro t h s hs
  let hc := childHistory h s
  have hprevious : previousHistory hc = h := by rfl
  have hparent : FirmHistoryAdmissible P t h := by
    unfold FirmHistoryAdmissible at hs ⊢
    simp only [FiniteMarkovTree.historyWeight] at hs
    change 0 < P.tree.historyWeight t h *
      P.tree.transition (currentState h) s at hs
    have htransition := P.tree.transition_nonneg (currentState h) s
    nlinarith
  have hbudgetH := hfirm.1 .H (t + 1) hc hs
  have hbudgetL := hfirm.1 .L (t + 1) hc hs
  have hwealthH := hfirm.2.2 .H t h s hs
  have hwealthL := hfirm.2.2 .L t h s hs
  have hbudgetHmass := congrArg (fun y : ℝ ↦ P.mass .H * y) hbudgetH
  have hbudgetLmass := congrArg (fun y : ℝ ↦ P.mass .L * y) hbudgetL
  have hwealthHmass := congrArg (fun y : ℝ ↦ P.mass .H * y) hwealthH
  have hwealthLmass := congrArg (fun y : ℝ ↦ P.mass .L * y) hwealthL
  have hproduction' := hproduction.2 t h s hs
  have hproductionPrice := congrArg
    (fun y : ℝ ↦ X.inputPrice (t + 1) hc * y) hproduction'
  have hlabor' := hlabor (t + 1) hc hs
  have hlaborWage := congrArg
    (fun y : ℝ ↦ X.wage (t + 1) hc * y) hlabor'
  have hcapitalInstalled := hcapital.2.1 t h s hs
  have hcapitalInstalledScaled := congrArg
    (fun y : ℝ ↦ (1 - P.depreciation) * y) hcapitalInstalled
  have hcapitalLaw := hcapital.2.2 (t + 1) hc hs
  rw [sum_firmType_eq_H_add_L] at hcapitalInstalledScaled hcapitalLaw
  have hcapitalCombined :
      (∑ i, P.mass i * X.capital i (t + 1) hc) =
        (1 - P.depreciation) * (∑ i, P.mass i * X.capital i t h) +
          X.investment (t + 1) hc := by
    rw [sum_firmType_eq_H_add_L, sum_firmType_eq_H_add_L]
    ring_nf at hcapitalInstalledScaled hcapitalLaw ⊢
    linarith
  have hcapitalPrice := congrArg
    (fun y : ℝ ↦ X.capitalPrice (t + 1) hc * y) hcapitalCombined
  have hresource' := hresource (t + 1) hc hs
  have hcredit' := hcredit (t + 1) hc hs
  have hdeposits' := hdeposits (t + 1) hc hs
  have hbankBalance' := hbankBalance (t + 1) hc hs
  rcases hsettlement (t + 1) hc hs with
    ⟨hinterbank, _hfacilityNonneg, hsettlement'⟩
  have hbankRenewal :=
    bankRetainedEquity_add_bankNetIncome_eq_preExit P I X hrenewal
      (t + 1) hc hs
  have hpriorFinancial :=
    currentHouseholdFinancialFaceIdentity P X hcurrentFaces hcredit
      hdeposits hsettlement t h hparent
  have hpriorFinancialReal := congrArg
    (fun y : ℝ ↦ y / X.inflation (t + 1) hc) hpriorFinancial
  have hretailer := haccounting.2 (t + 1) hc hs
  rcases hcapitalProducer (t + 1) hc hs with
    ⟨_hcapitalPositive, _hinvestmentNonneg, _hcreation, hcapitalIncome⟩
  rw [sum_firmType_eq_H_add_L] at hproductionPrice hlaborWage hresource' hcredit' hdeposits' hpriorFinancialReal
  rw [sum_firmType_eq_H_add_L, sum_firmType_eq_H_add_L] at hcapitalPrice
  simp only [bankPreExitEquity, hprevious,
    expectedAggregateBankGrossReturn] at hbankRenewal
  dsimp [hc, operatingProfit, realRepayment] at hwealthHmass hwealthLmass
  ring_nf at hbudgetHmass hbudgetLmass hwealthHmass hwealthLmass
  ring_nf at hproductionPrice hlaborWage hcapitalPrice hresource' hcredit' hdeposits'
  ring_nf at hbankBalance' hinterbank hsettlement' hbankRenewal hpriorFinancialReal
  ring_nf at hretailer hcapitalIncome ⊢
  linarith

/-- Full household compatibility from literal firm, bank, face, clearing and
resource accounts.  The theorem separates the inherited date-zero identity
from the current-face identity used at successor dates. -/
theorem sourceFiscalHouseholdCompatibility_of_source_flows
    (P : Primitives S) (I : InheritedState) (X : Allocation S)
    (hfirm : FirmBudgetFlows P I X)
    (hproduction : AggregateProduction P I X)
    (hcapitalProducer : CapitalProducerAccounts P X)
    (haccounting : AccountingIdentities P X)
    (hresource : ResourceClears P X)
    (hcredit : CreditClears P X)
    (hdeposits : DepositsClear P X)
    (hcapital : CapitalClears P I X)
    (hlabor : LaborClears P X)
    (hbankBalance : BankBalance P X)
    (hsettlement : SettlementClears P X)
    (hrenewal : BankRenewalFlows P I X)
    (hinheritedFaces : InheritedNominalFaceConsistency P I)
    (hcurrentFaces : CurrentNominalFaceConsistency P X) :
    SourceFiscalHouseholdCompatibility P I X := by
  constructor
  · exact sourceFiscalHouseholdCompatibility_zero_of_source_flows P I X hfirm
      hproduction hcapitalProducer haccounting hresource hcredit hdeposits
      hcapital hlabor hbankBalance hsettlement hrenewal hinheritedFaces
  · exact sourceFiscalHouseholdCompatibility_succ_of_source_flows P I X hfirm
      hproduction hcapitalProducer haccounting hresource hcredit hdeposits
      hcapital hlabor hbankBalance hsettlement hrenewal hcurrentFaces

/-- The concrete real/fiscal residual completion satisfies the literal
household budget once the remaining private, bank, face and market-clearing
source accounts are supplied.  The desired compatibility predicate is derived,
not passed as a premise. -/
theorem householdBudgetFlows_withSourceAccountingCompletion_of_source_flows
    (P : Primitives S) (I : InheritedState) (X : Allocation S)
    (hfirm : FirmBudgetFlows P I X)
    (hresource : SourceRealResourceCompatibility P I X)
    (hcapitalPositive : ∀ t h, FirmHistoryAdmissible P t h →
      0 < sourceAggregateCapital P I X t h)
    (hinvestmentNonneg : ∀ t h, FirmHistoryAdmissible P t h →
      0 ≤ sourceInvestment P I X t h)
    (hcredit : CreditClears P X)
    (hdeposits : DepositsClear P X)
    (hlabor : LaborClears P X)
    (hbankBalance : BankBalance P X)
    (hsettlement : SettlementClears P X)
    (hrenewal : BankRenewalFlows P I X)
    (hinheritedFaces : InheritedNominalFaceConsistency P I)
    (hcurrentFaces : CurrentNominalFaceConsistency P X) :
    HouseholdBudgetFlows P I (withSourceAccountingCompletion P I X) := by
  apply (householdBudgetFlows_withSourceAccountingCompletion_iff P I X).2
  apply sourceFiscalHouseholdCompatibility_of_source_flows P I
    (withSourceRealAccounts P I X)
  · simpa only [withSourceRealAccounts] using hfirm
  · exact withSourceRealAccounts_aggregateProduction P I X
  · exact withSourceRealAccounts_capitalProducerAccounts P I X
      hcapitalPositive hinvestmentNonneg
  · exact withSourceRealAccounts_accountingIdentities P I X
  · exact (resourceClears_withSourceRealAccounts_iff P I X).2 hresource
  · simpa only [withSourceRealAccounts] using hcredit
  · simpa only [withSourceRealAccounts] using hdeposits
  · exact withSourceRealAccounts_capitalClears P I X
  · simpa only [withSourceRealAccounts] using hlabor
  · simpa only [withSourceRealAccounts] using hbankBalance
  · simpa only [withSourceRealAccounts] using hsettlement
  · simpa only [withSourceRealAccounts] using hrenewal
  · exact hinheritedFaces
  · simpa only [withSourceRealAccounts] using hcurrentFaces

/-- Primitive domain of the two monetary rules in Section 3.11.  The current
instrument levels remain endogenous processes; these restrictions only make
the logarithmic source equations economically meaningful. -/
def MonetaryPolicyPrimitiveDomain (P : Primitives S) (I : InheritedState) : Prop :=
  0 < P.reserveRateSteady ∧ 0 < P.reserveQuantitySteady ∧
  0 < P.outputReference ∧ 0 < P.governmentBondSupply ∧
  0 < I.reserveRateLag ∧ 0 < I.reservesPreLag

/-- The source remuneration and reserve-quantity rules, including distinct
lagged pre-payment reserves.  Equations are imposed only on histories with
positive probability under the primitive recurrent tree. -/
def MonetaryPolicyRules (P : Primitives S) (I : InheritedState)
    (X : Allocation S) : Prop :=
  (∀ h, FirmHistoryAdmissible P 0 h →
    Real.log (X.reserveRate 0 h) =
      P.reserveRatePersistence * Real.log I.reserveRateLag +
      (1 - P.reserveRatePersistence) *
        (Real.log P.reserveRateSteady +
          P.inflationResponse * Real.log (X.inflation 0 h) +
          P.outputResponse * Real.log (X.output 0 h / P.outputReference)) +
      P.reserveRateInnovation (currentState h)) ∧
  (∀ h, FirmHistoryAdmissible P 0 h →
    Real.log (X.reservesPrePayment 0 h) =
      P.reserveQuantityPersistence * Real.log I.reservesPreLag +
      (1 - P.reserveQuantityPersistence) *
        Real.log P.reserveQuantitySteady +
      P.reserveQuantityInnovation (currentState h)) ∧
  (∀ t h s, FirmHistoryAdmissible P (t + 1) (childHistory h s) →
    Real.log (X.reserveRate (t + 1) (childHistory h s)) =
      P.reserveRatePersistence * Real.log (X.reserveRate t h) +
      (1 - P.reserveRatePersistence) *
        (Real.log P.reserveRateSteady +
          P.inflationResponse *
            Real.log (X.inflation (t + 1) (childHistory h s)) +
          P.outputResponse *
            Real.log
              (X.output (t + 1) (childHistory h s) / P.outputReference)) +
      P.reserveRateInnovation s) ∧
  (∀ t h s, FirmHistoryAdmissible P (t + 1) (childHistory h s) →
    Real.log (X.reservesPrePayment (t + 1) (childHistory h s)) =
      P.reserveQuantityPersistence * Real.log (X.reservesPrePayment t h) +
      (1 - P.reserveQuantityPersistence) *
        Real.log P.reserveQuantitySteady +
      P.reserveQuantityInnovation s)

/-- Source OTC corridor price in the active matching regime.  This is the
price equation only; matching quantities and population clearing remain in
`SettlementClears` and the bank-population layer, not in this predicate. -/
def OTCNegotiatedRateRule (P : Primitives S) (X : Allocation S) : Prop :=
  ∀ t h, FirmHistoryAdmissible P t h →
    0 < X.bankTightness t h ∧
    X.interbankRate t h =
      otcNegotiatedRate (X.reserveRate t h) (X.facilityRate t h)
        P.matchingIntensity (X.bankTightness t h)

/-! ### The announced four-instrument intervention used by the local branches -/

/-- The source intervention vector
`v = (v_R, v_M, v_ρ, v_Δ)`.  These are level changes to the date-zero
announcements; they are not extra endogenous prices or a free residual. -/
structure InitialPolicyIntervention where
  reserveRateInnovation : ℝ
  reserveQuantityInnovation : ℝ
  reserveRequirement : ℝ
  corridorWidth : ℝ

def zeroInitialPolicyIntervention : InitialPolicyIntervention where
  reserveRateInnovation := 0
  reserveQuantityInnovation := 0
  reserveRequirement := 0
  corridorWidth := 0

def pureReserveRateIntervention (h : ℝ) : InitialPolicyIntervention where
  reserveRateInnovation := h
  reserveQuantityInnovation := 0
  reserveRequirement := 0
  corridorWidth := 0

/-- The calendar component used by the deterministic local experiment never
returns to its initial state.  Consequently an innovation attached to the
initial Markov state is a date-zero announcement and not a recurrent shock.
This is the source's `0 → 1 → 2 → 2` timing condition in support form. -/
def InitialCalendarStateIsTransient (P : Primitives S) : Prop :=
  (∀ s, 0 < P.tree.transition P.tree.initial s → s ≠ P.tree.initial) ∧
  ∀ s, s ≠ P.tree.initial →
    P.tree.transition s P.tree.initial = 0

/-- The three literal calendar phases used by the finite local experiment. -/
inductive LocalBridgePhase
  | dateZero
  | dateOne
  | recurrent
  deriving DecidableEq, Fintype, Repr

/-- Deterministic transition `0 -> 1 -> 2 -> 2`; every unlisted transition
has probability zero. -/
def localBridgeTransition : LocalBridgePhase → LocalBridgePhase → ℝ
  | .dateZero, .dateOne => 1
  | .dateOne, .recurrent => 1
  | .recurrent, .recurrent => 1
  | _, _ => 0

/-- A concrete finite Markov carrier for the local prefix and recurrent tail.
This constructs the calendar itself; it does not construct the remaining
technology, policy or payment primitives. -/
def localBridgeTree : FiniteMarkovTree LocalBridgePhase where
  initial := .dateZero
  transition := localBridgeTransition
  transition_nonneg := by
    intro s s'
    cases s <;> cases s' <;> simp [localBridgeTransition]
  transition_sum_one := by
    intro s
    cases s
    · rw [Finset.sum_eq_single .dateOne]
      · simp [localBridgeTransition]
      · intro b _ hne
        cases b <;> simp_all [localBridgeTransition]
      · simp
    · rw [Finset.sum_eq_single .recurrent]
      · simp [localBridgeTransition]
      · intro b _ hne
        cases b <;> simp_all [localBridgeTransition]
      · simp
    · rw [Finset.sum_eq_single .recurrent]
      · simp [localBridgeTransition]
      · intro b _ hne
        cases b <;> simp_all [localBridgeTransition]
      · simp

theorem localBridgeTree_transition_support :
    localBridgeTree.transition .dateZero .dateOne = 1 ∧
      localBridgeTree.transition .dateOne .recurrent = 1 ∧
      localBridgeTree.transition .recurrent .recurrent = 1 := by
  simp [localBridgeTree, localBridgeTransition]

theorem localBridgeTree_transition_pos_from_dateZero_iff
    (s : LocalBridgePhase) :
    0 < localBridgeTree.transition .dateZero s ↔ s = .dateOne := by
  cases s <;> simp [localBridgeTree, localBridgeTransition]

theorem localBridgeTree_transition_pos_from_dateOne_iff
    (s : LocalBridgePhase) :
    0 < localBridgeTree.transition .dateOne s ↔ s = .recurrent := by
  cases s <;> simp [localBridgeTree, localBridgeTransition]

theorem localBridgeTree_transition_pos_from_recurrent_iff
    (s : LocalBridgePhase) :
    0 < localBridgeTree.transition .recurrent s ↔ s = .recurrent := by
  cases s <;> simp [localBridgeTree, localBridgeTransition]

/-- The unique aggregate history carried by the deterministic calendar at
each date, stored newest-state first like every model history. -/
def localBridgeHistory : (t : ℕ) → History LocalBridgePhase t
  | 0 => fun _ ↦ .dateZero
  | n + 1 => childHistory (localBridgeHistory n)
      (if n = 0 then .dateOne else .recurrent)

@[simp] theorem localBridgeHistory_current_zero :
    currentState (localBridgeHistory 0) = .dateZero := rfl

@[simp] theorem localBridgeHistory_current_succ (n : ℕ) :
    currentState (localBridgeHistory (n + 1)) =
      if n = 0 then .dateOne else .recurrent := rfl

@[simp] theorem localBridgeHistory_previous_succ (n : ℕ) :
    previousHistory (localBridgeHistory (n + 1)) = localBridgeHistory n := by
  rfl

theorem localBridgeTree_historyWeight_nonneg :
    ∀ t (h : History LocalBridgePhase t),
      0 ≤ localBridgeTree.historyWeight t h := by
  intro t
  induction t with
  | zero =>
      intro h
      simp only [FiniteMarkovTree.historyWeight]
      split <;> norm_num
  | succ t ih =>
      intro h
      simp only [FiniteMarkovTree.historyWeight]
      exact mul_nonneg (ih _) (localBridgeTree.transition_nonneg _ _)

theorem localBridgeHistory_weight_one :
    ∀ t, localBridgeTree.historyWeight t (localBridgeHistory t) = 1 := by
  intro t
  induction t with
  | zero =>
      simp [FiniteMarkovTree.historyWeight, localBridgeHistory,
        localBridgeTree, currentState]
  | succ t ih =>
      rw [FiniteMarkovTree.historyWeight, localBridgeHistory_previous_succ, ih]
      cases t with
      | zero =>
          simp [localBridgeHistory, localBridgeTree, localBridgeTransition,
            currentState, childHistory]
      | succ n =>
          by_cases hn : n = 0
          · subst n
            simp [localBridgeHistory, localBridgeTree, localBridgeTransition,
              currentState, childHistory]
          · simp [localBridgeHistory, localBridgeTree, localBridgeTransition,
              currentState, childHistory, hn]

/-- Positive probability exhausts exactly the displayed deterministic
history.  Thus a finite simulated prefix is not being generalized to hidden
off-path aggregate histories. -/
theorem localBridgeTree_historyWeight_pos_iff
    (t : ℕ) (h : History LocalBridgePhase t) :
    0 < localBridgeTree.historyWeight t h ↔ h = localBridgeHistory t := by
  constructor
  · intro hh
    induction t with
    | zero =>
        simp only [FiniteMarkovTree.historyWeight] at hh
        have hc : currentState h = localBridgeTree.initial := by
          split at hh
          · assumption
          · norm_num at hh
        funext j
        fin_cases j
        simpa [currentState, localBridgeTree, localBridgeHistory] using hc
    | succ n ih =>
        rw [FiniteMarkovTree.historyWeight] at hh
        have hprevNonneg :=
          localBridgeTree_historyWeight_nonneg n (previousHistory h)
        rcases (mul_pos_iff.mp hh) with hpos | hneg
        · have hprev : previousHistory h = localBridgeHistory n := ih _ hpos.1
          have ht := hpos.2
          rw [hprev] at ht
          have hcurrent : currentState h =
              (if n = 0 then .dateOne else .recurrent) := by
            cases n with
            | zero =>
                have ht' : 0 < localBridgeTree.transition .dateZero
                    (currentState h) := by
                  simpa [localBridgeHistory, currentState] using ht
                exact (localBridgeTree_transition_pos_from_dateZero_iff _).mp ht'
            | succ n =>
                cases n with
                | zero =>
                    have ht' : 0 < localBridgeTree.transition .dateOne
                        (currentState h) := by
                      simpa [localBridgeHistory, currentState, childHistory] using ht
                    exact (localBridgeTree_transition_pos_from_dateOne_iff _).mp ht'
                | succ n =>
                    have ht' : 0 < localBridgeTree.transition .recurrent
                        (currentState h) := by
                      simp [localBridgeHistory, currentState, childHistory] at ht
                      exact ht
                    exact (localBridgeTree_transition_pos_from_recurrent_iff _).mp ht'
          rw [← childHistory_previousHistory_currentState h, hprev, hcurrent]
          rfl
        · exact (not_lt_of_ge hprevNonneg hneg.1).elim
  · rintro rfl
    rw [localBridgeHistory_weight_one]
    norm_num

theorem localBridgeTree_initial_transient :
    (∀ s, 0 < localBridgeTree.transition localBridgeTree.initial s →
      s ≠ localBridgeTree.initial) ∧
    ∀ s, s ≠ localBridgeTree.initial →
      localBridgeTree.transition s localBridgeTree.initial = 0 := by
  constructor <;> intro s <;> cases s <;> simp [localBridgeTree, localBridgeTransition]

/-- Modify exactly the four date-zero instruments of the local experiment.
The two rule innovations are attached to the transient initial Markov state;
the reserve requirement and corridor paths are changed only at date zero.
Every real primitive, inherited nominal promise and later announcement is
literally inherited from `P`. -/
noncomputable def initialIntervenedPrimitives
    (P : Primitives S) (v : InitialPolicyIntervention) : Primitives S :=
  { P with
    reserveRateInnovation := fun s ↦
      P.reserveRateInnovation s +
        if s = P.tree.initial then v.reserveRateInnovation else 0
    reserveQuantityInnovation := fun s ↦
      P.reserveQuantityInnovation s +
        if s = P.tree.initial then v.reserveQuantityInnovation else 0
    reserveRequirementPath := fun t h ↦
      P.reserveRequirementPath t h +
        if t = 0 then v.reserveRequirement else 0
    corridorWidthPath := fun t h ↦
      P.corridorWidthPath t h +
        if t = 0 then v.corridorWidth else 0 }

/-- The three supported calendar phases of the deterministic bridge:
`0 → 1 → 2 → 2`.  Equalities to one, together with the Markov nonnegativity
and row-sum axioms, exclude unlisted supported successors. -/
def DeterministicBridgeCalendar
    (P : Primitives S) (dateOne recurrent : S) : Prop :=
  dateOne ≠ P.tree.initial ∧ recurrent ≠ P.tree.initial ∧
  dateOne ≠ recurrent ∧
  P.tree.transition P.tree.initial dateOne = 1 ∧
  P.tree.transition dateOne recurrent = 1 ∧
  P.tree.transition recurrent recurrent = 1

/-- Install the concrete deterministic local calendar while leaving every
non-calendar primitive byte-for-byte inherited from `P`. -/
def Primitives.withLocalBridgeTree
    (P : Primitives LocalBridgePhase) : Primitives LocalBridgePhase :=
  { P with tree := localBridgeTree }

theorem Primitives.withLocalBridgeTree_calendar
    (P : Primitives LocalBridgePhase) :
    DeterministicBridgeCalendar P.withLocalBridgeTree
      .dateOne .recurrent := by
  simp [DeterministicBridgeCalendar, Primitives.withLocalBridgeTree,
    localBridgeTree, localBridgeTransition]

theorem Primitives.withLocalBridgeTree_initial_transient
    (P : Primitives LocalBridgePhase) :
    InitialCalendarStateIsTransient P.withLocalBridgeTree := by
  simpa [Primitives.withLocalBridgeTree] using localBridgeTree_initial_transient

theorem Primitives.withLocalBridgeTree_admissible_iff
    (P : Primitives LocalBridgePhase) (t : ℕ)
    (h : History LocalBridgePhase t) :
    FirmHistoryAdmissible P.withLocalBridgeTree t h ↔
      h = localBridgeHistory t := by
  exact localBridgeTree_historyWeight_pos_iff t h

def bridgeDateZeroHistory (P : Primitives S) : History S 0 :=
  fun _ ↦ P.tree.initial

def bridgeDateOneHistory (P : Primitives S) (dateOne : S) : History S 1 :=
  childHistory (bridgeDateZeroHistory P) dateOne

def bridgeDateTwoHistory (P : Primitives S) (dateOne recurrent : S) : History S 2 :=
  childHistory (bridgeDateOneHistory P dateOne) recurrent

/-- Seven inherited coordinates at date one: two installed capitals, two
separate nominal firm promises, bank equity, and the two policy lags. -/
structure LocalPrefixStateSeven where
  capitalH : ℝ
  capitalL : ℝ
  firmFaceH : ℝ
  firmFaceL : ℝ
  bankFace : ℝ
  reserveRateLag : ℝ
  reservesPreLag : ℝ

/-- Ten current controls, in the source order used at each prefix date. -/
structure LocalPrefixControlsTen where
  consumptionH : ℝ
  consumptionL : ℝ
  workerConsumption : ℝ
  wage : ℝ
  inputPrice : ℝ
  inflation : ℝ
  capitalPrice : ℝ
  depositRate : ℝ
  loanRate : ℝ
  tightness : ℝ

/-- Six inherited coordinates at date two.  Firm promises may now be
compressed by the common robust-liquidation factor because both firms
originate active collateralized loans at date one. -/
structure LocalPrefixStateSix where
  capitalH : ℝ
  capitalL : ℝ
  commonPledgeValue : ℝ
  bankFace : ℝ
  reserveRateLag : ℝ
  reservesPreLag : ℝ

/-- The literal `7 + 10 + 6 + 10 = 33` coordinate carrier of the source
finite prefix.  This is a typed economic coordinate list, not an arbitrary
`Fin 33 → ℝ` residual supplied by a caller. -/
structure LocalPrefixCoordinates where
  stateOne : LocalPrefixStateSeven
  controlsZero : LocalPrefixControlsTen
  stateTwo : LocalPrefixStateSix
  controlsOne : LocalPrefixControlsTen

/-- Tie all 33 finite-prefix coordinates to the actual allocation and timing.
Installed physical capital and nominal faces are carried into the next date;
current controls remain endogenous.  At date two the common pledge coordinate
is the actual nominal liquidation value `(1-δ) Π₂ q₂`, not a selected child or
an unrelated scalar. -/
def LocalPrefixCoordinatesRealized
    (P : Primitives S) (X : Allocation S) (dateOne recurrent : S)
    (Z : LocalPrefixCoordinates) : Prop :=
  let h0 := bridgeDateZeroHistory P
  let h1 := bridgeDateOneHistory P dateOne
  let h2 := bridgeDateTwoHistory P dateOne recurrent
  Z.stateOne.capitalH = X.capital FirmType.H 0 h0 ∧
  Z.stateOne.capitalL = X.capital FirmType.L 0 h0 ∧
  Z.stateOne.firmFaceH = X.firmFace FirmType.H 0 h0 ∧
  Z.stateOne.firmFaceL = X.firmFace FirmType.L 0 h0 ∧
  Z.stateOne.bankFace = X.inflation 1 h1 * X.bankEquity 1 h1 ∧
  Z.stateOne.reserveRateLag = X.reserveRate 0 h0 ∧
  Z.stateOne.reservesPreLag = X.reservesPrePayment 0 h0 ∧
  Z.controlsZero.consumptionH = X.firmConsumption FirmType.H 0 h0 ∧
  Z.controlsZero.consumptionL = X.firmConsumption FirmType.L 0 h0 ∧
  Z.controlsZero.workerConsumption = X.workerConsumption 0 h0 ∧
  Z.controlsZero.wage = X.wage 0 h0 ∧
  Z.controlsZero.inputPrice = X.inputPrice 0 h0 ∧
  Z.controlsZero.inflation = X.inflation 0 h0 ∧
  Z.controlsZero.capitalPrice = X.capitalPrice 0 h0 ∧
  Z.controlsZero.depositRate = X.depositRate 0 h0 ∧
  Z.controlsZero.loanRate = X.loanRate 0 h0 ∧
  Z.controlsZero.tightness = X.bankTightness 0 h0 ∧
  Z.stateTwo.capitalH = X.capital FirmType.H 1 h1 ∧
  Z.stateTwo.capitalL = X.capital FirmType.L 1 h1 ∧
  Z.stateTwo.commonPledgeValue =
    (1 - P.depreciation) * X.inflation 2 h2 * X.capitalPrice 2 h2 ∧
  X.firmFace FirmType.H 1 h1 =
    P.pledgeability FirmType.H * Z.stateTwo.commonPledgeValue *
      Z.stateTwo.capitalH ∧
  X.firmFace FirmType.L 1 h1 =
    P.pledgeability FirmType.L * Z.stateTwo.commonPledgeValue *
      Z.stateTwo.capitalL ∧
  Z.stateTwo.bankFace = X.inflation 2 h2 * X.bankEquity 2 h2 ∧
  Z.stateTwo.reserveRateLag = X.reserveRate 1 h1 ∧
  Z.stateTwo.reservesPreLag = X.reservesPrePayment 1 h1 ∧
  Z.controlsOne.consumptionH = X.firmConsumption FirmType.H 1 h1 ∧
  Z.controlsOne.consumptionL = X.firmConsumption FirmType.L 1 h1 ∧
  Z.controlsOne.workerConsumption = X.workerConsumption 1 h1 ∧
  Z.controlsOne.wage = X.wage 1 h1 ∧
  Z.controlsOne.inputPrice = X.inputPrice 1 h1 ∧
  Z.controlsOne.inflation = X.inflation 1 h1 ∧
  Z.controlsOne.capitalPrice = X.capitalPrice 1 h1 ∧
  Z.controlsOne.depositRate = X.depositRate 1 h1 ∧
  Z.controlsOne.loanRate = X.loanRate 1 h1 ∧
  Z.controlsOne.tightness = X.bankTightness 1 h1

/-- The 33-coordinate realization surface does not inspect taxes.  This
definitional invariance is used below to state the precise full-allocation
reconstruction gap; fiscal closure is not silently inserted into the reduced
root. -/
theorem localPrefixCoordinatesRealized_withTax_iff
    (P : Primitives S) (X : Allocation S) (tax : AdaptedProcess S)
    (dateOne recurrent : S) (Z : LocalPrefixCoordinates) :
    LocalPrefixCoordinatesRealized P { X with tax := tax } dateOne recurrent Z ↔
      LocalPrefixCoordinatesRealized P X dateOne recurrent Z := by
  rfl

/-- The two financial rows of the finite system.  H is binding in both; L is
slack in `S` and binding in `B` at date zero. -/
inductive LocalPrefixBranch
  | slack
  | binding
  deriving DecidableEq

/-- Names of the exact 17 date-zero and 16 date-one equations used in the
finite reduction.  Giving the rows economic names prevents a mere count of
33 arbitrary scalar equations from masquerading as the source system. -/
inductive LocalPrefixEquation
  | firmBudgetZeroH | firmBudgetZeroL
  | firmCapitalEulerZeroH | firmCapitalEulerZeroL
  | firmRegimeZeroH | firmRegimeZeroL
  | bankEquityZero | capitalSupplyZero | resourcesZero
  | workerLaborZero | householdEulerZero | nkpcZero
  | reserveRateRuleZero | reserveQuantityRuleZero
  | loanPricingZero | depositPricingZero | bankBalanceZero
  | firmBudgetOneH | firmBudgetOneL
  | firmCapitalEulerOneH | firmCapitalEulerOneL
  | commonPledgeOne
  | bankEquityOne | capitalSupplyOne | resourcesOne
  | workerLaborOne | householdEulerOne | nkpcOne
  | reserveRateRuleOne | reserveQuantityRuleOne
  | loanPricingOne | depositPricingOne | bankBalanceOne
  deriving DecidableEq, Fintype

noncomputable def localFirmBudgetResidual
    (X : Allocation S) (i : FirmType) (t : ℕ) (h : History S t) : ℝ :=
  X.firmConsumption i t h + X.capitalPrice t h * X.capital i t h +
      X.firmDeposit i t h - X.firmWealth i t h - X.loan i t h

noncomputable def localFirmCapitalEulerResidual
    (P : Primitives S) (X : Allocation S) (i : FirmType)
    (t : ℕ) (h : History S t) (nextState : S) : ℝ :=
  let hnext := childHistory h nextState
  let sdf := P.entrepreneurDiscount *
    crraMarginal P.entrepreneurRiskAversion (X.firmConsumption i (t + 1) hnext) /
      crraMarginal P.entrepreneurRiskAversion (X.firmConsumption i t h)
  let marginalProduct := X.inputPrice (t + 1) hnext *
    (P.aggregateProductivity nextState * P.productivity i) * P.alpha *
      (X.capital i t h) ^ (P.alpha - 1) *
      (X.labor i (t + 1) hnext) ^ P.beta
  let collateralUnit := P.pledgeability i * (1 - P.depreciation) *
    X.inflation (t + 1) hnext * X.capitalPrice (t + 1) hnext
  X.capitalPrice t h -
    sdf * (marginalProduct +
      (1 - P.depreciation) * X.capitalPrice (t + 1) hnext) -
    X.collateralDual i t h * collateralUnit

noncomputable def localFirmBindingResidual
    (P : Primitives S) (X : Allocation S) (i : FirmType)
    (t : ℕ) (h : History S t) (nextState : S) : ℝ :=
  let hnext := childHistory h nextState
  X.firmFace i t h - P.pledgeability i * (1 - P.depreciation) *
    X.inflation (t + 1) hnext * X.capitalPrice (t + 1) hnext *
      X.capital i t h

noncomputable def localFirmDateZeroRegimeResidual
    (branch : LocalPrefixBranch) (P : Primitives S) (X : Allocation S)
    (i : FirmType) (h0 : History S 0) (dateOne : S) : ℝ :=
  match branch, i with
  | .slack, .L => X.collateralDual FirmType.L 0 h0
  | _, _ => localFirmBindingResidual P X i 0 h0 dateOne

noncomputable def localBankEquityTransitionResidual
    (P : Primitives S) (X : Allocation S)
    (t : ℕ) (h : History S t) (nextState : S) : ℝ :=
  X.bankEquity (t + 1) (childHistory h nextState) -
    bankRenewalFactor P * X.loanRate t h * X.bankEquity t h /
      X.inflation (t + 1) (childHistory h nextState)

noncomputable def localCapitalSupplyResidual
    (P : Primitives S) (X : Allocation S) (t : ℕ) (h : History S t) : ℝ :=
  X.capitalPrice t h - 1 -
    P.capitalAdjustmentCost * X.investment t h / X.aggregateCapital t h

noncomputable def localResourceResidual
    (P : Primitives S) (X : Allocation S) (t : ℕ) (h : History S t) : ℝ :=
  X.workerConsumption t h + ∑ i, P.mass i * X.firmConsumption i t h +
    X.capitalCreationCost t h + X.priceAdjustmentResourceCost t h - X.output t h

noncomputable def localWorkerLaborResidual
    (P : Primitives S) (X : Allocation S) (t : ℕ) (h : History S t) : ℝ :=
  X.wage t h - P.laborScale *
    X.workerConsumption t h ^ P.workerRiskAversion *
      X.workerLabor t h ^ P.laborCurvature

noncomputable def localHouseholdDepositEulerResidual
    (P : Primitives S) (X : Allocation S)
    (t : ℕ) (h : History S t) (nextState : S) : ℝ :=
  let hnext := childHistory h nextState
  1 - P.workerDiscount * X.depositRate t h /
      X.inflation (t + 1) hnext *
    crraMarginal P.workerRiskAversion (X.workerConsumption (t + 1) hnext) /
      crraMarginal P.workerRiskAversion (X.workerConsumption t h)

noncomputable def localNKPCResidual
    (P : Primitives S) (X : Allocation S)
    (t : ℕ) (h : History S t) (nextState : S) : ℝ :=
  let hnext := childHistory h nextState
  let householdSDF := P.workerDiscount *
    crraMarginal P.workerRiskAversion (X.workerConsumption (t + 1) hnext) /
      crraMarginal P.workerRiskAversion (X.workerConsumption t h)
  1 - P.priceElasticity + P.priceElasticity * X.inputPrice t h -
      P.priceAdjustmentCost * X.inflation t h * (X.inflation t h - 1) +
    householdSDF * P.priceAdjustmentCost * X.output (t + 1) hnext /
      X.output t h * X.inflation (t + 1) hnext *
        (X.inflation (t + 1) hnext - 1)

noncomputable def localReserveRateRuleResidual
    (P : Primitives S) (I : InheritedState) (X : Allocation S)
    (t : ℕ) (h : History S t) : ℝ :=
  match t with
  | 0 =>
      Real.log (X.reserveRate 0 h) -
        (P.reserveRatePersistence * Real.log I.reserveRateLag +
          (1 - P.reserveRatePersistence) *
            (Real.log P.reserveRateSteady +
              P.inflationResponse * Real.log (X.inflation 0 h) +
              P.outputResponse * Real.log (X.output 0 h / P.outputReference)) +
          P.reserveRateInnovation (currentState h))
  | n + 1 =>
      let hp := previousHistory h
      Real.log (X.reserveRate (n + 1) h) -
        (P.reserveRatePersistence * Real.log (X.reserveRate n hp) +
          (1 - P.reserveRatePersistence) *
            (Real.log P.reserveRateSteady +
              P.inflationResponse * Real.log (X.inflation (n + 1) h) +
              P.outputResponse *
                Real.log (X.output (n + 1) h / P.outputReference)) +
          P.reserveRateInnovation (currentState h))

noncomputable def localReserveQuantityRuleResidual
    (P : Primitives S) (I : InheritedState) (X : Allocation S)
    (t : ℕ) (h : History S t) : ℝ :=
  match t with
  | 0 =>
      Real.log (X.reservesPrePayment 0 h) -
        (P.reserveQuantityPersistence * Real.log I.reservesPreLag +
          (1 - P.reserveQuantityPersistence) *
            Real.log P.reserveQuantitySteady +
          P.reserveQuantityInnovation (currentState h))
  | n + 1 =>
      let hp := previousHistory h
      Real.log (X.reservesPrePayment (n + 1) h) -
        (P.reserveQuantityPersistence *
            Real.log (X.reservesPrePayment n hp) +
          (1 - P.reserveQuantityPersistence) *
            Real.log P.reserveQuantitySteady +
          P.reserveQuantityInnovation (currentState h))

noncomputable def localBankSettlementSurplus
    (P : Primitives S) (X : Allocation S)
    (t : ℕ) (h : History S t) (ω : BankPayment) : ℝ :=
  bankSettlementSurplus (X.reservesPrePayment t h)
    (P.reserveRequirementPath t h)
    (X.depositRate t h / X.reserveRate t h)
    (X.bankDeposits t h) (P.paymentShock ω)

noncomputable def localBankLiquidityMarginal
    (P : Primitives S) (X : Allocation S)
    (t : ℕ) (h : History S t) (ω : BankPayment) : ℝ :=
  otcLiquidityMarginal
    (bankOTCDeficitSlopeAt P X t h (X.bankTightness t h))
    (bankOTCSurplusSlopeAt P X t h (X.bankTightness t h))
    (localBankSettlementSurplus P X t h ω)

noncomputable def localLoanPricingResidual
    (P : Primitives S) (X : Allocation S)
    (t : ℕ) (h : History S t) : ℝ :=
  X.loanRate t h - X.reserveRate t h -
    finiteSupportExpectation P.paymentSupport P.paymentProbability
      (localBankLiquidityMarginal P X t h)

noncomputable def localDepositPricingResidual
    (P : Primitives S) (X : Allocation S)
    (t : ℕ) (h : History S t) : ℝ :=
  let rho := P.reserveRequirementPath t h
  let xi := X.depositRate t h / X.reserveRate t h
  let marginal := localBankLiquidityMarginal P X t h
  X.loanRate t h - X.depositRate t h -
      rho * finiteSupportExpectation P.paymentSupport P.paymentProbability marginal +
    (xi - rho) * finiteSupportExpectation P.paymentSupport P.paymentProbability
      (fun ω ↦ marginal ω * P.paymentShock ω)

noncomputable def localBankBalanceResidual
    (X : Allocation S) (t : ℕ) (h : History S t) : ℝ :=
  X.bankLoans t h + X.reservesPrePayment t h -
    X.bankDeposits t h - X.bankRetainedEquity t h

/-- Every bank type's literal balance sheet and the population aggregation
identities imply the aggregate balance row used by the finite prefix.  This is
one direction only: a zero aggregate residual does not reconstruct individual
bank feasibility or optimality. -/
theorem localBankBalanceResidual_eq_zero_of_finiteRowEnvironment
    {J : Type*} [Fintype J] [DecidableEq J]
    (P : Primitives S) (I : InheritedState) (X : Allocation S)
    (B : BankPopulationCandidate S J)
    (H : BankPopulationFiniteRowEnvironmentFor P I X B)
    (t : ℕ) (h : History S t) (hs : FirmHistoryAdmissible P t h) :
    localBankBalanceResidual X t h = 0 := by
  classical
  rcases H with ⟨_hmass, hfeasible, haggregate, _hotc⟩
  rcases haggregate t h hs with
    ⟨_hequity, _hdividend, hretained, hloans, hreserves, hdeposits⟩
  have hbalance : ∀ j,
      (B.plan j).loans t h + (B.plan j).reservesPre t h =
        (B.plan j).deposits t h + (B.plan j).retainedEquity t h := by
    intro j
    exact (hfeasible j).2.2.1 t h hs
  unfold localBankBalanceResidual
  rw [hloans, hreserves, hdeposits, hretained]
  calc
    (∑ j, B.mass j * (B.plan j).loans t h) +
          (∑ j, B.mass j * (B.plan j).reservesPre t h) -
        (∑ j, B.mass j * (B.plan j).deposits t h) -
          (∑ j, B.mass j * (B.plan j).retainedEquity t h) =
      ∑ j, B.mass j *
        ((B.plan j).loans t h + (B.plan j).reservesPre t h -
          (B.plan j).deposits t h - (B.plan j).retainedEquity t h) := by
            symm
            calc
              (∑ j, B.mass j *
                ((B.plan j).loans t h + (B.plan j).reservesPre t h -
                  (B.plan j).deposits t h -
                    (B.plan j).retainedEquity t h)) =
                  ∑ j, (B.mass j * (B.plan j).loans t h +
                    B.mass j * (B.plan j).reservesPre t h -
                    B.mass j * (B.plan j).deposits t h -
                    B.mass j * (B.plan j).retainedEquity t h) := by
                      apply Finset.sum_congr rfl
                      intro j _
                      ring
              _ = _ := by
                rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib,
                  Finset.sum_add_distrib]
    _ = 0 := by
      apply Finset.sum_eq_zero
      intro j _
      rw [hbalance j]
      ring

/-- Compatibility projection from the fuller population equilibrium.  The
finite-row proof itself above uses only the non-circular environment. -/
theorem localBankBalanceResidual_eq_zero_of_populationFor
    {J : Type*} [Fintype J] [DecidableEq J]
    (P : Primitives S) (I : InheritedState) (X : Allocation S)
    (B : BankPopulationCandidate S J)
    (H : BankPopulationEquilibriumFor P I X B)
    (t : ℕ) (h : History S t) (hs : FirmHistoryAdmissible P t h) :
    localBankBalanceResidual X t h = 0 := by
  exact localBankBalanceResidual_eq_zero_of_finiteRowEnvironment P I X B
    (bankPopulationFiniteRowEnvironmentFor_of_equilibriumFor P I X B H) t h hs

/-- The actual finite residual evaluated on an allocation.  Rows 0--16 use
date zero, rows 17--32 date one, and every forward term is taken from the
endogenous successor allocation.  No future price, consumption or wealth is
frozen when the intervention changes. -/
noncomputable def localPrefixResidual
    (branch : LocalPrefixBranch) (P : Primitives S) (I : InheritedState)
    (X : Allocation S) (dateOne recurrent : S) : LocalPrefixEquation → ℝ :=
  let h0 := bridgeDateZeroHistory P
  let h1 := bridgeDateOneHistory P dateOne
  fun equation ↦ match equation with
  | .firmBudgetZeroH => localFirmBudgetResidual X FirmType.H 0 h0
  | .firmBudgetZeroL => localFirmBudgetResidual X FirmType.L 0 h0
  | .firmCapitalEulerZeroH =>
      localFirmCapitalEulerResidual P X FirmType.H 0 h0 dateOne
  | .firmCapitalEulerZeroL =>
      localFirmCapitalEulerResidual P X FirmType.L 0 h0 dateOne
  | .firmRegimeZeroH =>
      localFirmDateZeroRegimeResidual branch P X FirmType.H h0 dateOne
  | .firmRegimeZeroL =>
      localFirmDateZeroRegimeResidual branch P X FirmType.L h0 dateOne
  | .bankEquityZero => localBankEquityTransitionResidual P X 0 h0 dateOne
  | .capitalSupplyZero => localCapitalSupplyResidual P X 0 h0
  | .resourcesZero => localResourceResidual P X 0 h0
  | .workerLaborZero => localWorkerLaborResidual P X 0 h0
  | .householdEulerZero => localHouseholdDepositEulerResidual P X 0 h0 dateOne
  | .nkpcZero => localNKPCResidual P X 0 h0 dateOne
  | .reserveRateRuleZero => localReserveRateRuleResidual P I X 0 h0
  | .reserveQuantityRuleZero => localReserveQuantityRuleResidual P I X 0 h0
  | .loanPricingZero => localLoanPricingResidual P X 0 h0
  | .depositPricingZero => localDepositPricingResidual P X 0 h0
  | .bankBalanceZero => localBankBalanceResidual X 0 h0
  | .firmBudgetOneH => localFirmBudgetResidual X FirmType.H 1 h1
  | .firmBudgetOneL => localFirmBudgetResidual X FirmType.L 1 h1
  | .firmCapitalEulerOneH =>
      localFirmCapitalEulerResidual P X FirmType.H 1 h1 recurrent
  | .firmCapitalEulerOneL =>
      localFirmCapitalEulerResidual P X FirmType.L 1 h1 recurrent
  | .commonPledgeOne =>
      X.firmFace FirmType.H 1 h1 /
          (P.pledgeability FirmType.H * X.capital FirmType.H 1 h1) -
        X.firmFace FirmType.L 1 h1 /
          (P.pledgeability FirmType.L * X.capital FirmType.L 1 h1)
  | .bankEquityOne => localBankEquityTransitionResidual P X 1 h1 recurrent
  | .capitalSupplyOne => localCapitalSupplyResidual P X 1 h1
  | .resourcesOne => localResourceResidual P X 1 h1
  | .workerLaborOne => localWorkerLaborResidual P X 1 h1
  | .householdEulerOne => localHouseholdDepositEulerResidual P X 1 h1 recurrent
  | .nkpcOne => localNKPCResidual P X 1 h1 recurrent
  | .reserveRateRuleOne => localReserveRateRuleResidual P I X 1 h1
  | .reserveQuantityRuleOne => localReserveQuantityRuleResidual P I X 1 h1
  | .loanPricingOne => localLoanPricingResidual P X 1 h1
  | .depositPricingOne => localDepositPricingResidual P X 1 h1
  | .bankBalanceOne => localBankBalanceResidual X 1 h1

def LocalPrefixEquationsHold
    (branch : LocalPrefixBranch) (P : Primitives S) (I : InheritedState)
    (X : Allocation S) (dateOne recurrent : S) : Prop :=
  ∀ equation, localPrefixResidual branch P I X dateOne recurrent equation = 0

/-! The reduced 33-row system below is computed only from its 33 coordinates,
the inherited positions, the primitive economy and the exact continuation
control rule.  It is separate from `localPrefixResidual`, which audits those
same economic equations against a complete allocation. -/

abbrev LocalPrefixContinuationRule :=
  LocalPrefixStateSix → LocalPrefixControlsTen

/-- At the state delivered by the finite prefix, the continuation rule returns
the actual endogenous date-two controls of the full allocation.  Thus future
prices, consumption and wealth respond through the continuation; only the
inherited six-state vector is passed across the seam. -/
def LocalContinuationControlsRealized
    (P : Primitives S) (X : Allocation S) (dateOne recurrent : S)
    (tail : LocalPrefixContinuationRule) (state : LocalPrefixStateSix) : Prop :=
  let h2 := bridgeDateTwoHistory P dateOne recurrent
  let u2 := tail state
  u2.consumptionH = X.firmConsumption FirmType.H 2 h2 ∧
  u2.consumptionL = X.firmConsumption FirmType.L 2 h2 ∧
  u2.workerConsumption = X.workerConsumption 2 h2 ∧
  u2.wage = X.wage 2 h2 ∧
  u2.inputPrice = X.inputPrice 2 h2 ∧
  u2.inflation = X.inflation 2 h2 ∧
  u2.capitalPrice = X.capitalPrice 2 h2 ∧
  u2.depositRate = X.depositRate 2 h2 ∧
  u2.loanRate = X.loanRate 2 h2 ∧
  u2.tightness = X.bankTightness 2 h2

/-! ### Source bank/payment regime for the deterministic local bridge -/

/-- The artificial witness uses exactly two equiprobable payment shocks,
`-ζ` and `+ζ`.  This predicate is a property to be verified for the witness;
it does not replace the general finite payment law in `Primitives`. -/
def BinarySymmetricPaymentLaw
    (P : Primitives S) (paymentMinus paymentPlus : BankPayment)
    (paymentSize : ℝ) : Prop :=
  paymentMinus ≠ paymentPlus ∧ 0 < paymentSize ∧
  (∀ ω, ω ∈ P.paymentSupport ↔ ω = paymentMinus ∨ ω = paymentPlus) ∧
  P.paymentProbability paymentMinus = 1 / 2 ∧
  P.paymentProbability paymentPlus = 1 / 2 ∧
  P.paymentShock paymentMinus = -paymentSize ∧
  P.paymentShock paymentPlus = paymentSize

/-- Any finite expectation under the artificial witness's two-point law is
literally the arithmetic average of its two atom values.  This is the algebraic
bridge used by the reduced bank-pricing rows; it does not assert bank
optimality. -/
theorem finiteSupportExpectation_eq_average_of_binarySymmetric
    (P : Primitives S) (paymentMinus paymentPlus : BankPayment)
    (paymentSize : ℝ)
    (H : BinarySymmetricPaymentLaw P paymentMinus paymentPlus paymentSize)
    (f : BankPayment → ℝ) :
    finiteSupportExpectation P.paymentSupport P.paymentProbability f =
      (f paymentMinus + f paymentPlus) / 2 := by
  rcases H with ⟨hne, _hsize, hsupport, hprobMinus, hprobPlus,
    _hshockMinus, _hshockPlus⟩
  have hsupportEq : P.paymentSupport = {paymentMinus, paymentPlus} := by
    ext ω
    rw [hsupport]
    simp only [Finset.mem_insert, Finset.mem_singleton]
  unfold finiteSupportExpectation
  rw [hsupportEq]
  simp [hne, hprobMinus, hprobPlus]
  ring

/-- The shock-weighted expectation under the binary witness. -/
theorem finiteSupportExpectation_mul_shock_eq_of_binarySymmetric
    (P : Primitives S) (paymentMinus paymentPlus : BankPayment)
    (paymentSize : ℝ)
    (H : BinarySymmetricPaymentLaw P paymentMinus paymentPlus paymentSize)
    (f : BankPayment → ℝ) :
    finiteSupportExpectation P.paymentSupport P.paymentProbability
        (fun ω ↦ f ω * P.paymentShock ω) =
      paymentSize * (f paymentPlus - f paymentMinus) / 2 := by
  rcases H with ⟨hne, hsize, hsupport, hprobMinus, hprobPlus,
    hshockMinus, hshockPlus⟩
  rw [finiteSupportExpectation_eq_average_of_binarySymmetric P paymentMinus
      paymentPlus paymentSize
      ⟨hne, hsize, hsupport, hprobMinus, hprobPlus, hshockMinus, hshockPlus⟩]
  rw [hshockMinus, hshockPlus]
  ring

/-- In the strict deficit/surplus region used by the finite experiment, the
actual finite-law marginal-liquidity expectations reduce to the average and
difference terms written in rows 8 and 9.  This proves the expectation
elimination only; deriving those pricing rows from dynamic bank optimality
still requires the Bellman comparison bridge. -/
theorem binaryStrictSigns_expectations
    (P : Primitives S) (X : Allocation S) (t : ℕ) (h : History S t)
    (paymentMinus paymentPlus : BankPayment) (paymentSize : ℝ)
    (H : BinarySymmetricPaymentLaw P paymentMinus paymentPlus paymentSize)
    (hminus : localBankSettlementSurplus P X t h paymentMinus < 0)
    (hplus : 0 < localBankSettlementSurplus P X t h paymentPlus) :
    finiteSupportExpectation P.paymentSupport P.paymentProbability
        (localBankLiquidityMarginal P X t h) =
        (bankOTCDeficitSlopeAt P X t h (X.bankTightness t h) +
          bankOTCSurplusSlopeAt P X t h (X.bankTightness t h)) / 2 ∧
      finiteSupportExpectation P.paymentSupport P.paymentProbability
          (fun ω ↦ localBankLiquidityMarginal P X t h ω * P.paymentShock ω) =
        -paymentSize *
          (bankOTCDeficitSlopeAt P X t h (X.bankTightness t h) -
            bankOTCSurplusSlopeAt P X t h (X.bankTightness t h)) / 2 := by
  have hmargMinus : localBankLiquidityMarginal P X t h paymentMinus =
      bankOTCDeficitSlopeAt P X t h (X.bankTightness t h) := by
    unfold localBankLiquidityMarginal otcLiquidityMarginal
    rw [if_pos hminus]
  have hmargPlus : localBankLiquidityMarginal P X t h paymentPlus =
      bankOTCSurplusSlopeAt P X t h (X.bankTightness t h) := by
    unfold localBankLiquidityMarginal otcLiquidityMarginal
    rw [if_neg (not_lt_of_ge hplus.le)]
  constructor
  · rw [finiteSupportExpectation_eq_average_of_binarySymmetric P paymentMinus
      paymentPlus paymentSize H, hmargMinus, hmargPlus]
  · rw [finiteSupportExpectation_mul_shock_eq_of_binarySymmetric P paymentMinus
      paymentPlus paymentSize H, hmargMinus, hmargPlus]
    ring



/-- On the strict binary branch, the two reduced pricing rows and the aggregate
balance identity make the common plan's literal expected gross return equal to
the loan return times retained equity.  This is the missing algebraic seam
between the reduced bank-equity transition and typewise renewal; it does not
derive the pricing rows, feasibility, or optimality. -/
theorem expectedBankGrossReturn_eq_loanRate_mul_retainedEquity_of_binary_rows
    {S : Type*} [Fintype S] [DecidableEq S]
    (P : Primitives S) (X : Allocation S) (p : BankPlan S)
    (t : ℕ) (h : History S t)
    (paymentMinus paymentPlus : BankPayment) (paymentSize : ℝ)
    (hbinary : BinarySymmetricPaymentLaw P paymentMinus paymentPlus paymentSize)
    (hflows : BankCandidateOTCFlowsAt P X p t h (X.bankTightness t h))
    (hreserve : X.reserveRate t h ≠ 0)
    (hminus : localBankSettlementSurplus P X t h paymentMinus < 0)
    (hplus : 0 < localBankSettlementSurplus P X t h paymentPlus)
    (hloans : p.loans t h = X.bankLoans t h)
    (hreserves : p.reservesPre t h = X.reservesPrePayment t h)
    (hdeposits : p.deposits t h = X.bankDeposits t h)
    (hretained : p.retainedEquity t h = X.bankRetainedEquity t h)
    (hloanRow : localLoanPricingResidual P X t h = 0)
    (hdepositRow : localDepositPricingResidual P X t h = 0)
    (hbalanceRow : localBankBalanceResidual X t h = 0) :
    expectedBankGrossReturn P X p t h =
      X.loanRate t h * p.retainedEquity t h := by
  rcases hbinary with ⟨hne, hsize, hsupport, hprobMinus, hprobPlus,
    hshockMinus, hshockPlus⟩
  have hbinary' : BinarySymmetricPaymentLaw P paymentMinus paymentPlus paymentSize :=
    ⟨hne, hsize, hsupport, hprobMinus, hprobPlus, hshockMinus, hshockPlus⟩
  have hminusMem : paymentMinus ∈ P.paymentSupport :=
    (hsupport paymentMinus).2 (Or.inl rfl)
  have hplusMem : paymentPlus ∈ P.paymentSupport :=
    (hsupport paymentPlus).2 (Or.inr rfl)
  have hexpectations := binaryStrictSigns_expectations P X t h paymentMinus
    paymentPlus paymentSize hbinary' hminus hplus
  unfold localLoanPricingResidual at hloanRow
  rw [hexpectations.1] at hloanRow
  simp only [localDepositPricingResidual] at hdepositRow
  rw [hexpectations.1, hexpectations.2] at hdepositRow
  unfold localBankBalanceResidual at hbalanceRow
  change finiteSupportExpectation P.paymentSupport P.paymentProbability
      (fun ω ↦ bankGrossReturn P X p ω t h) =
    X.loanRate t h * p.retainedEquity t h
  rw [finiteSupportExpectation_eq_average_of_binarySymmetric P paymentMinus
      paymentPlus paymentSize hbinary']
  rw [bankGrossReturn_eq_detailed_of_candidateFlows P X p t h
      (X.bankTightness t h) hflows paymentMinus hminusMem,
    bankGrossReturn_eq_detailed_of_candidateFlows P X p t h
      (X.bankTightness t h) hflows paymentPlus hplusMem]
  rw [bankDetailedPortfolioReturn_eq_reduced P X t h (X.bankTightness t h)
      (p.loans t h) (p.reservesPre t h) (p.deposits t h) paymentMinus hreserve,
    bankDetailedPortfolioReturn_eq_reduced P X t h (X.bankTightness t h)
      (p.loans t h) (p.reservesPre t h) (p.deposits t h) paymentPlus hreserve]
  rw [hloans, hreserves, hdeposits, hretained]
  unfold bankReducedPortfolioReturn bankReducedPortfolioReturnWithShock
  rw [hshockMinus, hshockPlus]
  unfold localBankSettlementSurplus at hminus hplus
  rw [hshockMinus] at hminus
  rw [hshockPlus] at hplus
  unfold otcLiquidityPayoff
  rw [if_pos hminus, if_neg (not_lt_of_ge hplus.le)]
  unfold bankSettlementSurplus at hminus hplus ⊢
  linear_combination
    X.loanRate t h * hbalanceRow -
      X.reservesPrePayment t h * hloanRow +
      X.bankDeposits t h * hdepositRow

/-- A KKT marginal selector equals the marginal used by the reduced bank rows
when the individual and aggregate settlement surpluses lie strictly on the
same side of the OTC kink.  No conclusion is drawn for a zero-surplus atom. -/
theorem marginalLiquidity_eq_local_of_matching_strict_signs
    {S : Type*} [Fintype S]
    (P : Primitives S) (X : Allocation S) (t : ℕ) (h : History S t)
    (candidateReserves candidateDeposits : ℝ)
    (marginalLiquidity : BankPayment → ℝ)
    (hconcave : bankOTCSurplusSlopeAt P X t h (X.bankTightness t h) ≤
      bankOTCDeficitSlopeAt P X t h (X.bankTightness t h))
    (hsuper : ∀ ω ∈ P.paymentSupport,
      IsOTCLiquiditySupergradient
        (bankOTCDeficitSlopeAt P X t h (X.bankTightness t h))
        (bankOTCSurplusSlopeAt P X t h (X.bankTightness t h))
        (bankSettlementSurplus candidateReserves
          (P.reserveRequirementPath t h)
          (X.depositRate t h / X.reserveRate t h) candidateDeposits
          (P.paymentShock ω)) (marginalLiquidity ω))
    (hsigns : ∀ ω ∈ P.paymentSupport,
      (bankSettlementSurplus candidateReserves
          (P.reserveRequirementPath t h)
          (X.depositRate t h / X.reserveRate t h) candidateDeposits
          (P.paymentShock ω) < 0 ∧
        localBankSettlementSurplus P X t h ω < 0) ∨
      (0 < bankSettlementSurplus candidateReserves
          (P.reserveRequirementPath t h)
          (X.depositRate t h / X.reserveRate t h) candidateDeposits
          (P.paymentShock ω) ∧
        0 < localBankSettlementSurplus P X t h ω)) :
    ∀ ω ∈ P.paymentSupport,
      marginalLiquidity ω = localBankLiquidityMarginal P X t h ω := by
  intro ω hω
  have hcases :=
    (isOTCLiquiditySupergradient_iff_cases hconcave).1 (hsuper ω hω)
  rcases hsigns ω hω with hnegative | hpositive
  · rcases hcases with hcase | hcase | hcase
    · rw [hcase.2]
      unfold localBankLiquidityMarginal otcLiquidityMarginal
      rw [if_pos hnegative.2]
    · linarith [hnegative.1, hcase.1]
    · linarith [hnegative.1, hcase.1]
  · rcases hcases with hcase | hcase | hcase
    · linarith [hpositive.1, hcase.1]
    · linarith [hpositive.1, hcase.1]
    · rw [hcase.2]
      unfold localBankLiquidityMarginal otcLiquidityMarginal
      rw [if_neg (not_lt_of_ge hpositive.2.le)]

/-- The actual KKT equations imply the two reduced pricing rows when both
regulatory caps are strictly slack and the selected marginal is the economic
OTC marginal.  This is only the forward optimality-to-row implication: the two
scalar residuals do not reconstruct feasibility or dynamic optimality. -/
theorem localBankPricingResiduals_eq_zero_of_kkt
    {S : Type*} [Fintype S]
    (P : Primitives S) (X : Allocation S) (t : ℕ) (h : History S t)
    (retainedEquity candidateLoans candidateReserves candidateDeposits : ℝ)
    (marginalLiquidity : BankPayment → ℝ)
    (loanCapDual depositCapDual : ℝ)
    (hkkt : BankSpreadKKTSupportAt P X t h
      (bankOTCDeficitSlopeAt P X t h (X.bankTightness t h))
      (bankOTCSurplusSlopeAt P X t h (X.bankTightness t h))
      retainedEquity candidateLoans candidateReserves candidateDeposits
      marginalLiquidity loanCapDual depositCapDual)
    (hmarginal : ∀ ω ∈ P.paymentSupport,
      marginalLiquidity ω = localBankLiquidityMarginal P X t h ω)
    (hloanSlack : candidateLoans < P.bankLoanCap * retainedEquity)
    (hdepositSlack : candidateDeposits < P.bankDepositCap * retainedEquity) :
    localLoanPricingResidual P X t h = 0 ∧
      localDepositPricingResidual P X t h = 0 := by
  rcases hkkt with ⟨hstatic, _hcovarianceEq, _hcovarianceNonpos,
    _hmomentNonpos, hspread⟩
  rcases hstatic with ⟨hfoc, _hmonotone⟩
  dsimp [BankStaticFOCConditionsAt] at hfoc
  rcases hfoc with ⟨_hloanDualNonneg, _hdepositDualNonneg, _hsuper,
    hloanFOC, _hdepositFOC, hloanComp, hdepositComp⟩
  have hloanDual : loanCapDual = 0 := by
    rcases mul_eq_zero.mp hloanComp with hzero | hzero
    · exact hzero
    · exact (ne_of_gt (sub_pos.mpr hloanSlack) hzero).elim
  have hdepositDual : depositCapDual = 0 := by
    rcases mul_eq_zero.mp hdepositComp with hzero | hzero
    · exact hzero
    · exact (ne_of_gt (sub_pos.mpr hdepositSlack) hzero).elim
  have hexpectation :
      finiteSupportExpectation P.paymentSupport P.paymentProbability
          marginalLiquidity =
        finiteSupportExpectation P.paymentSupport P.paymentProbability
          (localBankLiquidityMarginal P X t h) := by
    unfold finiteSupportExpectation
    apply Finset.sum_congr rfl
    intro ω hω
    rw [hmarginal ω hω]
  have hmoment :
      finiteSupportExpectation P.paymentSupport P.paymentProbability
          (fun ω ↦ marginalLiquidity ω * P.paymentShock ω) =
        finiteSupportExpectation P.paymentSupport P.paymentProbability
          (fun ω ↦ localBankLiquidityMarginal P X t h ω *
            P.paymentShock ω) := by
    unfold finiteSupportExpectation
    apply Finset.sum_congr rfl
    intro ω hω
    simp only
    rw [hmarginal ω hω]
  constructor
  · unfold localLoanPricingResidual
    rw [← hexpectation]
    linarith [hloanFOC]
  · unfold localDepositPricingResidual
    rw [hexpectation, hmoment, hloanDual, hdepositDual] at hspread
    linarith

/-- Compose the literal local Bellman comparison, the proved nonsmooth KKT
theorem, strict sign matching and slack caps to obtain the two actual reduced
bank-pricing rows.  Population transport and the reverse implication remain
separate obligations. -/
theorem localBankPricingResiduals_eq_zero_of_bellman_interior
    {S : Type*} [Fintype S] [DecidableEq S]
    (P : Primitives S) (X : Allocation S) (p : BankPlan S)
    (t : ℕ) (h : History S t) (bankValue : BankValueProcess S)
    (hhomogeneous : BankValueHomogeneousAt P t h bankValue)
    (henvironment : BankBellmanLocalEnvironmentAt P X t h p
      (X.bankTightness t h) bankValue)
    (hreserveRate : 0 < X.reserveRate t h)
    (hsurplusSlope : 0 ≤
      bankOTCSurplusSlopeAt P X t h (X.bankTightness t h))
    (hconcave : bankOTCSurplusSlopeAt P X t h (X.bankTightness t h) ≤
      bankOTCDeficitSlopeAt P X t h (X.bankTightness t h))
    (hxi : P.reserveRequirementPath t h <
      X.depositRate t h / X.reserveRate t h)
    (hequity : 0 < p.retainedEquity t h)
    (hinterior : 0 < p.loans t h ∧ 0 < p.reservesPre t h ∧
      0 < p.deposits t h)
    (hinflation : ∀ s, 0 < P.tree.transition (currentState h) s →
      0 < X.inflation (t + 1) (childHistory h s))
    (hstrictSolvency : ∀ ω ∈ P.paymentSupport, ∀ s,
      0 < P.tree.transition (currentState h) s →
      0 < bankRealPortfolioReturnAt P X t h
        (bankOTCDeficitSlopeAt P X t h (X.bankTightness t h))
        (bankOTCSurplusSlopeAt P X t h (X.bankTightness t h))
        (p.loans t h) (p.reservesPre t h) (p.deposits t h) ω s)
    (hsigns : ∀ ω ∈ P.paymentSupport,
      (bankSettlementSurplus (p.reservesPre t h)
          (P.reserveRequirementPath t h)
          (X.depositRate t h / X.reserveRate t h) (p.deposits t h)
          (P.paymentShock ω) < 0 ∧
        localBankSettlementSurplus P X t h ω < 0) ∨
      (0 < bankSettlementSurplus (p.reservesPre t h)
          (P.reserveRequirementPath t h)
          (X.depositRate t h / X.reserveRate t h) (p.deposits t h)
          (P.paymentShock ω) ∧
        0 < localBankSettlementSurplus P X t h ω))
    (hloanSlack : p.loans t h < P.bankLoanCap * p.retainedEquity t h)
    (hdepositSlack : p.deposits t h <
      P.bankDepositCap * p.retainedEquity t h) :
    localLoanPricingResidual P X t h = 0 ∧
      localDepositPricingResidual P X t h = 0 := by
  have hfeasible := henvironment.2.2.2.2.2.1
  have hstaticOptimal := bankStaticPortfolioOptimal_of_bellman P X p t h
    (X.bankTightness t h) bankValue hhomogeneous henvironment
  obtain ⟨marginalLiquidity, loanCapDual, depositCapDual, hkkt⟩ :=
    bankSpreadKKTSupport_of_interior P X t h
      (bankOTCDeficitSlopeAt P X t h (X.bankTightness t h))
      (bankOTCSurplusSlopeAt P X t h (X.bankTightness t h))
      (p.retainedEquity t h) (p.loans t h) (p.reservesPre t h)
      (p.deposits t h) hreserveRate hsurplusSlope hconcave hxi hfeasible
      hequity hinterior hinflation hstrictSolvency hstaticOptimal
  have hsuper := hkkt.1.1.2.2.1
  have hmarginal := marginalLiquidity_eq_local_of_matching_strict_signs
    P X t h (p.reservesPre t h) (p.deposits t h) marginalLiquidity
    hconcave hsuper hsigns
  exact localBankPricingResiduals_eq_zero_of_kkt P X t h
    (p.retainedEquity t h) (p.loans t h) (p.reservesPre t h)
    (p.deposits t h) marginalLiquidity loanCapDual depositCapDual hkkt
    hmarginal hloanSlack hdepositSlack

/-- Every represented bank type has the witness's common payment law and
regulatory caps.  Together with the normalized-portfolio equalities below,
this is the source homogeneity reduction from a type population to aggregate
bank ratios. -/
def BankPopulationSharesPrimitiveLaw {J : Type*}
    (P : Primitives S) (B : BankPopulationCandidate S J) : Prop :=
  ∀ j,
    (B.paymentLaw j).support = P.paymentSupport ∧
    (B.paymentLaw j).probability = P.paymentProbability ∧
    (B.paymentLaw j).shock = P.paymentShock ∧
    (B.paymentLaw j).depositCap = P.bankDepositCap ∧
    (B.paymentLaw j).loanCap = P.bankLoanCap

theorem massOneFullRetentionBankPopulation_sharesPrimitiveLaw
    (P : Primitives S) (I : InheritedState) (X : Allocation S)
    (bankValue : BankValueProcess S) :
    BankPopulationSharesPrimitiveLaw P
      (massOneFullRetentionBankPopulation P I X bankValue) := by
  intro j
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- One type in the finite bank population implies the two aggregate pricing
residuals when its payment law is the common primitive law, its literal dynamic
analytic data are supplied, and the local experiment verifies the strict
interior/sign conditions.  Homogeneity and the local Bellman environment are
derived here; neither is read from `BankOptimalWithValue`.  The result does not
infer the converse from the two scalar rows. -/
theorem localBankPricingResiduals_eq_zero_of_population_type
    {J : Type*} [Fintype J] [DecidableEq J]
    (P : Primitives S) (I : InheritedState) (X : Allocation S)
    (B : BankPopulationCandidate S J)
    (H : BankPopulationFiniteRowEnvironmentFor P I X B)
    (hlaw : BankPopulationSharesPrimitiveLaw P B)
    (j : J) (t : ℕ) (h : History S t)
    (hdynamicData : BankPopulationDynamicBellmanDataAt P X B t h)
    (hs : FirmHistoryAdmissible P t h)
    (htightness : 0 < X.bankTightness t h)
    (hconsumption : 0 < X.workerConsumption t h)
    (hchildConsumption : ∀ s,
      0 < P.tree.transition (currentState h) s →
      0 < X.workerConsumption (t + 1) (childHistory h s))
    (hreserveRate : 0 < X.reserveRate t h)
    (hsurplusSlope : 0 ≤
      bankOTCSurplusSlopeAt P X t h (X.bankTightness t h))
    (hconcave : bankOTCSurplusSlopeAt P X t h (X.bankTightness t h) ≤
      bankOTCDeficitSlopeAt P X t h (X.bankTightness t h))
    (hxi : P.reserveRequirementPath t h <
      X.depositRate t h / X.reserveRate t h)
    (hinterior : 0 < (B.plan j).loans t h ∧
      0 < (B.plan j).reservesPre t h ∧ 0 < (B.plan j).deposits t h)
    (hinflation : ∀ s, 0 < P.tree.transition (currentState h) s →
      0 < X.inflation (t + 1) (childHistory h s))
    (hstrictSolvency : ∀ ω ∈ P.paymentSupport, ∀ s,
      0 < P.tree.transition (currentState h) s →
      0 < bankRealPortfolioReturnAt P X t h
        (bankOTCDeficitSlopeAt P X t h (X.bankTightness t h))
        (bankOTCSurplusSlopeAt P X t h (X.bankTightness t h))
        ((B.plan j).loans t h) ((B.plan j).reservesPre t h)
        ((B.plan j).deposits t h) ω s)
    (hsigns : ∀ ω ∈ P.paymentSupport,
      (bankSettlementSurplus ((B.plan j).reservesPre t h)
          (P.reserveRequirementPath t h)
          (X.depositRate t h / X.reserveRate t h) ((B.plan j).deposits t h)
          (P.paymentShock ω) < 0 ∧
        localBankSettlementSurplus P X t h ω < 0) ∨
      (0 < bankSettlementSurplus ((B.plan j).reservesPre t h)
          (P.reserveRequirementPath t h)
          (X.depositRate t h / X.reserveRate t h) ((B.plan j).deposits t h)
          (P.paymentShock ω) ∧
        0 < localBankSettlementSurplus P X t h ω))
    (hloanSlack : (B.plan j).loans t h <
      P.bankLoanCap * (B.plan j).retainedEquity t h)
    (hdepositSlack : (B.plan j).deposits t h <
      P.bankDepositCap * (B.plan j).retainedEquity t h) :
    localLoanPricingResidual P X t h = 0 ∧
      localDepositPricingResidual P X t h = 0 := by
  rcases H with ⟨_hmass, hfeasible, _haggregate, _hotc⟩
  rcases hlaw j with ⟨hsupport, hprobability, hshock, hdepositCap, hloanCap⟩
  have hprimitive : P.withBankPaymentLaw (B.paymentLaw j) = P :=
    Primitives.withBankPaymentLaw_eq P (B.paymentLaw j) hsupport hprobability
      hshock hdepositCap hloanCap
  have hfeasibleP : BankFeasible P
      (I.withBankFace (B.initialFace j)) X (B.plan j) := by
    simpa [hprimitive] using hfeasible j
  have hdataP : BankDynamicBellmanDataAt P X (B.plan j) t h (B.value j) := by
    simpa [hprimitive] using hdynamicData j
  rcases hdataP with ⟨candidate, hstarts, hcontinuationOptimal, hdynamic,
    hcurrentValue, hexit, hvalueNonneg, htail⟩
  have hhomogeneous : BankValueHomogeneousAt P t h (B.value j) :=
    bankValueHomogeneous_of_dynamicPolicyConditions P X t h (B.value j) hdynamic
  have hequity : 0 < (B.plan j).retainedEquity t h :=
    (hfeasibleP.1 t h hs).2.2.1
  have henvironment := bankBellmanLocalEnvironmentAt_of_continuationOptimality
    P X (B.plan j) t h (B.value j) candidate hstarts hcontinuationOptimal
    hdynamic hcurrentValue hequity htightness hconsumption hchildConsumption
    hinflation hexit hvalueNonneg htail
  exact localBankPricingResiduals_eq_zero_of_bellman_interior P X (B.plan j)
    t h (B.value j) hhomogeneous henvironment hreserveRate hsurplusSlope
    hconcave hxi hequity hinterior hinflation hstrictSolvency hsigns
    hloanSlack hdepositSlack

/-- Strict local banking and household margins at one prefix history.  The
candidate remains the full dynamic bank-population equilibrium; this predicate
only states the source region in which the two closed-form bank rows are
obtained.  In particular the payment signs and slack caps are checked for each
bank type, not inferred from an aggregate balance. -/
def LocalMacroStrictBankRegimeAt {J : Type*} [Fintype J]
    (P : Primitives S) (X : Allocation S) (B : BankPopulationCandidate S J)
    (t : ℕ) (h : History S t) (paymentMinus paymentPlus : BankPayment) : Prop :=
  FirmHistoryAdmissible P t h ∧
  0 < X.bankTightness t h ∧ X.bankTightness t h < 1 ∧
  0 < X.reserveRate t h ∧ X.reserveRate t h < X.depositRate t h ∧
  X.depositRate t h < X.loanRate t h ∧
  X.loanRate t h < X.facilityRate t h ∧
  0 ≤ P.reserveRequirementPath t h ∧
  P.reserveRequirementPath t h < X.depositRate t h / X.reserveRate t h ∧
  X.bankDividend t h = 0 ∧ X.bankRetainedEquity t h = X.bankEquity t h ∧
  0 < X.bankEquity t h ∧ 0 < X.bankLoans t h ∧
  0 < X.reservesPrePayment t h ∧ 0 < X.bankDeposits t h ∧
  0 < X.householdDeposits t h ∧ 0 < X.householdBonds t h ∧
  (∀ i, 0 < X.loan i t h ∧ X.firmDeposit i t h = 0) ∧
  (∀ j,
    (B.plan j).dividend t h = 0 ∧
    (B.plan j).retainedEquity t h = (B.plan j).equity t h ∧
    0 < (B.plan j).retainedEquity t h ∧
    0 < (B.plan j).loans t h ∧ 0 < (B.plan j).reservesPre t h ∧
    0 < (B.plan j).deposits t h ∧
    (B.plan j).deposits t h <
      (B.paymentLaw j).depositCap * (B.plan j).retainedEquity t h ∧
    (B.plan j).loans t h <
      (B.paymentLaw j).loanCap * (B.plan j).retainedEquity t h ∧
    bankSettlementSurplus ((B.plan j).reservesPre t h)
        (P.reserveRequirementPath t h)
        (X.depositRate t h / X.reserveRate t h) ((B.plan j).deposits t h)
        ((B.paymentLaw j).shock paymentMinus) < 0 ∧
    0 < bankSettlementSurplus ((B.plan j).reservesPre t h)
        (P.reserveRequirementPath t h)
        (X.depositRate t h / X.reserveRate t h) ((B.plan j).deposits t h)
        ((B.paymentLaw j).shock paymentPlus) ∧
    (B.plan j).loans t h * X.bankRetainedEquity t h =
      X.bankLoans t h * (B.plan j).retainedEquity t h ∧
    (B.plan j).reservesPre t h * X.bankRetainedEquity t h =
      X.reservesPrePayment t h * (B.plan j).retainedEquity t h ∧
    (B.plan j).deposits t h * X.bankRetainedEquity t h =
      X.bankDeposits t h * (B.plan j).retainedEquity t h ∧
    ∀ ω ∈ (B.paymentLaw j).support, ∀ s,
      0 < P.tree.transition (currentState h) s →
      0 < bankGrossReturn (P.withBankPaymentLaw (B.paymentLaw j)) X
        (B.plan j) ω t h /
          X.inflation (t + 1) (childHistory h s))

/-- The binary strict-sign conditions give strictly positive aggregate deficit
and surplus supplies.  Thus the finite interior experiment cannot fall into
either OTC no-trade corner. -/
theorem bankSupplies_pos_of_binary_strict
    {J : Type*} [Fintype J] [DecidableEq J]
    (P : Primitives S) (X : Allocation S) (B : BankPopulationCandidate S J)
    (t : ℕ) (h : History S t)
    (paymentMinus paymentPlus : BankPayment) (paymentSize : ℝ) (j : J)
    (hmass : ∀ k, 0 < B.mass k)
    (hlaw : BankPopulationSharesPrimitiveLaw P B)
    (hbinary : BinarySymmetricPaymentLaw P paymentMinus paymentPlus paymentSize)
    (hregime : LocalMacroStrictBankRegimeAt P X B t h
      paymentMinus paymentPlus) :
    0 < bankDeficitSupplyAt P X t h B.mass
        (fun k ↦ (B.plan k).reservesPre t h)
        (fun k ↦ (B.plan k).deposits t h)
        (fun k ↦ (B.paymentLaw k).support)
        (fun k ↦ (B.paymentLaw k).probability)
        (fun k ↦ (B.paymentLaw k).shock) ∧
      0 < bankSurplusSupplyAt P X t h B.mass
        (fun k ↦ (B.plan k).reservesPre t h)
        (fun k ↦ (B.plan k).deposits t h)
        (fun k ↦ (B.paymentLaw k).support)
        (fun k ↦ (B.paymentLaw k).probability)
        (fun k ↦ (B.paymentLaw k).shock) := by
  classical
  rcases hregime with ⟨_hs, _htightness, _htightnessLt, _hreserveRate,
    _hreserveDeposit, _hdepositLoan, _hloanFacility, _hrhoNonneg, _hxi,
    _hdividend, _hretainedEq, _hbankEquity, _hbankLoans, _hbankReserves,
    _hbankDeposits, _hhouseholdDeposits, _hhouseholdBonds, _hfirms,
    htype⟩
  rcases hlaw j with ⟨hsupport, _hprobability, _hshock, _hdepositCap, _hloanCap⟩
  have hminusMemP : paymentMinus ∈ P.paymentSupport :=
    (hbinary.2.2.1 paymentMinus).2 (Or.inl rfl)
  have hplusMemP : paymentPlus ∈ P.paymentSupport :=
    (hbinary.2.2.1 paymentPlus).2 (Or.inr rfl)
  have hminusMem : paymentMinus ∈ (B.paymentLaw j).support := by
    simpa [hsupport] using hminusMemP
  have hplusMem : paymentPlus ∈ (B.paymentLaw j).support := by
    simpa [hsupport] using hplusMemP
  rcases htype j with ⟨_hdividendJ, _hretainedJ, _hretainedPos,
    _hloansPos, _hreservesPos, _hdepositsPos, _hdepositSlack, _hloanSlack,
    hminus, hplus, _hloansShare, _hreservesShare, _hdepositsShare,
    _hgrossStrict⟩
  have hdeficitExpectationNonneg : ∀ k, 0 ≤
      finiteSupportExpectation (B.paymentLaw k).support
        (B.paymentLaw k).probability (fun ω ↦
          max (-bankSettlementSurplus ((B.plan k).reservesPre t h)
            (P.reserveRequirementPath t h)
            (X.depositRate t h / X.reserveRate t h)
            ((B.plan k).deposits t h) ((B.paymentLaw k).shock ω)) 0) := by
    intro k
    unfold finiteSupportExpectation
    apply Finset.sum_nonneg
    intro ω hω
    exact mul_nonneg ((B.paymentLaw k).probability_nonneg ω)
      (le_max_right _ _)
  have hsurplusExpectationNonneg : ∀ k, 0 ≤
      finiteSupportExpectation (B.paymentLaw k).support
        (B.paymentLaw k).probability (fun ω ↦
          max (bankSettlementSurplus ((B.plan k).reservesPre t h)
            (P.reserveRequirementPath t h)
            (X.depositRate t h / X.reserveRate t h)
            ((B.plan k).deposits t h) ((B.paymentLaw k).shock ω)) 0) := by
    intro k
    unfold finiteSupportExpectation
    apply Finset.sum_nonneg
    intro ω hω
    exact mul_nonneg ((B.paymentLaw k).probability_nonneg ω)
      (le_max_right _ _)
  have hdeficitExpectation : 0 <
      finiteSupportExpectation (B.paymentLaw j).support
        (B.paymentLaw j).probability (fun ω ↦
          max (-bankSettlementSurplus ((B.plan j).reservesPre t h)
            (P.reserveRequirementPath t h)
            (X.depositRate t h / X.reserveRate t h)
            ((B.plan j).deposits t h) ((B.paymentLaw j).shock ω)) 0) := by
    unfold finiteSupportExpectation
    apply Finset.sum_pos'
    · intro ω hω
      exact mul_nonneg ((B.paymentLaw j).probability_nonneg ω)
        (le_max_right _ _)
    · refine ⟨paymentMinus, hminusMem, ?_⟩
      apply mul_pos ((B.paymentLaw j).probability_pos_on_support _ hminusMem)
      change 0 < max (-bankSettlementSurplus ((B.plan j).reservesPre t h)
        (P.reserveRequirementPath t h)
        (X.depositRate t h / X.reserveRate t h) ((B.plan j).deposits t h)
        ((B.paymentLaw j).shock paymentMinus)) 0
      rw [max_eq_left (neg_nonneg.mpr hminus.le)]
      linarith
  have hsurplusExpectation : 0 <
      finiteSupportExpectation (B.paymentLaw j).support
        (B.paymentLaw j).probability (fun ω ↦
          max (bankSettlementSurplus ((B.plan j).reservesPre t h)
            (P.reserveRequirementPath t h)
            (X.depositRate t h / X.reserveRate t h)
            ((B.plan j).deposits t h) ((B.paymentLaw j).shock ω)) 0) := by
    unfold finiteSupportExpectation
    apply Finset.sum_pos'
    · intro ω hω
      exact mul_nonneg ((B.paymentLaw j).probability_nonneg ω)
        (le_max_right _ _)
    · refine ⟨paymentPlus, hplusMem, ?_⟩
      apply mul_pos ((B.paymentLaw j).probability_pos_on_support _ hplusMem)
      change 0 < max (bankSettlementSurplus ((B.plan j).reservesPre t h)
        (P.reserveRequirementPath t h)
        (X.depositRate t h / X.reserveRate t h) ((B.plan j).deposits t h)
        ((B.paymentLaw j).shock paymentPlus)) 0
      rw [max_eq_left hplus.le]
      exact hplus
  constructor
  · unfold bankDeficitSupplyAt
    apply Finset.sum_pos'
    · intro k _hk
      exact mul_nonneg (hmass k).le (hdeficitExpectationNonneg k)
    · exact ⟨j, Finset.mem_univ j, mul_pos (hmass j) hdeficitExpectation⟩
  · unfold bankSurplusSupplyAt
    apply Finset.sum_pos'
    · intro k _hk
      exact mul_nonneg (hmass k).le (hsurplusExpectationNonneg k)
    · exact ⟨j, Finset.mem_univ j, mul_pos (hmass j) hsurplusExpectation⟩

/-- In the finite binary interior experiment, the dynamic bank population,
positive bilateral OTC supplies and the checked strict regime imply the three
bank rows of the 33-equation prefix.  This is the forward implication only:
the rows do not reconstruct individual feasibility, Bellman optimality or a
full recurrent equilibrium. -/
theorem localFiniteBankRows_eq_zero_of_population_of_positive_supplies
    {J : Type*} [Fintype J] [DecidableEq J]
    (P : Primitives S) (I : InheritedState) (X : Allocation S)
    (B : BankPopulationCandidate S J)
    (t : ℕ) (h : History S t)
    (paymentMinus paymentPlus : BankPayment) (paymentSize : ℝ) (j : J)
    (H : BankPopulationFiniteRowEnvironmentFor P I X B)
    (hlaw : BankPopulationSharesPrimitiveLaw P B)
    (hdynamicData : BankPopulationDynamicBellmanDataAt P X B t h)
    (hbinary : BinarySymmetricPaymentLaw P paymentMinus paymentPlus paymentSize)
    (hregime : LocalMacroStrictBankRegimeAt P X B t h
      paymentMinus paymentPlus)
    (hpositive : PositiveDomain P X)
    (hdeficit : 0 < bankDeficitSupplyAt P X t h B.mass
      (fun k ↦ (B.plan k).reservesPre t h)
      (fun k ↦ (B.plan k).deposits t h)
      (fun k ↦ (B.paymentLaw k).support)
      (fun k ↦ (B.paymentLaw k).probability)
      (fun k ↦ (B.paymentLaw k).shock))
    (hsurplus : 0 < bankSurplusSupplyAt P X t h B.mass
      (fun k ↦ (B.plan k).reservesPre t h)
      (fun k ↦ (B.plan k).deposits t h)
      (fun k ↦ (B.paymentLaw k).support)
      (fun k ↦ (B.paymentLaw k).probability)
      (fun k ↦ (B.paymentLaw k).shock)) :
    localLoanPricingResidual P X t h = 0 ∧
      localDepositPricingResidual P X t h = 0 ∧
      localBankBalanceResidual X t h = 0 := by
  rcases hregime with ⟨hs, htightness, _htightnessLt, hreserveRate,
    hreserveDeposit, hdepositLoan, hloanFacility, _hrhoNonneg, hxi,
    _hdividend, hretainedEq, hbankEquity, _hbankLoans, _hbankReserves,
    _hbankDeposits, _hhouseholdDeposits, _hhouseholdBonds, _hfirms,
    htype⟩
  rcases H with ⟨hmass, hfeasible, haggregate, hotc⟩
  have Hcopy : BankPopulationFiniteRowEnvironmentFor P I X B :=
    ⟨hmass, hfeasible, haggregate, hotc⟩
  have hactive := bankPopulationOTCRegimeAt_bilateral P X B t h
    (hotc t h hs) hdeficit hsurplus
  have hcorridor : X.reserveRate t h < X.facilityRate t h :=
    lt_trans hreserveDeposit (lt_trans hdepositLoan hloanFacility)
  have hslopes0 := otcSlopes_ordered (X.reserveRate t h)
    (X.facilityRate t h) P.matchingIntensity (X.bankTightness t h)
    hcorridor P.matching_intensity_pos htightness
  have hslopes : 0 ≤
        bankOTCSurplusSlopeAt P X t h (X.bankTightness t h) ∧
      bankOTCSurplusSlopeAt P X t h (X.bankTightness t h) ≤
        bankOTCDeficitSlopeAt P X t h (X.bankTightness t h) := by
    unfold bankOTCSurplusSlopeAt bankOTCDeficitSlopeAt
    rw [hactive.2.2]
    exact hslopes0
  have hinflation : ∀ s, 0 < P.tree.transition (currentState h) s →
      0 < X.inflation (t + 1) (childHistory h s) := by
    intro s htransition
    apply (hpositive (t + 1) (childHistory h s) ?_).2.2.2.2.2.2.1
    unfold FirmHistoryAdmissible at hs ⊢
    simp only [FiniteMarkovTree.historyWeight]
    simpa [previousHistory, childHistory, currentState] using
      mul_pos hs htransition
  rcases hlaw j with ⟨hsupport, hprobability, hshock, hdepositCap, hloanCap⟩
  have hprimitive : P.withBankPaymentLaw (B.paymentLaw j) = P :=
    Primitives.withBankPaymentLaw_eq P (B.paymentLaw j) hsupport hprobability
      hshock hdepositCap hloanCap
  have hflows : BankCandidateOTCFlowsAt P X (B.plan j) t h
      (X.bankTightness t h) := by
    simpa [hprimitive] using hactive.2.1 j
  rcases htype j with ⟨_hdividendJ, _hretainedJ, hretainedPos,
    hloansPos, hreservesPos, hdepositsPos, hdepositSlack0, hloanSlack0,
    hminus0, hplus0, _hloansShare, hreservesShare, hdepositsShare,
    hgrossStrict⟩
  have hdepositSlack : (B.plan j).deposits t h <
      P.bankDepositCap * (B.plan j).retainedEquity t h := by
    simpa [hdepositCap] using hdepositSlack0
  have hloanSlack : (B.plan j).loans t h <
      P.bankLoanCap * (B.plan j).retainedEquity t h := by
    simpa [hloanCap] using hloanSlack0
  have hstrictSolvency : ∀ ω ∈ P.paymentSupport, ∀ s,
      0 < P.tree.transition (currentState h) s →
      0 < bankRealPortfolioReturnAt P X t h
        (bankOTCDeficitSlopeAt P X t h (X.bankTightness t h))
        (bankOTCSurplusSlopeAt P X t h (X.bankTightness t h))
        ((B.plan j).loans t h) ((B.plan j).reservesPre t h)
        ((B.plan j).deposits t h) ω s := by
    intro ω hω s htransition
    have hωj : ω ∈ (B.paymentLaw j).support := by simpa [hsupport] using hω
    have hactual := hgrossStrict ω hωj s htransition
    have hactualP : 0 < bankGrossReturn P X (B.plan j) ω t h /
        X.inflation (t + 1) (childHistory h s) := by
      simpa [hprimitive] using hactual
    rw [bankGrossReturn_eq_reduced_of_candidateFlows P X (B.plan j) t h
      (X.bankTightness t h) hflows hreserveRate.ne' ω hω] at hactualP
    exact hactualP
  have haggregateRetained : 0 < X.bankRetainedEquity t h := by
    rw [hretainedEq]
    exact hbankEquity
  have hscaledSurplus : ∀ ω,
      bankSettlementSurplus ((B.plan j).reservesPre t h)
          (P.reserveRequirementPath t h)
          (X.depositRate t h / X.reserveRate t h) ((B.plan j).deposits t h)
          (P.paymentShock ω) * X.bankRetainedEquity t h =
        localBankSettlementSurplus P X t h ω *
          (B.plan j).retainedEquity t h := by
    intro ω
    unfold localBankSettlementSurplus bankSettlementSurplus
    linear_combination hreservesShare +
      (-P.reserveRequirementPath t h +
        (X.depositRate t h / X.reserveRate t h -
          P.reserveRequirementPath t h) * P.paymentShock ω) * hdepositsShare
  have hminus : bankSettlementSurplus ((B.plan j).reservesPre t h)
      (P.reserveRequirementPath t h)
      (X.depositRate t h / X.reserveRate t h) ((B.plan j).deposits t h)
      (P.paymentShock paymentMinus) < 0 := by
    simpa [hshock] using hminus0
  have hplus : 0 < bankSettlementSurplus ((B.plan j).reservesPre t h)
      (P.reserveRequirementPath t h)
      (X.depositRate t h / X.reserveRate t h) ((B.plan j).deposits t h)
      (P.paymentShock paymentPlus) := by
    simpa [hshock] using hplus0
  have haggregateMinus : localBankSettlementSurplus P X t h paymentMinus < 0 := by
    have hproduct : localBankSettlementSurplus P X t h paymentMinus *
        (B.plan j).retainedEquity t h < 0 := by
      rw [← hscaledSurplus paymentMinus]
      exact mul_neg_of_neg_of_pos hminus haggregateRetained
    rcases (mul_neg_iff.mp hproduct) with hcase | hcase
    · exact (not_lt_of_ge hretainedPos.le hcase.2).elim
    · exact hcase.1
  have haggregatePlus : 0 < localBankSettlementSurplus P X t h paymentPlus := by
    have hproduct : 0 < localBankSettlementSurplus P X t h paymentPlus *
        (B.plan j).retainedEquity t h := by
      rw [← hscaledSurplus paymentPlus]
      exact mul_pos hplus haggregateRetained
    rcases (mul_pos_iff.mp hproduct) with hcase | hcase
    · exact hcase.1
    · exact (not_lt_of_ge hretainedPos.le hcase.2).elim
  have hsigns : ∀ ω ∈ P.paymentSupport,
      (bankSettlementSurplus ((B.plan j).reservesPre t h)
          (P.reserveRequirementPath t h)
          (X.depositRate t h / X.reserveRate t h) ((B.plan j).deposits t h)
          (P.paymentShock ω) < 0 ∧
        localBankSettlementSurplus P X t h ω < 0) ∨
      (0 < bankSettlementSurplus ((B.plan j).reservesPre t h)
          (P.reserveRequirementPath t h)
          (X.depositRate t h / X.reserveRate t h) ((B.plan j).deposits t h)
          (P.paymentShock ω) ∧
        0 < localBankSettlementSurplus P X t h ω) := by
    intro ω hω
    rcases (hbinary.2.2.1 ω).mp hω with rfl | rfl
    · exact Or.inl ⟨hminus, haggregateMinus⟩
    · exact Or.inr ⟨hplus, haggregatePlus⟩
  have hconsumption : 0 < X.workerConsumption t h :=
    (hpositive t h hs).1
  have hchildConsumption : ∀ s,
      0 < P.tree.transition (currentState h) s →
      0 < X.workerConsumption (t + 1) (childHistory h s) := by
    intro s htransition
    apply (hpositive (t + 1) (childHistory h s) ?_).1
    unfold FirmHistoryAdmissible at hs ⊢
    simp only [FiniteMarkovTree.historyWeight]
    simpa [previousHistory, childHistory, currentState] using
      mul_pos hs htransition
  have hpricing := localBankPricingResiduals_eq_zero_of_population_type
    P I X B Hcopy hlaw j t h hdynamicData hs htightness hconsumption
    hchildConsumption hreserveRate hslopes.1 hslopes.2 hxi
    ⟨hloansPos, hreservesPos, hdepositsPos⟩ hinflation hstrictSolvency hsigns
    hloanSlack hdepositSlack
  exact ⟨hpricing.1, hpricing.2,
    localBankBalanceResidual_eq_zero_of_finiteRowEnvironment P I X B Hcopy
      t h hs⟩

/-- The strict binary population regime itself supplies the positive bilateral
OTC quantities needed by the preceding theorem.  Hence no extra market-activity
assumption is exposed at the finite-prefix boundary. -/
theorem localFiniteBankRows_eq_zero_of_population
    {J : Type*} [Fintype J] [DecidableEq J]
    (P : Primitives S) (I : InheritedState) (X : Allocation S)
    (B : BankPopulationCandidate S J)
    (t : ℕ) (h : History S t)
    (paymentMinus paymentPlus : BankPayment) (paymentSize : ℝ) (j : J)
    (H : BankPopulationFiniteRowEnvironmentFor P I X B)
    (hlaw : BankPopulationSharesPrimitiveLaw P B)
    (hdynamicData : BankPopulationDynamicBellmanDataAt P X B t h)
    (hbinary : BinarySymmetricPaymentLaw P paymentMinus paymentPlus paymentSize)
    (hregime : LocalMacroStrictBankRegimeAt P X B t h
      paymentMinus paymentPlus)
    (hpositive : PositiveDomain P X) :
    localLoanPricingResidual P X t h = 0 ∧
      localDepositPricingResidual P X t h = 0 ∧
      localBankBalanceResidual X t h = 0 := by
  have hsupplies := bankSupplies_pos_of_binary_strict P X B t h
    paymentMinus paymentPlus paymentSize j (fun k ↦ (H.1 k).1)
    hlaw hbinary hregime
  exact localFiniteBankRows_eq_zero_of_population_of_positive_supplies
    P I X B t h paymentMinus paymentPlus paymentSize j H hlaw hdynamicData
    hbinary hregime hpositive hsupplies.1 hsupplies.2

/-- Full prefix banking witness at dates zero and one.  It exposes the actual
population used by the competitive equilibrium and the common binary law,
rather than silently applying binary representative-bank formulas to the
general heterogeneous carrier. -/
def LocalMacroStrictBankRegime
    (P : Primitives S) (I : InheritedState) (X : Allocation S)
    (dateOne : S) : Prop :=
    ∃ n : ℕ, ∃ B : BankPopulationCandidate S (Fin (n + 1)),
    ∃ paymentMinus paymentPlus : BankPayment, ∃ paymentSize : ℝ,
      BankPopulationEquilibriumFor P I X B ∧
      BankPopulationSharesPrimitiveLaw P B ∧
      BinarySymmetricPaymentLaw P paymentMinus paymentPlus paymentSize ∧
      LocalMacroStrictBankRegimeAt P X B 0 (bridgeDateZeroHistory P)
        paymentMinus paymentPlus ∧
      LocalMacroStrictBankRegimeAt P X B 1 (bridgeDateOneHistory P dateOne)
        paymentMinus paymentPlus

/-- The strict finite bank witness together with the genuinely dynamic analytic
data at both prefix dates.  Keeping this separate from
`LocalMacroStrictBankRegime` makes explicit that sign/interiority checks alone
do not establish value attainment, dominance, tail summability or terminality. -/
def FiniteBankPrefixDynamicWitness
    (P : Primitives S) (I : InheritedState) (X : Allocation S)
    (dateOne : S) : Prop :=
  ∃ n : ℕ, ∃ B : BankPopulationCandidate S (Fin (n + 1)),
    ∃ paymentMinus paymentPlus : BankPayment, ∃ paymentSize : ℝ,
      BankPopulationFiniteRowEnvironmentFor P I X B ∧
      BankPopulationSharesPrimitiveLaw P B ∧
      BinarySymmetricPaymentLaw P paymentMinus paymentPlus paymentSize ∧
      LocalMacroStrictBankRegimeAt P X B 0 (bridgeDateZeroHistory P)
        paymentMinus paymentPlus ∧
      LocalMacroStrictBankRegimeAt P X B 1 (bridgeDateOneHistory P dateOne)
        paymentMinus paymentPlus ∧
      BankPopulationDynamicBellmanDataAt P X B 0
        (bridgeDateZeroHistory P) ∧
      BankPopulationDynamicBellmanDataAt P X B 1
        (bridgeDateOneHistory P dateOne)

/-- The finite experiment's strict witness and explicit dynamic analytic data
close rows 8, 9 and 10 at both prefix dates.  This remains only the forward
equilibrium-to-reduced-system implication. -/
theorem localPrefixBankRows_eq_zero_of_dynamic_witness
    (P : Primitives S) (I : InheritedState) (X : Allocation S)
    (dateOne : S)
    (hwitness : FiniteBankPrefixDynamicWitness P I X dateOne)
    (hpositive : PositiveDomain P X) :
    (localLoanPricingResidual P X 0 (bridgeDateZeroHistory P) = 0 ∧
      localDepositPricingResidual P X 0 (bridgeDateZeroHistory P) = 0 ∧
      localBankBalanceResidual X 0 (bridgeDateZeroHistory P) = 0) ∧
    (localLoanPricingResidual P X 1 (bridgeDateOneHistory P dateOne) = 0 ∧
      localDepositPricingResidual P X 1 (bridgeDateOneHistory P dateOne) = 0 ∧
      localBankBalanceResidual X 1 (bridgeDateOneHistory P dateOne) = 0) := by
  rcases hwitness with ⟨n, B, paymentMinus, paymentPlus, paymentSize,
    H, hlaw, hbinary, hzero, hone, hdynamicZero, hdynamicOne⟩
  have hz := localFiniteBankRows_eq_zero_of_population P I X B 0
    (bridgeDateZeroHistory P) paymentMinus paymentPlus paymentSize
    (0 : Fin (n + 1)) H hlaw hdynamicZero hbinary hzero hpositive
  have ho := localFiniteBankRows_eq_zero_of_population P I X B 1
    (bridgeDateOneHistory P dateOne) paymentMinus paymentPlus paymentSize
    (0 : Fin (n + 1)) H hlaw hdynamicOne hbinary hone hpositive
  exact ⟨hz, ho⟩

def localPrefixStateSevenCapital
    (x : LocalPrefixStateSeven) : FirmType → ℝ
  | .H => x.capitalH
  | .L => x.capitalL

def localPrefixStateSevenFace
    (x : LocalPrefixStateSeven) : FirmType → ℝ
  | .H => x.firmFaceH
  | .L => x.firmFaceL

def localPrefixStateSixCapital
    (x : LocalPrefixStateSix) : FirmType → ℝ
  | .H => x.capitalH
  | .L => x.capitalL

def localPrefixStateSixFace (P : Primitives S)
    (x : LocalPrefixStateSix) : FirmType → ℝ
  | .H => P.pledgeability FirmType.H * x.commonPledgeValue * x.capitalH
  | .L => P.pledgeability FirmType.L * x.commonPledgeValue * x.capitalL

def localPrefixFirmConsumption
    (u : LocalPrefixControlsTen) : FirmType → ℝ
  | .H => u.consumptionH
  | .L => u.consumptionL

/-- All predetermined and current objects needed by one of the two finite
dates after static labor and banking quantities have been eliminated. -/
structure LocalPrefixDateData where
  currentCapital : FirmType → ℝ
  inheritedFace : FirmType → ℝ
  currentBankFace : ℝ
  lagReserveRate : ℝ
  lagReservesPre : ℝ
  controls : LocalPrefixControlsTen
  nextCapital : FirmType → ℝ
  nextFace : FirmType → ℝ
  nextBankFace : ℝ
  currentReserveRate : ℝ
  currentReservesPre : ℝ
  nextControls : LocalPrefixControlsTen
  currentAggregateProductivity : ℝ
  nextAggregateProductivity : ℝ
  reserveRateInnovation : ℝ
  reserveQuantityInnovation : ℝ
  reserveRequirement : ℝ
  corridorWidth : ℝ

noncomputable def localPrefixDateZeroData
    (P : Primitives S) (I : InheritedState) (Z : LocalPrefixCoordinates)
    (dateOne : S) :
    LocalPrefixDateData where
  currentCapital := I.capital
  inheritedFace := I.firmFace
  currentBankFace := I.bankFace
  lagReserveRate := I.reserveRateLag
  lagReservesPre := I.reservesPreLag
  controls := Z.controlsZero
  nextCapital := localPrefixStateSevenCapital Z.stateOne
  nextFace := localPrefixStateSevenFace Z.stateOne
  nextBankFace := Z.stateOne.bankFace
  currentReserveRate := Z.stateOne.reserveRateLag
  currentReservesPre := Z.stateOne.reservesPreLag
  nextControls := Z.controlsOne
  currentAggregateProductivity := P.aggregateProductivity P.tree.initial
  nextAggregateProductivity := P.aggregateProductivity dateOne
  reserveRateInnovation := P.reserveRateInnovation P.tree.initial
  reserveQuantityInnovation := P.reserveQuantityInnovation P.tree.initial
  reserveRequirement := P.reserveRequirementPath 0 (bridgeDateZeroHistory P)
  corridorWidth := P.corridorWidthPath 0 (bridgeDateZeroHistory P)

noncomputable def localPrefixDateOneData
    (P : Primitives S) (Z : LocalPrefixCoordinates)
    (dateOne recurrent : S) (tail : LocalPrefixContinuationRule) :
    LocalPrefixDateData where
  currentCapital := localPrefixStateSevenCapital Z.stateOne
  inheritedFace := localPrefixStateSevenFace Z.stateOne
  currentBankFace := Z.stateOne.bankFace
  lagReserveRate := Z.stateOne.reserveRateLag
  lagReservesPre := Z.stateOne.reservesPreLag
  controls := Z.controlsOne
  nextCapital := localPrefixStateSixCapital Z.stateTwo
  nextFace := localPrefixStateSixFace P Z.stateTwo
  nextBankFace := Z.stateTwo.bankFace
  currentReserveRate := Z.stateTwo.reserveRateLag
  currentReservesPre := Z.stateTwo.reservesPreLag
  nextControls := tail Z.stateTwo
  currentAggregateProductivity := P.aggregateProductivity dateOne
  nextAggregateProductivity := P.aggregateProductivity recurrent
  reserveRateInnovation := P.reserveRateInnovation dateOne
  reserveQuantityInnovation := P.reserveQuantityInnovation dateOne
  reserveRequirement :=
    P.reserveRequirementPath 1 (bridgeDateOneHistory P dateOne)
  corridorWidth := P.corridorWidthPath 1 (bridgeDateOneHistory P dateOne)

noncomputable def localPrefixLabor
    (P : Primitives S) (d : LocalPrefixDateData) (i : FirmType) : ℝ :=
  (P.beta * d.controls.inputPrice * d.currentAggregateProductivity *
      P.productivity i * d.currentCapital i ^ P.alpha / d.controls.wage) ^
    (1 / (1 - P.beta))

noncomputable def localPrefixOutput
    (P : Primitives S) (d : LocalPrefixDateData) (i : FirmType) : ℝ :=
  operatingOutput (d.currentAggregateProductivity * P.productivity i)
    (d.currentCapital i) (localPrefixLabor P d i) P.alpha P.beta

noncomputable def localPrefixOperatingProfit
    (P : Primitives S) (d : LocalPrefixDateData) (i : FirmType) : ℝ :=
  d.controls.inputPrice * localPrefixOutput P d i -
    d.controls.wage * localPrefixLabor P d i

noncomputable def localPrefixNextMarginalProduct
    (P : Primitives S) (d : LocalPrefixDateData) (i : FirmType) : ℝ :=
  let nextLabor :=
    (P.beta * d.nextControls.inputPrice * d.nextAggregateProductivity *
        P.productivity i * d.nextCapital i ^ P.alpha /
        d.nextControls.wage) ^ (1 / (1 - P.beta))
  d.nextControls.inputPrice * d.nextAggregateProductivity * P.productivity i *
    P.alpha * d.nextCapital i ^ (P.alpha - 1) * nextLabor ^ P.beta

noncomputable def localPrefixAggregateCapital
    (P : Primitives S) (capital : FirmType → ℝ) : ℝ :=
  ∑ i, P.mass i * capital i

noncomputable def localPrefixAggregateOutput
    (P : Primitives S) (d : LocalPrefixDateData) : ℝ :=
  ∑ i, P.mass i * localPrefixOutput P d i

noncomputable def localPrefixAggregateLabor
    (P : Primitives S) (d : LocalPrefixDateData) : ℝ :=
  ∑ i, P.mass i * localPrefixLabor P d i

noncomputable def localPrefixInvestment
    (P : Primitives S) (d : LocalPrefixDateData) : ℝ :=
  localPrefixAggregateCapital P d.nextCapital -
    (1 - P.depreciation) * localPrefixAggregateCapital P d.currentCapital

noncomputable def localPrefixCapitalCost
    (P : Primitives S) (d : LocalPrefixDateData) : ℝ :=
  capitalCreationTechnology P (localPrefixInvestment P d)
    (localPrefixAggregateCapital P d.currentCapital)

noncomputable def localPrefixRotembergCost
    (P : Primitives S) (d : LocalPrefixDateData) : ℝ :=
  P.priceAdjustmentCost / 2 * (d.controls.inflation - 1) ^ 2 *
    localPrefixAggregateOutput P d

noncomputable def localPrefixFirmWealth
    (P : Primitives S) (d : LocalPrefixDateData) (i : FirmType) : ℝ :=
  localPrefixOperatingProfit P d i +
    (1 - P.depreciation) * d.controls.capitalPrice * d.currentCapital i -
    d.inheritedFace i / d.controls.inflation

noncomputable def localPrefixEntrepreneurSDF
    (P : Primitives S) (d : LocalPrefixDateData) (i : FirmType) : ℝ :=
  P.entrepreneurDiscount *
    crraMarginal P.entrepreneurRiskAversion
      (localPrefixFirmConsumption d.nextControls i) /
    crraMarginal P.entrepreneurRiskAversion
      (localPrefixFirmConsumption d.controls i)

noncomputable def localPrefixPledgeUnit
    (P : Primitives S) (d : LocalPrefixDateData) (i : FirmType) : ℝ :=
  P.pledgeability i * (1 - P.depreciation) *
    d.nextControls.inflation * d.nextControls.capitalPrice

noncomputable def localPrefixBankDeficitSlope
    (P : Primitives S) (d : LocalPrefixDateData) : ℝ :=
  otcDeficitSlope d.currentReserveRate
    (otcNegotiatedRate d.currentReserveRate
      (d.currentReserveRate + d.corridorWidth)
      P.matchingIntensity d.controls.tightness)
    (d.currentReserveRate + d.corridorWidth)
    P.matchingIntensity d.controls.tightness

noncomputable def localPrefixBankSurplusSlope
    (P : Primitives S) (d : LocalPrefixDateData) : ℝ :=
  otcSurplusSlope d.currentReserveRate
    (otcNegotiatedRate d.currentReserveRate
      (d.currentReserveRate + d.corridorWidth)
      P.matchingIntensity d.controls.tightness)
    P.matchingIntensity d.controls.tightness

noncomputable def localPrefixMeanAbsolutePaymentShock
    (P : Primitives S) : ℝ :=
  finiteSupportExpectation P.paymentSupport P.paymentProbability
    (fun ω ↦ |P.paymentShock ω|)

/-- The absolute payment-shock moment appearing in the reduced system equals
the positive atom size for the binary symmetric witness. -/
theorem localPrefixMeanAbsolutePaymentShock_eq_of_binarySymmetric
    (P : Primitives S) (paymentMinus paymentPlus : BankPayment)
    (paymentSize : ℝ)
    (H : BinarySymmetricPaymentLaw P paymentMinus paymentPlus paymentSize) :
    localPrefixMeanAbsolutePaymentShock P = paymentSize := by
  rcases H with ⟨hne, hsize, hsupport, hprobMinus, hprobPlus,
    hshockMinus, hshockPlus⟩
  rw [localPrefixMeanAbsolutePaymentShock,
    finiteSupportExpectation_eq_average_of_binarySymmetric P paymentMinus
      paymentPlus paymentSize
      ⟨hne, hsize, hsupport, hprobMinus, hprobPlus, hshockMinus, hshockPlus⟩]
  rw [hshockMinus, hshockPlus, abs_neg, abs_of_pos hsize]
  ring

noncomputable def localPrefixReserveDepositRatio
    (P : Primitives S) (d : LocalPrefixDateData) : ℝ :=
  d.reserveRequirement +
    (d.controls.depositRate / d.currentReserveRate - d.reserveRequirement) *
      localPrefixMeanAbsolutePaymentShock P *
        (1 - d.controls.tightness) / (1 + d.controls.tightness)

noncomputable def localReducedFirmBudgetResidual
    (P : Primitives S) (d : LocalPrefixDateData) (i : FirmType) : ℝ :=
  localPrefixFirmConsumption d.controls i +
      d.controls.capitalPrice * d.nextCapital i -
      d.nextFace i / d.controls.loanRate -
    localPrefixFirmWealth P d i

noncomputable def localReducedFirmCapitalEulerResidual
    (branch : LocalPrefixBranch) (P : Primitives S)
    (d : LocalPrefixDateData) (i : FirmType) : ℝ :=
  let sdf := localPrefixEntrepreneurSDF P d i
  let unconstrained := d.controls.capitalPrice -
    sdf * (localPrefixNextMarginalProduct P d i +
      (1 - P.depreciation) * d.nextControls.capitalPrice)
  match branch, i with
  | .slack, .L => unconstrained
  | _, _ =>
      let pledge := localPrefixPledgeUnit P d i
      d.controls.capitalPrice - pledge / d.controls.loanRate -
        sdf * (localPrefixNextMarginalProduct P d i +
          (1 - P.depreciation) * d.nextControls.capitalPrice -
          pledge / d.nextControls.inflation)

noncomputable def localReducedFirmRegimeResidual
    (branch : LocalPrefixBranch) (P : Primitives S)
    (d : LocalPrefixDateData) (i : FirmType) : ℝ :=
  match branch, i with
  | .slack, .L =>
      d.controls.loanRate * localPrefixEntrepreneurSDF P d i /
        d.nextControls.inflation - 1
  | _, _ => d.nextFace i - localPrefixPledgeUnit P d i * d.nextCapital i

noncomputable def localReducedRemainingResidual
    (P : Primitives S) (d : LocalPrefixDateData) (row : Fin 11) : ℝ :=
  let output := localPrefixAggregateOutput P d
  let nextOutput :=
    ∑ i, P.mass i * operatingOutput
      (d.nextAggregateProductivity * P.productivity i) (d.nextCapital i)
      ((P.beta * d.nextControls.inputPrice * d.nextAggregateProductivity *
          P.productivity i * d.nextCapital i ^ P.alpha /
          d.nextControls.wage) ^ (1 / (1 - P.beta))) P.alpha P.beta
  let householdSDF := P.workerDiscount *
    crraMarginal P.workerRiskAversion d.nextControls.workerConsumption /
      crraMarginal P.workerRiskAversion d.controls.workerConsumption
  let deficitSlope := localPrefixBankDeficitSlope P d
  let surplusSlope := localPrefixBankSurplusSlope P d
  let averageSlope := (deficitSlope + surplusSlope) / 2
  let slopeDifference := deficitSlope - surplusSlope
  let xi := d.controls.depositRate / d.currentReserveRate
  let paymentSize := localPrefixMeanAbsolutePaymentShock P
  let reserveDepositRatio := localPrefixReserveDepositRatio P d
  let bankLoans := ∑ i, P.mass i * d.nextFace i / d.controls.loanRate
  match row with
  | 0 => d.nextBankFace -
      bankRenewalFactor P * d.controls.loanRate * d.currentBankFace /
        d.controls.inflation
  | 1 => d.controls.capitalPrice - 1 -
      P.capitalAdjustmentCost * localPrefixInvestment P d /
        localPrefixAggregateCapital P d.currentCapital
  | 2 => d.controls.workerConsumption +
      (∑ i, P.mass i * localPrefixFirmConsumption d.controls i) +
      localPrefixCapitalCost P d + localPrefixRotembergCost P d - output
  | 3 => d.controls.wage - P.laborScale *
      d.controls.workerConsumption ^ P.workerRiskAversion *
        localPrefixAggregateLabor P d ^ P.laborCurvature
  | 4 => 1 - householdSDF * d.controls.depositRate /
      d.nextControls.inflation
  | 5 => 1 - P.priceElasticity +
      P.priceElasticity * d.controls.inputPrice -
      P.priceAdjustmentCost * d.controls.inflation *
        (d.controls.inflation - 1) +
      householdSDF * P.priceAdjustmentCost * nextOutput / output *
        d.nextControls.inflation * (d.nextControls.inflation - 1)
  | 6 => Real.log d.currentReserveRate -
      (P.reserveRatePersistence * Real.log d.lagReserveRate +
        (1 - P.reserveRatePersistence) *
          (Real.log P.reserveRateSteady +
            P.inflationResponse * Real.log d.controls.inflation +
            P.outputResponse * Real.log (output / P.outputReference)) +
        d.reserveRateInnovation)
  | 7 => Real.log d.currentReservesPre -
      (P.reserveQuantityPersistence * Real.log d.lagReservesPre +
        (1 - P.reserveQuantityPersistence) *
          Real.log P.reserveQuantitySteady + d.reserveQuantityInnovation)
  | 8 => d.controls.loanRate - d.currentReserveRate - averageSlope
  | 9 => d.currentReserveRate +
      (1 - d.reserveRequirement) * averageSlope -
      (xi - d.reserveRequirement) * paymentSize * slopeDifference / 2 -
      d.controls.depositRate
  | 10 => bankLoans -
      (d.currentBankFace / d.controls.inflation +
        (1 / reserveDepositRatio - 1) * d.currentReservesPre)

/-- Bank loans reconstructed from the originated nominal firm faces in the
finite reduction. -/
noncomputable def localPrefixReducedBankLoans
    (P : Primitives S) (d : LocalPrefixDateData) : ℝ :=
  ∑ i, P.mass i * d.nextFace i / d.controls.loanRate

/-- Deposits reconstructed from reserves and the reduced reserve/deposit
ratio.  A literal identification therefore also needs that ratio nonzero. -/
noncomputable def localPrefixReducedBankDeposits
    (P : Primitives S) (d : LocalPrefixDateData) : ℝ :=
  d.currentReservesPre / localPrefixReserveDepositRatio P d

/-- Real bank equity represented by the reduced nominal face coordinate. -/
noncomputable def localPrefixReducedBankEquity
    (d : LocalPrefixDateData) : ℝ :=
  d.currentBankFace / d.controls.inflation

/-- Row ten of the reduced system is exactly the level bank balance after the
three eliminated bank quantities are reconstructed.  This proves an equality;
it does not infer individual-bank feasibility or optimality. -/
theorem localReducedRemainingResidual_bankBalance_eq
    (P : Primitives S) (d : LocalPrefixDateData)
    (hratio : localPrefixReserveDepositRatio P d ≠ 0)
    (hrow : localReducedRemainingResidual P d 10 = 0) :
    localPrefixReducedBankLoans P d + d.currentReservesPre =
      localPrefixReducedBankDeposits P d + localPrefixReducedBankEquity d := by
  simp only [localReducedRemainingResidual] at hrow
  unfold localPrefixReducedBankLoans localPrefixReducedBankDeposits
    localPrefixReducedBankEquity
  field_simp [hratio] at hrow ⊢
  linear_combination hrow

/-- Row zero is the exact nominal bank-face transition used in the reduction. -/
theorem localReducedRemainingResidual_bankFace_eq
    (P : Primitives S) (d : LocalPrefixDateData)
    (hrow : localReducedRemainingResidual P d 0 = 0) :
    d.nextBankFace =
      bankRenewalFactor P * d.controls.loanRate * d.currentBankFace /
        d.controls.inflation := by
  simp only [localReducedRemainingResidual] at hrow
  linarith

/-- Dividing the exact nominal-face row by the recorded child inflation gives
the corresponding real-equity transition, without imposing a linear tail. -/
theorem localReducedRemainingResidual_bankEquityTransition_eq
    (P : Primitives S) (d : LocalPrefixDateData)
    (hrow : localReducedRemainingResidual P d 0 = 0) :
    d.nextBankFace / d.nextControls.inflation =
      bankRenewalFactor P * d.controls.loanRate *
        (d.currentBankFace / d.controls.inflation) /
          d.nextControls.inflation := by
  rw [localReducedRemainingResidual_bankFace_eq P d hrow]
  ring

/-- The concrete 33-equation function `F_r(Z,v)`.  Intervention dependence is
already inside `P = initialIntervenedPrimitives P₀ v`; the tail rule supplies
only date-two controls and must separately be proved to be the exact infinite
continuation. -/
noncomputable def localReducedPrefixResidual
    (branch : LocalPrefixBranch) (P : Primitives S) (I : InheritedState)
    (Z : LocalPrefixCoordinates) (dateOne recurrent : S)
    (tail : LocalPrefixContinuationRule) : LocalPrefixEquation → ℝ :=
  let d0 := localPrefixDateZeroData P I Z dateOne
  let d1 := localPrefixDateOneData P Z dateOne recurrent tail
  fun equation ↦ match equation with
  | .firmBudgetZeroH => localReducedFirmBudgetResidual P d0 FirmType.H
  | .firmBudgetZeroL => localReducedFirmBudgetResidual P d0 FirmType.L
  | .firmCapitalEulerZeroH =>
      localReducedFirmCapitalEulerResidual branch P d0 FirmType.H
  | .firmCapitalEulerZeroL =>
      localReducedFirmCapitalEulerResidual branch P d0 FirmType.L
  | .firmRegimeZeroH => localReducedFirmRegimeResidual branch P d0 FirmType.H
  | .firmRegimeZeroL => localReducedFirmRegimeResidual branch P d0 FirmType.L
  | .bankEquityZero => localReducedRemainingResidual P d0 0
  | .capitalSupplyZero => localReducedRemainingResidual P d0 1
  | .resourcesZero => localReducedRemainingResidual P d0 2
  | .workerLaborZero => localReducedRemainingResidual P d0 3
  | .householdEulerZero => localReducedRemainingResidual P d0 4
  | .nkpcZero => localReducedRemainingResidual P d0 5
  | .reserveRateRuleZero => localReducedRemainingResidual P d0 6
  | .reserveQuantityRuleZero => localReducedRemainingResidual P d0 7
  | .loanPricingZero => localReducedRemainingResidual P d0 8
  | .depositPricingZero => localReducedRemainingResidual P d0 9
  | .bankBalanceZero => localReducedRemainingResidual P d0 10
  | .firmBudgetOneH => localReducedFirmBudgetResidual P d1 FirmType.H
  | .firmBudgetOneL => localReducedFirmBudgetResidual P d1 FirmType.L
  | .firmCapitalEulerOneH =>
      localReducedFirmCapitalEulerResidual LocalPrefixBranch.binding P d1 FirmType.H
  | .firmCapitalEulerOneL =>
      localReducedFirmCapitalEulerResidual LocalPrefixBranch.binding P d1 FirmType.L
  | .commonPledgeOne => Z.stateTwo.commonPledgeValue -
      (1 - P.depreciation) * d1.nextControls.inflation *
        d1.nextControls.capitalPrice
  | .bankEquityOne => localReducedRemainingResidual P d1 0
  | .capitalSupplyOne => localReducedRemainingResidual P d1 1
  | .resourcesOne => localReducedRemainingResidual P d1 2
  | .workerLaborOne => localReducedRemainingResidual P d1 3
  | .householdEulerOne => localReducedRemainingResidual P d1 4
  | .nkpcOne => localReducedRemainingResidual P d1 5
  | .reserveRateRuleOne => localReducedRemainingResidual P d1 6
  | .reserveQuantityRuleOne => localReducedRemainingResidual P d1 7
  | .loanPricingOne => localReducedRemainingResidual P d1 8
  | .depositPricingOne => localReducedRemainingResidual P d1 9
  | .bankBalanceOne => localReducedRemainingResidual P d1 10

def LocalReducedPrefixEquationsHold
    (branch : LocalPrefixBranch) (P : Primitives S) (I : InheritedState)
    (Z : LocalPrefixCoordinates) (dateOne recurrent : S)
    (tail : LocalPrefixContinuationRule) : Prop :=
  ∀ equation,
    localReducedPrefixResidual branch P I Z dateOne recurrent tail equation = 0

/-- On an actually realized prefix, the exact date-zero reduced face row is
the literal inherited-face to date-one equity transition.  The theorem is
conditional on the displayed exact reduced equations; it imports no external
existence certificate. -/
theorem localReducedPrefix_bankFaceTransition_zero_of_realized
    (P : Primitives S) (I : InheritedState) (X : Allocation S)
    (dateOne recurrent : S) (Z : LocalPrefixCoordinates)
    (tail : LocalPrefixContinuationRule)
    (hrealized : LocalPrefixCoordinatesRealized P X dateOne recurrent Z)
    (hequations : LocalReducedPrefixEquationsHold LocalPrefixBranch.slack P I Z
      dateOne recurrent tail) :
    X.inflation 1 (bridgeDateOneHistory P dateOne) *
        X.bankEquity 1 (bridgeDateOneHistory P dateOne) =
      bankRenewalFactor P *
        X.loanRate 0 (bridgeDateZeroHistory P) * I.bankFace /
          X.inflation 0 (bridgeDateZeroHistory P) := by
  rcases hrealized with
    ⟨_hcapitalH0, _hcapitalL0, _hfirmFaceH0, _hfirmFaceL0, hbankFace1,
      _hreserveLag0, _hreservesLag0, _hcH0, _hcL0, _hcW0, _hwage0,
      _hinput0, hinflation0, _hcapitalPrice0, _hdepositRate0, hloanRate0,
      _htightness0, _hcapitalH1, _hcapitalL1, _hpledge2, _hfirmFaceH1,
      _hfirmFaceL1, _hbankFace2, _hreserveLag1, _hreservesLag1, _hcH1,
      _hcL1, _hcW1, _hwage1, _hinput1, _hinflation1, _hcapitalPrice1,
      _hdepositRate1, _hloanRate1, _htightness1⟩
  have hrow := hequations LocalPrefixEquation.bankEquityZero
  change localReducedRemainingResidual P
    (localPrefixDateZeroData P I Z dateOne) 0 = 0 at hrow
  have hface := localReducedRemainingResidual_bankFace_eq P
    (localPrefixDateZeroData P I Z dateOne) hrow
  dsimp [localPrefixDateZeroData] at hface
  calc
    X.inflation 1 (bridgeDateOneHistory P dateOne) *
          X.bankEquity 1 (bridgeDateOneHistory P dateOne) =
        Z.stateOne.bankFace := hbankFace1.symm
    _ = bankRenewalFactor P * Z.controlsZero.loanRate * I.bankFace /
          Z.controlsZero.inflation := hface
    _ = _ := by rw [hloanRate0, hinflation0]

/-- The exact date-one reduced face row is likewise the literal date-one to
date-two transition on the supported prefix. -/
theorem localReducedPrefix_bankFaceTransition_one_of_realized
    (P : Primitives S) (I : InheritedState) (X : Allocation S)
    (dateOne recurrent : S) (Z : LocalPrefixCoordinates)
    (tail : LocalPrefixContinuationRule)
    (hrealized : LocalPrefixCoordinatesRealized P X dateOne recurrent Z)
    (hequations : LocalReducedPrefixEquationsHold LocalPrefixBranch.slack P I Z
      dateOne recurrent tail) :
    X.inflation 2 (bridgeDateTwoHistory P dateOne recurrent) *
        X.bankEquity 2 (bridgeDateTwoHistory P dateOne recurrent) =
      bankRenewalFactor P *
        X.loanRate 1 (bridgeDateOneHistory P dateOne) *
        (X.inflation 1 (bridgeDateOneHistory P dateOne) *
          X.bankEquity 1 (bridgeDateOneHistory P dateOne)) /
        X.inflation 1 (bridgeDateOneHistory P dateOne) := by
  rcases hrealized with
    ⟨_hcapitalH0, _hcapitalL0, _hfirmFaceH0, _hfirmFaceL0, hbankFace1,
      _hreserveLag0, _hreservesLag0, _hcH0, _hcL0, _hcW0, _hwage0,
      _hinput0, _hinflation0, _hcapitalPrice0, _hdepositRate0, _hloanRate0,
      _htightness0, _hcapitalH1, _hcapitalL1, _hpledge2, _hfirmFaceH1,
      _hfirmFaceL1, hbankFace2, _hreserveLag1, _hreservesLag1, _hcH1,
      _hcL1, _hcW1, _hwage1, _hinput1, hinflation1, _hcapitalPrice1,
      _hdepositRate1, hloanRate1, _htightness1⟩
  have hrow := hequations LocalPrefixEquation.bankEquityOne
  change localReducedRemainingResidual P
    (localPrefixDateOneData P Z dateOne recurrent tail) 0 = 0 at hrow
  have hface := localReducedRemainingResidual_bankFace_eq P
    (localPrefixDateOneData P Z dateOne recurrent tail) hrow
  dsimp [localPrefixDateOneData] at hface
  calc
    X.inflation 2 (bridgeDateTwoHistory P dateOne recurrent) *
          X.bankEquity 2 (bridgeDateTwoHistory P dateOne recurrent) =
        Z.stateTwo.bankFace := hbankFace2.symm
    _ = bankRenewalFactor P * Z.controlsOne.loanRate *
          Z.stateOne.bankFace / Z.controlsOne.inflation := hface
    _ = _ := by rw [hloanRate1, hbankFace1, hinflation1]

/-- The date-zero nominal face row becomes the actual literal real-equity
transition once initial equity is reconstructed from the inherited face and
child inflation is nonzero. -/
theorem localReducedPrefix_bankEquityTransition_zero_of_realized
    (P : Primitives S) (I : InheritedState) (X : Allocation S)
    (dateOne recurrent : S) (Z : LocalPrefixCoordinates)
    (tail : LocalPrefixContinuationRule)
    (hrealized : LocalPrefixCoordinatesRealized P X dateOne recurrent Z)
    (hequations : LocalReducedPrefixEquationsHold LocalPrefixBranch.slack P I Z
      dateOne recurrent tail)
    (hcurrent : X.bankEquity 0 (bridgeDateZeroHistory P) =
      I.bankFace / X.inflation 0 (bridgeDateZeroHistory P))
    (hchildInflation :
      X.inflation 1 (bridgeDateOneHistory P dateOne) ≠ 0) :
    localBankEquityTransitionResidual P X 0
      (bridgeDateZeroHistory P) dateOne = 0 := by
  have hface := localReducedPrefix_bankFaceTransition_zero_of_realized
    P I X dateOne recurrent Z tail hrealized hequations
  change X.bankEquity 1 (bridgeDateOneHistory P dateOne) -
    bankRenewalFactor P * X.loanRate 0 (bridgeDateZeroHistory P) *
      X.bankEquity 0 (bridgeDateZeroHistory P) /
        X.inflation 1 (bridgeDateOneHistory P dateOne) = 0
  rw [sub_eq_zero, hcurrent]
  apply (eq_div_iff hchildInflation).2
  calc
    X.bankEquity 1 (bridgeDateOneHistory P dateOne) *
          X.inflation 1 (bridgeDateOneHistory P dateOne) =
        X.inflation 1 (bridgeDateOneHistory P dateOne) *
          X.bankEquity 1 (bridgeDateOneHistory P dateOne) := mul_comm _ _
    _ = bankRenewalFactor P * X.loanRate 0 (bridgeDateZeroHistory P) *
          I.bankFace / X.inflation 0 (bridgeDateZeroHistory P) := hface
    _ = bankRenewalFactor P * X.loanRate 0 (bridgeDateZeroHistory P) *
          (I.bankFace / X.inflation 0 (bridgeDateZeroHistory P)) := by ring

/-- At date one, nonzero current and child inflation cancel the two nominal
faces and close the literal real-equity residual exactly. -/
theorem localReducedPrefix_bankEquityTransition_one_of_realized
    (P : Primitives S) (I : InheritedState) (X : Allocation S)
    (dateOne recurrent : S) (Z : LocalPrefixCoordinates)
    (tail : LocalPrefixContinuationRule)
    (hrealized : LocalPrefixCoordinatesRealized P X dateOne recurrent Z)
    (hequations : LocalReducedPrefixEquationsHold LocalPrefixBranch.slack P I Z
      dateOne recurrent tail)
    (hcurrentInflation :
      X.inflation 1 (bridgeDateOneHistory P dateOne) ≠ 0)
    (hchildInflation :
      X.inflation 2 (bridgeDateTwoHistory P dateOne recurrent) ≠ 0) :
    localBankEquityTransitionResidual P X 1
      (bridgeDateOneHistory P dateOne) recurrent = 0 := by
  have hface := localReducedPrefix_bankFaceTransition_one_of_realized
    P I X dateOne recurrent Z tail hrealized hequations
  change X.bankEquity 2 (bridgeDateTwoHistory P dateOne recurrent) -
    bankRenewalFactor P * X.loanRate 1 (bridgeDateOneHistory P dateOne) *
      X.bankEquity 1 (bridgeDateOneHistory P dateOne) /
        X.inflation 2 (bridgeDateTwoHistory P dateOne recurrent) = 0
  rw [sub_eq_zero]
  apply (eq_div_iff hchildInflation).2
  calc
    X.bankEquity 2 (bridgeDateTwoHistory P dateOne recurrent) *
          X.inflation 2 (bridgeDateTwoHistory P dateOne recurrent) =
        X.inflation 2 (bridgeDateTwoHistory P dateOne recurrent) *
          X.bankEquity 2 (bridgeDateTwoHistory P dateOne recurrent) := mul_comm _ _
    _ = bankRenewalFactor P * X.loanRate 1 (bridgeDateOneHistory P dateOne) *
          (X.inflation 1 (bridgeDateOneHistory P dateOne) *
            X.bankEquity 1 (bridgeDateOneHistory P dateOne)) /
          X.inflation 1 (bridgeDateOneHistory P dateOne) := hface
    _ = bankRenewalFactor P * X.loanRate 1 (bridgeDateOneHistory P dateOne) *
          X.bankEquity 1 (bridgeDateOneHistory P dateOne) := by
      field_simp [hcurrentInflation]

/-- With explicit reduced-to-literal quantity identifications, the exact
date-zero reduced balance row becomes the literal aggregate balance residual.
The premises are coordinate identities, not a `BankFeasible` record. -/
theorem localReducedPrefix_bankBalance_zero_of_identified
    (P : Primitives S) (I : InheritedState) (X : Allocation S)
    (dateOne recurrent : S) (Z : LocalPrefixCoordinates)
    (tail : LocalPrefixContinuationRule)
    (hequations : LocalReducedPrefixEquationsHold LocalPrefixBranch.slack P I Z
      dateOne recurrent tail)
    (hratio : localPrefixReserveDepositRatio P
      (localPrefixDateZeroData P I Z dateOne) ≠ 0)
    (hloans : X.bankLoans 0 (bridgeDateZeroHistory P) =
      localPrefixReducedBankLoans P (localPrefixDateZeroData P I Z dateOne))
    (hreserves : X.reservesPrePayment 0 (bridgeDateZeroHistory P) =
      (localPrefixDateZeroData P I Z dateOne).currentReservesPre)
    (hdeposits : X.bankDeposits 0 (bridgeDateZeroHistory P) =
      localPrefixReducedBankDeposits P (localPrefixDateZeroData P I Z dateOne))
    (hretained : X.bankRetainedEquity 0 (bridgeDateZeroHistory P) =
      localPrefixReducedBankEquity (localPrefixDateZeroData P I Z dateOne)) :
    localBankBalanceResidual X 0 (bridgeDateZeroHistory P) = 0 := by
  have hrow := hequations LocalPrefixEquation.bankBalanceZero
  change localReducedRemainingResidual P
    (localPrefixDateZeroData P I Z dateOne) 10 = 0 at hrow
  have hbalance := localReducedRemainingResidual_bankBalance_eq P
    (localPrefixDateZeroData P I Z dateOne) hratio hrow
  unfold localBankBalanceResidual
  rw [hloans, hreserves, hdeposits, hretained]
  linarith

/-- Date one has the same exact identified balance implication. -/
theorem localReducedPrefix_bankBalance_one_of_identified
    (P : Primitives S) (I : InheritedState) (X : Allocation S)
    (dateOne recurrent : S) (Z : LocalPrefixCoordinates)
    (tail : LocalPrefixContinuationRule)
    (hequations : LocalReducedPrefixEquationsHold LocalPrefixBranch.slack P I Z
      dateOne recurrent tail)
    (hratio : localPrefixReserveDepositRatio P
      (localPrefixDateOneData P Z dateOne recurrent tail) ≠ 0)
    (hloans : X.bankLoans 1 (bridgeDateOneHistory P dateOne) =
      localPrefixReducedBankLoans P
        (localPrefixDateOneData P Z dateOne recurrent tail))
    (hreserves : X.reservesPrePayment 1 (bridgeDateOneHistory P dateOne) =
      (localPrefixDateOneData P Z dateOne recurrent tail).currentReservesPre)
    (hdeposits : X.bankDeposits 1 (bridgeDateOneHistory P dateOne) =
      localPrefixReducedBankDeposits P
        (localPrefixDateOneData P Z dateOne recurrent tail))
    (hretained : X.bankRetainedEquity 1 (bridgeDateOneHistory P dateOne) =
      localPrefixReducedBankEquity
        (localPrefixDateOneData P Z dateOne recurrent tail)) :
    localBankBalanceResidual X 1 (bridgeDateOneHistory P dateOne) = 0 := by
  have hrow := hequations LocalPrefixEquation.bankBalanceOne
  change localReducedRemainingResidual P
    (localPrefixDateOneData P Z dateOne recurrent tail) 10 = 0 at hrow
  have hbalance := localReducedRemainingResidual_bankBalance_eq P
    (localPrefixDateOneData P Z dateOne recurrent tail) hratio hrow
  unfold localBankBalanceResidual
  rw [hloans, hreserves, hdeposits, hretained]
  linarith

/-- The reduced root plus its 33-coordinate realization does not determine a
full `Allocation`: taxes are absent from both surfaces.  This theorem gives a
concrete counter-witness and pinpoints the need for an additional literal
fiscal/accounting reconstruction.  It does not assert that the modified
allocation satisfies fiscal closure or equilibrium. -/
theorem localReducedPrefix_surface_does_not_identify_tax
    (branch : LocalPrefixBranch) (P : Primitives S) (I : InheritedState)
    (X : Allocation S) (dateOne recurrent : S) (Z : LocalPrefixCoordinates)
    (tail : LocalPrefixContinuationRule)
    (hrealized : LocalPrefixCoordinatesRealized P X dateOne recurrent Z)
    (hequations : LocalReducedPrefixEquationsHold branch P I Z
      dateOne recurrent tail) :
    ∃ X' : Allocation S,
      LocalPrefixCoordinatesRealized P X' dateOne recurrent Z ∧
      LocalReducedPrefixEquationsHold branch P I Z dateOne recurrent tail ∧
      X' ≠ X := by
  let tax' : AdaptedProcess S := fun t h ↦ X.tax t h + 1
  let X' : Allocation S := { X with tax := tax' }
  refine ⟨X', ?_, hequations, ?_⟩
  · exact (localPrefixCoordinatesRealized_withTax_iff P X tax'
      dateOne recurrent Z).2 hrealized
  · intro heq
    have htax := congrArg
      (fun Y : Allocation S ↦ Y.tax 0 (bridgeDateZeroHistory P)) heq
    dsimp [X', tax'] at htax
    linarith

noncomputable def localRecurrentDateData
    (P : Primitives LocalBridgePhase)
    (state : ℕ → LocalPrefixStateSix)
    (controls : ℕ → LocalPrefixControlsTen)
    (n : ℕ) : LocalPrefixDateData where
  currentCapital := localPrefixStateSixCapital (state n)
  inheritedFace := localPrefixStateSixFace P (state n)
  currentBankFace := (state n).bankFace
  lagReserveRate := (state n).reserveRateLag
  lagReservesPre := (state n).reservesPreLag
  controls := controls n
  nextCapital := localPrefixStateSixCapital (state (n + 1))
  nextFace := localPrefixStateSixFace P (state (n + 1))
  nextBankFace := (state (n + 1)).bankFace
  currentReserveRate := (state (n + 1)).reserveRateLag
  currentReservesPre := (state (n + 1)).reservesPreLag
  nextControls := controls (n + 1)
  currentAggregateProductivity := P.aggregateProductivity .recurrent
  nextAggregateProductivity := P.aggregateProductivity .recurrent
  reserveRateInnovation := P.reserveRateInnovation .recurrent
  reserveQuantityInnovation := P.reserveQuantityInnovation .recurrent
  reserveRequirement := P.reserveRequirementPath (n + 2) (localBridgeHistory (n + 2))
  corridorWidth := P.corridorWidthPath (n + 2) (localBridgeHistory (n + 2))

noncomputable def localSlackExactDateData
    (P : Primitives LocalBridgePhase) (I : InheritedState)
    (Z : LocalPrefixCoordinates) (tail : LocalPrefixContinuationRule)
    (state : ℕ → LocalPrefixStateSix)
    (controls : ℕ → LocalPrefixControlsTen) : ℕ → LocalPrefixDateData
  | 0 => localPrefixDateZeroData P I Z .dateOne
  | 1 => localPrefixDateOneData P Z .dateOne .recurrent tail
  | n + 2 => localRecurrentDateData P state controls n

noncomputable def localDateBankEquity (d : LocalPrefixDateData) : ℝ :=
  d.currentBankFace / d.controls.inflation

noncomputable def localDateBankOwnerIncome
    (P : Primitives LocalBridgePhase) (d : LocalPrefixDateData) : ℝ :=
  P.bankExit * (1 - P.bankSeedShare) *
    (d.currentBankFace / (bankRenewalFactor P * d.controls.inflation))

/-- The private and pre-settlement bank fields obtained literally from one
reduced date. Aggregate settlement is installed in the next constructor. -/
noncomputable def localSlackPrivateBankCore
    (P : Primitives LocalBridgePhase)
    (d : ℕ → LocalPrefixDateData) : Allocation LocalBridgePhase where
  firmConsumption := fun i t _h ↦ localPrefixFirmConsumption (d t).controls i
  workerConsumption := fun t _h ↦ (d t).controls.workerConsumption
  workerLabor := fun t _h ↦ localPrefixAggregateLabor P (d t)
  capital := fun i t _h ↦ (d t).nextCapital i
  aggregateCapital := fun t _h ↦ localPrefixAggregateCapital P (d t).currentCapital
  labor := fun i t _h ↦ localPrefixLabor P (d t) i
  loan := fun i t _h ↦ (d t).nextFace i / (d t).controls.loanRate
  firmDeposit := fun _i _t _h ↦ 0
  firmFace := fun i t _h ↦ (d t).nextFace i
  firmWealth := fun i t _h ↦ localPrefixFirmWealth P (d t) i
  collateralDual := fun i t _h ↦
    match t, i with
    | 0, .L => 0
    | _, _ => 1 / (d t).controls.loanRate -
        localPrefixEntrepreneurSDF P (d t) i / (d t).nextControls.inflation
  inputPrice := fun t _h ↦ (d t).controls.inputPrice
  wage := fun t _h ↦ (d t).controls.wage
  inflation := fun t _h ↦ (d t).controls.inflation
  capitalPrice := fun t _h ↦ (d t).controls.capitalPrice
  loanRate := fun t _h ↦ (d t).controls.loanRate
  depositRate := fun t _h ↦ (d t).controls.depositRate
  reserveRate := fun t _h ↦ (d t).currentReserveRate
  interbankRate := fun t _h ↦
    otcNegotiatedRate (d t).currentReserveRate
      ((d t).currentReserveRate + (d t).corridorWidth)
      P.matchingIntensity (d t).controls.tightness
  facilityRate := fun t _h ↦ (d t).currentReserveRate + (d t).corridorWidth
  bankTightness := fun t _h ↦ (d t).controls.tightness
  reservesPrePayment := fun t _h ↦ (d t).currentReservesPre
  reservesPostPayment := fun _t _h ↦ 0
  bankLoans := fun t _h ↦ localPrefixReducedBankLoans P (d t)
  bankDeposits := fun t _h ↦ localPrefixReducedBankDeposits P (d t)
  bankEquity := fun t _h ↦ localDateBankEquity (d t)
  bankRetainedEquity := fun t _h ↦ localDateBankEquity (d t)
  bankDividend := fun _t _h ↦ 0
  bankNetIncome := fun t _h ↦ localDateBankOwnerIncome P (d t)
  retailerNetIncome := fun _t _h ↦ 0
  capitalProducerNetIncome := fun _t _h ↦ 0
  interbankPosition := fun _t _h ↦ 0
  facilityBorrowing := fun _t _h ↦ 0
  householdDeposits := fun t _h ↦ localPrefixReducedBankDeposits P (d t)
  householdBonds := fun t _h ↦ P.governmentBondSupply - (d t).currentReservesPre
  centralBankBonds := fun t _h ↦ (d t).currentReservesPre
  governmentBondRate := fun t _h ↦ (d t).controls.depositRate
  tax := fun _t _h ↦ 0
  output := fun t _h ↦ localPrefixAggregateOutput P (d t)
  investment := fun t _h ↦ localPrefixInvestment P (d t)
  capitalCreationCost := fun t _h ↦ localPrefixCapitalCost P (d t)
  priceAdjustmentResourceCost := fun t _h ↦ localPrefixRotembergCost P (d t)
  retailerLogRelativePrice := fun _t _h ↦ 0

noncomputable def localSlackExpectedPostReserves
    (P : Primitives LocalBridgePhase)
    (d : ℕ → LocalPrefixDateData) (t : ℕ)
    (h : History LocalBridgePhase t) : ℝ :=
  let X := localSlackPrivateBankCore P d
  let p := fullRetentionCommonBankPlan P X
  finiteSupportExpectation P.paymentSupport P.paymentProbability
    (fun ω ↦ p.reservesPost ω t h)

noncomputable def localSlackExpectedInterbank
    (P : Primitives LocalBridgePhase)
    (d : ℕ → LocalPrefixDateData) (t : ℕ)
    (h : History LocalBridgePhase t) : ℝ :=
  let X := localSlackPrivateBankCore P d
  let p := fullRetentionCommonBankPlan P X
  finiteSupportExpectation P.paymentSupport P.paymentProbability
    (fun ω ↦ p.interbank ω t h)

noncomputable def localSlackExpectedFacility
    (P : Primitives LocalBridgePhase)
    (d : ℕ → LocalPrefixDateData) (t : ℕ)
    (h : History LocalBridgePhase t) : ℝ :=
  let X := localSlackPrivateBankCore P d
  let p := fullRetentionCommonBankPlan P X
  finiteSupportExpectation P.paymentSupport P.paymentProbability
    (fun ω ↦ p.facility ω t h)

/-- Replace the three aggregate settlement placeholders by the exact finite-law
expectations generated from the common plan's matching and facility rules. -/
noncomputable def localSlackSettlementAllocation
    (P : Primitives LocalBridgePhase)
    (d : ℕ → LocalPrefixDateData) : Allocation LocalBridgePhase :=
  let X := localSlackPrivateBankCore P d
  { X with
    reservesPostPayment := localSlackExpectedPostReserves P d
    interbankPosition := localSlackExpectedInterbank P d
    facilityBorrowing := localSlackExpectedFacility P d }

/-- Full source real/fiscal completion of the literal private/bank map. -/
noncomputable def localSlackLiteralAllocation
    (P : Primitives LocalBridgePhase) (I : InheritedState)
    (d : ℕ → LocalPrefixDateData) : Allocation LocalBridgePhase :=
  withSourceAccountingCompletion P I (localSlackSettlementAllocation P d)

theorem localSlackExpectedPostReserves_eq
    (P : Primitives LocalBridgePhase)
    (d : ℕ → LocalPrefixDateData) (t : ℕ)
    (h : History LocalBridgePhase t) :
    localSlackExpectedPostReserves P d t h =
      (d t).currentReservesPre + localSlackExpectedInterbank P d t h +
        localSlackExpectedFacility P d t h := by
  let X := localSlackPrivateBankCore P d
  let transfer : BankPayment → ℝ := fun ω ↦
    (X.depositRate t h / X.reserveRate t h) * P.paymentShock ω *
      X.bankDeposits t h
  have htransfer : finiteSupportExpectation P.paymentSupport P.paymentProbability
      transfer = 0 := by
    unfold transfer finiteSupportExpectation
    calc
      (∑ ω ∈ P.paymentSupport, P.paymentProbability ω *
          ((X.depositRate t h / X.reserveRate t h) * P.paymentShock ω *
            X.bankDeposits t h)) =
          ((X.depositRate t h / X.reserveRate t h) * X.bankDeposits t h) *
            (∑ ω ∈ P.paymentSupport,
              P.paymentProbability ω * P.paymentShock ω) := by
                rw [Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro ω _hω
                ring
      _ = 0 := by rw [P.payment_shock_mean_zero]; ring
  unfold localSlackExpectedPostReserves localSlackExpectedInterbank
    localSlackExpectedFacility
  change finiteSupportExpectation P.paymentSupport P.paymentProbability
      (fun ω ↦ X.reservesPrePayment t h + transfer ω +
        (fullRetentionCommonBankPlan P X).interbank ω t h +
        (fullRetentionCommonBankPlan P X).facility ω t h) = _
  rw [finiteSupportExpectation_add, finiteSupportExpectation_add,
    finiteSupportExpectation_add,
    finiteSupportExpectation_const _ _ P.payment_probability_sum_one,
    htransfer]
  dsimp only [X, localSlackPrivateBankCore]
  ring

theorem localSlackExpectedFacility_nonneg
    (P : Primitives LocalBridgePhase)
    (d : ℕ → LocalPrefixDateData) (t : ℕ)
    (h : History LocalBridgePhase t)
    (htightness : 0 < (d t).controls.tightness) :
    0 ≤ localSlackExpectedFacility P d t h := by
  unfold localSlackExpectedFacility finiteSupportExpectation
  apply Finset.sum_nonneg
  intro ω hω
  apply mul_nonneg (P.payment_probability_nonneg ω)
  exact bankFacilityBorrowingAt_nonneg P (localSlackPrivateBankCore P d)
    t h (d t).controls.tightness (d t).currentReservesPre
      (localPrefixReducedBankDeposits P (d t)) htightness ω

theorem localSlackLiteralAllocation_settlementClears
    (P : Primitives LocalBridgePhase) (I : InheritedState)
    (d : ℕ → LocalPrefixDateData)
    (htightness : ∀ t, 0 < (d t).controls.tightness)
    (hinterbank : ∀ t (h : History LocalBridgePhase t),
      FirmHistoryAdmissible P t h → localSlackExpectedInterbank P d t h = 0) :
    SettlementClears P (localSlackLiteralAllocation P I d) := by
  intro t h hs
  have hpost := localSlackExpectedPostReserves_eq P d t h
  have hfacility := localSlackExpectedFacility_nonneg P d t h (htightness t)
  simp only [localSlackLiteralAllocation, withSourceAccountingCompletion,
    withSourceFiscalAccounts, withSourceRealAccounts,
    localSlackSettlementAllocation]
  exact ⟨hinterbank t h hs, hfacility, hpost⟩

theorem localSlackLiteralAllocation_bank_fields
    (P : Primitives LocalBridgePhase) (I : InheritedState)
    (d : ℕ → LocalPrefixDateData) (t : ℕ)
    (h : History LocalBridgePhase t) :
    (localSlackLiteralAllocation P I d).bankLoans t h =
        localPrefixReducedBankLoans P (d t) ∧
    (localSlackLiteralAllocation P I d).reservesPrePayment t h =
        (d t).currentReservesPre ∧
    (localSlackLiteralAllocation P I d).bankDeposits t h =
        localPrefixReducedBankDeposits P (d t) ∧
    (localSlackLiteralAllocation P I d).bankEquity t h =
        (d t).currentBankFace / (d t).controls.inflation ∧
    (localSlackLiteralAllocation P I d).bankRetainedEquity t h =
        (d t).currentBankFace / (d t).controls.inflation ∧
    (localSlackLiteralAllocation P I d).bankDividend t h = 0 := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem localSlackLiteralAllocation_private_fields
    (P : Primitives LocalBridgePhase) (I : InheritedState)
    (d : ℕ → LocalPrefixDateData) (t : ℕ)
    (h : History LocalBridgePhase t) (i : FirmType) :
    (localSlackLiteralAllocation P I d).firmConsumption i t h =
        localPrefixFirmConsumption (d t).controls i ∧
    (localSlackLiteralAllocation P I d).capital i t h = (d t).nextCapital i ∧
    (localSlackLiteralAllocation P I d).firmFace i t h = (d t).nextFace i ∧
    (localSlackLiteralAllocation P I d).loan i t h =
        (d t).nextFace i / (d t).controls.loanRate ∧
    (localSlackLiteralAllocation P I d).firmDeposit i t h = 0 ∧
    (localSlackLiteralAllocation P I d).labor i t h = localPrefixLabor P (d t) i := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem localSlackLiteralAllocation_bankBalance
    (P : Primitives LocalBridgePhase) (I : InheritedState)
    (d : ℕ → LocalPrefixDateData)
    (hratio : ∀ t, localPrefixReserveDepositRatio P (d t) ≠ 0)
    (hrow : ∀ t, localReducedRemainingResidual P (d t) 10 = 0) :
    BankBalance P (localSlackLiteralAllocation P I d) := by
  intro t h _hs
  have hb := localReducedRemainingResidual_bankBalance_eq P (d t)
    (hratio t) (hrow t)
  simpa [localSlackLiteralAllocation, withSourceAccountingCompletion,
    withSourceFiscalAccounts, withSourceRealAccounts,
    localSlackSettlementAllocation, localSlackPrivateBankCore,
    localDateBankEquity] using hb

theorem localSlackLiteralAllocation_creditClears
    (P : Primitives LocalBridgePhase) (I : InheritedState)
    (d : ℕ → LocalPrefixDateData) :
    CreditClears P (localSlackLiteralAllocation P I d) := by
  intro t h _hs
  change localPrefixReducedBankLoans P (d t) =
    ∑ i, P.mass i * ((d t).nextFace i / (d t).controls.loanRate)
  unfold localPrefixReducedBankLoans
  apply Finset.sum_congr rfl
  intro i _hi
  ring

theorem localSlackLiteralAllocation_depositsClear
    (P : Primitives LocalBridgePhase) (I : InheritedState)
    (d : ℕ → LocalPrefixDateData) :
    DepositsClear P (localSlackLiteralAllocation P I d) := by
  intro t h _hs
  simp [localSlackLiteralAllocation, withSourceAccountingCompletion,
    withSourceFiscalAccounts, withSourceRealAccounts,
    localSlackSettlementAllocation, localSlackPrivateBankCore]

theorem localSlackLiteralAllocation_currentNominalFaceConsistency
    (P : Primitives LocalBridgePhase) (I : InheritedState)
    (d : ℕ → LocalPrefixDateData)
    (hloanRate : ∀ t, (d t).controls.loanRate ≠ 0) :
    CurrentNominalFaceConsistency P (localSlackLiteralAllocation P I d) := by
  intro i t h _hs
  simp only [localSlackLiteralAllocation, withSourceAccountingCompletion,
    withSourceFiscalAccounts, withSourceRealAccounts,
    localSlackSettlementAllocation, localSlackPrivateBankCore]
  field_simp [hloanRate t]
  ring

theorem localSlackLiteralAllocation_laborClears
    (P : Primitives LocalBridgePhase) (I : InheritedState)
    (d : ℕ → LocalPrefixDateData) :
    LaborClears P (localSlackLiteralAllocation P I d) := by
  intro t h _hs
  rfl

theorem localSlackLiteralAllocation_prefix_realized
    (P : Primitives LocalBridgePhase) (I : InheritedState)
    (Z : LocalPrefixCoordinates) (tail : LocalPrefixContinuationRule)
    (state : ℕ → LocalPrefixStateSix)
    (controls : ℕ → LocalPrefixControlsTen)
    (hstate : state 0 = Z.stateTwo)
    (hcontrols : controls 0 = tail Z.stateTwo)
    (hinflationOne : Z.controlsOne.inflation ≠ 0)
    (hinflationTwo : (tail Z.stateTwo).inflation ≠ 0)
    (hequations : LocalReducedPrefixEquationsHold LocalPrefixBranch.slack
      P I Z .dateOne .recurrent tail) :
    LocalPrefixCoordinatesRealized P
      (localSlackLiteralAllocation P I
        (localSlackExactDateData P I Z tail state controls))
      .dateOne .recurrent Z := by
  have hpledge := hequations LocalPrefixEquation.commonPledgeOne
  change Z.stateTwo.commonPledgeValue -
      (1 - P.depreciation) * (tail Z.stateTwo).inflation *
        (tail Z.stateTwo).capitalPrice = 0 at hpledge
  unfold LocalPrefixCoordinatesRealized
  dsimp [localSlackLiteralAllocation, withSourceAccountingCompletion,
    withSourceFiscalAccounts, withSourceRealAccounts,
    localSlackSettlementAllocation, localSlackPrivateBankCore,
    localSlackExactDateData, localPrefixDateZeroData, localPrefixDateOneData,
    localRecurrentDateData, localDateBankEquity]
  rw [hstate, hcontrols]
  repeat' apply And.intro
  all_goals try rfl
  all_goals try field_simp [hinflationOne, hinflationTwo]
  all_goals linarith

/-- The concrete common plan is feasible once the displayed reduced quantities,
caps, settlement margin, and detailed-return solvency hold at every supported
history.  No feasibility or optimality record occurs among the premises. -/
theorem localSlackLiteralAllocation_commonPlan_feasible
    (P : Primitives LocalBridgePhase) (I : InheritedState)
    (d : ℕ → LocalPrefixDateData)
    (hpositive : ∀ t,
      0 < (d t).currentBankFace / (d t).controls.inflation ∧
      0 ≤ localPrefixReducedBankLoans P (d t) ∧
      0 ≤ (d t).currentReservesPre ∧
      0 ≤ localPrefixReducedBankDeposits P (d t))
    (hratio : ∀ t, localPrefixReserveDepositRatio P (d t) ≠ 0)
    (hbalanceRow : ∀ t, localReducedRemainingResidual P (d t) 10 = 0)
    (hcaps : ∀ t,
      localPrefixReducedBankDeposits P (d t) ≤
          P.bankDepositCap * ((d t).currentBankFace / (d t).controls.inflation) ∧
      localPrefixReducedBankLoans P (d t) ≤
          P.bankLoanCap * ((d t).currentBankFace / (d t).controls.inflation))
    (htightness : ∀ t, 0 < (d t).controls.tightness)
    (hsettlementMargin : ∀ t (h : History LocalBridgePhase t),
      FirmHistoryAdmissible P t h → ∀ ω, ω ∈ P.paymentSupport →
        P.reserveRequirementPath t h * localPrefixReducedBankDeposits P (d t) *
            (1 + P.paymentShock ω) ≤
          bankPostSettlementReservesAt P (localSlackLiteralAllocation P I d)
            t h (d t).controls.tightness (d t).currentReservesPre
              (localPrefixReducedBankDeposits P (d t)) ω)
    (hinitialFace : (d 0).currentBankFace = I.bankFace)
    (hsolvent : ∀ t (h : History LocalBridgePhase t),
      FirmHistoryAdmissible P t h → ∀ ω, ω ∈ P.paymentSupport → ∀ s,
        0 < P.tree.transition (currentState h) s →
          0 ≤ bankDetailedPortfolioReturnAt P
            (localSlackLiteralAllocation P I d) t h (d t).controls.tightness
              (localPrefixReducedBankLoans P (d t)) (d t).currentReservesPre
              (localPrefixReducedBankDeposits P (d t)) ω /
            (localSlackLiteralAllocation P I d).inflation (t + 1)
              (childHistory h s)) :
    BankFeasible P I (localSlackLiteralAllocation P I d)
      (fullRetentionCommonBankPlan P (localSlackLiteralAllocation P I d)) := by
  let X := localSlackLiteralAllocation P I d
  let p := fullRetentionCommonBankPlan P X
  have hbankBalance := localSlackLiteralAllocation_bankBalance P I d hratio hbalanceRow
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro t h _hs
    rcases hpositive t with ⟨hequity, hloans, hreserves, hdeposits⟩
    change 0 < X.bankEquity t h ∧ 0 ≤ (0 : ℝ) ∧
      0 < X.bankEquity t h ∧ 0 ≤ X.bankLoans t h ∧
      0 ≤ X.reservesPrePayment t h ∧ 0 ≤ X.bankDeposits t h
    simpa [X, localSlackLiteralAllocation, withSourceAccountingCompletion,
      withSourceFiscalAccounts, withSourceRealAccounts,
      localSlackSettlementAllocation, localSlackPrivateBankCore,
      localDateBankEquity] using
        And.intro hequity (And.intro (show 0 ≤ (0 : ℝ) by norm_num)
          (And.intro hequity (And.intro hloans (And.intro hreserves hdeposits))))
  · intro t h _hs
    change X.bankEquity t h = X.bankEquity t h - 0
    ring
  · intro t h hs
    exact hbankBalance t h hs
  · intro t h _hs
    simpa [p, fullRetentionCommonBankPlan, X,
      localSlackLiteralAllocation, withSourceAccountingCompletion,
      withSourceFiscalAccounts, withSourceRealAccounts,
      localSlackSettlementAllocation, localSlackPrivateBankCore,
      localDateBankEquity] using hcaps t
  · intro t h hs ω hω
    have hfacility := bankFacilityBorrowingAt_nonneg P X t h
      (X.bankTightness t h) (X.reservesPrePayment t h) (X.bankDeposits t h)
      (by simpa [X, localSlackLiteralAllocation, withSourceAccountingCompletion,
        withSourceFiscalAccounts, withSourceRealAccounts,
        localSlackSettlementAllocation, localSlackPrivateBankCore] using htightness t) ω
    refine ⟨?_, rfl, ?_⟩
    · exact hfacility
    · simpa [X, localSlackLiteralAllocation, withSourceAccountingCompletion,
        withSourceFiscalAccounts, withSourceRealAccounts,
        localSlackSettlementAllocation, localSlackPrivateBankCore] using
          hsettlementMargin t h hs ω hω
  · intro h _hs
    change X.bankEquity 0 h = I.bankFace / X.inflation 0 h
    simp [X, localSlackLiteralAllocation, withSourceAccountingCompletion,
      withSourceFiscalAccounts, withSourceRealAccounts,
      localSlackSettlementAllocation, localSlackPrivateBankCore,
      localDateBankEquity, hinitialFace]
  · intro t h hs ω hω s htransition
    rw [fullRetentionCommonBankPlan_grossReturn_eq_detailed P X t h ω hω]
    simpa [X, localSlackLiteralAllocation, withSourceAccountingCompletion,
      withSourceFiscalAccounts, withSourceRealAccounts,
      localSlackSettlementAllocation, localSlackPrivateBankCore] using
        hsolvent t h hs ω hω s htransition

def localPrefixCoordinatesVector
    (Z : LocalPrefixCoordinates) : Fin 33 → ℝ
  | 0 => Z.stateOne.capitalH
  | 1 => Z.stateOne.capitalL
  | 2 => Z.stateOne.firmFaceH
  | 3 => Z.stateOne.firmFaceL
  | 4 => Z.stateOne.bankFace
  | 5 => Z.stateOne.reserveRateLag
  | 6 => Z.stateOne.reservesPreLag
  | 7 => Z.controlsZero.consumptionH
  | 8 => Z.controlsZero.consumptionL
  | 9 => Z.controlsZero.workerConsumption
  | 10 => Z.controlsZero.wage
  | 11 => Z.controlsZero.inputPrice
  | 12 => Z.controlsZero.inflation
  | 13 => Z.controlsZero.capitalPrice
  | 14 => Z.controlsZero.depositRate
  | 15 => Z.controlsZero.loanRate
  | 16 => Z.controlsZero.tightness
  | 17 => Z.stateTwo.capitalH
  | 18 => Z.stateTwo.capitalL
  | 19 => Z.stateTwo.commonPledgeValue
  | 20 => Z.stateTwo.bankFace
  | 21 => Z.stateTwo.reserveRateLag
  | 22 => Z.stateTwo.reservesPreLag
  | 23 => Z.controlsOne.consumptionH
  | 24 => Z.controlsOne.consumptionL
  | 25 => Z.controlsOne.workerConsumption
  | 26 => Z.controlsOne.wage
  | 27 => Z.controlsOne.inputPrice
  | 28 => Z.controlsOne.inflation
  | 29 => Z.controlsOne.capitalPrice
  | 30 => Z.controlsOne.depositRate
  | 31 => Z.controlsOne.loanRate
  | 32 => Z.controlsOne.tightness
  | _ => 0

def localPrefixCoordinatesOfVector
    (z : Fin 33 → ℝ) : LocalPrefixCoordinates where
  stateOne := {
    capitalH := z 0
    capitalL := z 1
    firmFaceH := z 2
    firmFaceL := z 3
    bankFace := z 4
    reserveRateLag := z 5
    reservesPreLag := z 6 }
  controlsZero := {
    consumptionH := z 7
    consumptionL := z 8
    workerConsumption := z 9
    wage := z 10
    inputPrice := z 11
    inflation := z 12
    capitalPrice := z 13
    depositRate := z 14
    loanRate := z 15
    tightness := z 16 }
  stateTwo := {
    capitalH := z 17
    capitalL := z 18
    commonPledgeValue := z 19
    bankFace := z 20
    reserveRateLag := z 21
    reservesPreLag := z 22 }
  controlsOne := {
    consumptionH := z 23
    consumptionL := z 24
    workerConsumption := z 25
    wage := z 26
    inputPrice := z 27
    inflation := z 28
    capitalPrice := z 29
    depositRate := z 30
    loanRate := z 31
    tightness := z 32 }

def localPrefixEquationOfIndex : Fin 33 → LocalPrefixEquation
  | 0 => .firmBudgetZeroH
  | 1 => .firmBudgetZeroL
  | 2 => .firmCapitalEulerZeroH
  | 3 => .firmCapitalEulerZeroL
  | 4 => .firmRegimeZeroH
  | 5 => .firmRegimeZeroL
  | 6 => .bankEquityZero
  | 7 => .capitalSupplyZero
  | 8 => .resourcesZero
  | 9 => .workerLaborZero
  | 10 => .householdEulerZero
  | 11 => .nkpcZero
  | 12 => .reserveRateRuleZero
  | 13 => .reserveQuantityRuleZero
  | 14 => .loanPricingZero
  | 15 => .depositPricingZero
  | 16 => .bankBalanceZero
  | 17 => .firmBudgetOneH
  | 18 => .firmBudgetOneL
  | 19 => .firmCapitalEulerOneH
  | 20 => .firmCapitalEulerOneL
  | 21 => .commonPledgeOne
  | 22 => .bankEquityOne
  | 23 => .capitalSupplyOne
  | 24 => .resourcesOne
  | 25 => .workerLaborOne
  | 26 => .householdEulerOne
  | 27 => .nkpcOne
  | 28 => .reserveRateRuleOne
  | 29 => .reserveQuantityRuleOne
  | 30 => .loanPricingOne
  | 31 => .depositPricingOne
  | 32 => .bankBalanceOne
  | _ => .bankBalanceOne

noncomputable def localReducedPrefixResidualVector
    (branch : LocalPrefixBranch) (P : Primitives S) (I : InheritedState)
    (dateOne recurrent : S) (tail : LocalPrefixContinuationRule) :
    (Fin 33 → ℝ) → (Fin 33 → ℝ) :=
  fun z row ↦ localReducedPrefixResidual branch P I
    (localPrefixCoordinatesOfVector z) dateOne recurrent tail
      (localPrefixEquationOfIndex row)

/-- Every one of the 33 bridge coordinates is a positive economic level.  The
paper differentiates their logarithmic deviations, so this domain condition
is part of the chart and cannot be recovered merely from Jacobian rank. -/
def LocalPrefixCoordinatesPositive (Z : LocalPrefixCoordinates) : Prop :=
  ∀ j, 0 < localPrefixCoordinatesVector Z j

/-- Positive log chart about the bridge: the zero vector represents `Z0`, and
the `j`th coordinate is `Z0_j * exp z_j`. -/
noncomputable def localPrefixLogChart
    (Z0 : LocalPrefixCoordinates) (z : Fin 33 → ℝ) : LocalPrefixCoordinates :=
  localPrefixCoordinatesOfVector
    (fun j ↦ localPrefixCoordinatesVector Z0 j * Real.exp (z j))

/-- Pull the concrete 33 residuals back through the source's positive log
chart.  This is the function whose Jacobian is enclosed in the manuscript. -/
noncomputable def localReducedPrefixLogResidualVector
    (branch : LocalPrefixBranch) (P : Primitives S) (I : InheritedState)
    (Z0 : LocalPrefixCoordinates) (dateOne recurrent : S)
    (tail : LocalPrefixContinuationRule) :
    (Fin 33 → ℝ) → (Fin 33 → ℝ) :=
  fun z row ↦ localReducedPrefixResidual branch P I
    (localPrefixLogChart Z0 z) dateOne recurrent tail
      (localPrefixEquationOfIndex row)

/-- The old raw-level rank condition remains available for diagnostics, but it
is not the Jacobian condition consumed by Proposition 4.2. -/
def LocalReducedPrefixJacobianInvertibleAt
    (branch : LocalPrefixBranch) (P : Primitives S) (I : InheritedState)
    (Z : LocalPrefixCoordinates) (dateOne recurrent : S)
    (tail : LocalPrefixContinuationRule) : Prop :=
  let F := localReducedPrefixResidualVector branch P I dateOne recurrent tail
  let z := localPrefixCoordinatesVector Z
  DifferentiableAt ℝ F z ∧ Function.Bijective (fderiv ℝ F z)

/-- Source-strength Jacobian certificate in log coordinates.  It requires a
genuine differentiable neighborhood, identifies the inverse with the actual
Fréchet derivative at the zero log deviation, and records the strict
operator-norm enclosure.  Proving this from directed arithmetic remains an
OPEN numerical bridge; no free matrix is accepted without the two inverse
identities. -/
def LocalReducedPrefixLogJacobianCertifiedAt
    (branch : LocalPrefixBranch) (P : Primitives S) (I : InheritedState)
    (Z0 : LocalPrefixCoordinates) (dateOne recurrent : S)
    (tail : LocalPrefixContinuationRule) (inverseNormBound : ℝ) : Prop :=
  let F := localReducedPrefixLogResidualVector branch P I Z0
    dateOne recurrent tail
  let J := fderiv ℝ F (0 : Fin 33 → ℝ)
  LocalPrefixCoordinatesPositive Z0 ∧
  ∃ radius : ℝ, 0 < radius ∧
    DifferentiableOn ℝ F (Metric.ball (0 : Fin 33 → ℝ) radius) ∧
    ∃ Jinv : (Fin 33 → ℝ) →L[ℝ] (Fin 33 → ℝ),
      Function.LeftInverse Jinv J ∧ Function.RightInverse Jinv J ∧
      ‖Jinv‖ < inverseNormBound

/-! ### Exact local continuation behind the finite prefix -/

/-- Start the continuation economy at the recurrent calendar state without
altering any real, financial or policy primitive. -/
def Primitives.withInitialState (P : Primitives S) (initial : S) : Primitives S :=
  { P with tree := { P.tree with initial := initial } }

def localPrefixStateSixVector (x : LocalPrefixStateSix) : Fin 6 → ℝ
  | 0 => x.capitalH
  | 1 => x.capitalL
  | 2 => x.commonPledgeValue
  | 3 => x.bankFace
  | 4 => x.reserveRateLag
  | 5 => x.reservesPreLag
  | _ => 0

def localPrefixStateSixOfVector (x : Fin 6 → ℝ) : LocalPrefixStateSix where
  capitalH := x 0
  capitalL := x 1
  commonPledgeValue := x 2
  bankFace := x 3
  reserveRateLag := x 4
  reservesPreLag := x 5

def localPrefixControlsTenVector (u : LocalPrefixControlsTen) : Fin 10 → ℝ
  | 0 => u.consumptionH
  | 1 => u.consumptionL
  | 2 => u.workerConsumption
  | 3 => u.wage
  | 4 => u.inputPrice
  | 5 => u.inflation
  | 6 => u.capitalPrice
  | 7 => u.depositRate
  | 8 => u.loanRate
  | 9 => u.tightness
  | _ => 0

def LocalPrefixStateSixPositive (x : LocalPrefixStateSix) : Prop :=
  ∀ j, 0 < localPrefixStateSixVector x j

def LocalPrefixStateSixNear
    (radius : ℝ) (x0 x : LocalPrefixStateSix) : Prop :=
  0 < radius ∧ ∀ j,
    |localPrefixStateSixVector x j - localPrefixStateSixVector x0 j| < radius

noncomputable def localPrefixStateSixLogChart
    (x0 : LocalPrefixStateSix) (z : Fin 6 → ℝ) : LocalPrefixStateSix :=
  localPrefixStateSixOfVector
    (fun j ↦ localPrefixStateSixVector x0 j * Real.exp (z j))

/-- Ten log control responses of the exact continuation to six log state
deviations.  Its derivative at zero is the source matrix `P_*`. -/
noncomputable def localContinuationLogResponse
    (x0 : LocalPrefixStateSix) (tail : LocalPrefixContinuationRule) :
    (Fin 6 → ℝ) → (Fin 10 → ℝ) :=
  fun z j ↦ Real.log
    (localPrefixControlsTenVector (tail (localPrefixStateSixLogChart x0 z)) j /
      localPrefixControlsTenVector (tail x0) j)

/-- The six reduced states determine the corresponding inherited physical and
nominal positions at the start of the recurrent continuation.  Remaining
household/public faces are reconstructed subject to the equilibrium's nominal
face identity rather than inserted into the six-state carrier. -/
def LocalContinuationInheritedStateMatches
    (P : Primitives S) (x : LocalPrefixStateSix) (I : InheritedState) : Prop :=
  I.capital = localPrefixStateSixCapital x ∧
  I.firmFace = localPrefixStateSixFace P x ∧
  I.bankFace = x.bankFace ∧
  I.reserveRateLag = x.reserveRateLag ∧
  I.reservesPreLag = x.reservesPreLag

/-- The continuation rule returns the actual initial controls of its full
recurrent allocation. -/
def LocalContinuationInitialControlsRealized
    (P : Primitives S) (X : Allocation S) (tail : LocalPrefixContinuationRule)
    (x : LocalPrefixStateSix) : Prop :=
  let h0 := bridgeDateZeroHistory P
  let u := tail x
  u.consumptionH = X.firmConsumption FirmType.H 0 h0 ∧
  u.consumptionL = X.firmConsumption FirmType.L 0 h0 ∧
  u.workerConsumption = X.workerConsumption 0 h0 ∧
  u.wage = X.wage 0 h0 ∧
  u.inputPrice = X.inputPrice 0 h0 ∧
  u.inflation = X.inflation 0 h0 ∧
  u.capitalPrice = X.capitalPrice 0 h0 ∧
  u.depositRate = X.depositRate 0 h0 ∧
  u.loanRate = X.loanRate 0 h0 ∧
  u.tightness = X.bankTightness 0 h0

/-- Pointwise sup neighborhood for every economically carried allocation
field.  This replaces the earlier partial topology that omitted inherited
faces, bank portfolios, policy quantities, ownership income and fiscal flows. -/
def AllocationFullNear
    (P : Primitives S) (radius : ℝ) (X Y : Allocation S) : Prop :=
  0 < radius ∧ ∀ t h, FirmHistoryAdmissible P t h →
    (∀ i, |X.firmConsumption i t h - Y.firmConsumption i t h| < radius) ∧
    |X.workerConsumption t h - Y.workerConsumption t h| < radius ∧
    |X.workerLabor t h - Y.workerLabor t h| < radius ∧
    (∀ i, |X.capital i t h - Y.capital i t h| < radius) ∧
    |X.aggregateCapital t h - Y.aggregateCapital t h| < radius ∧
    (∀ i, |X.labor i t h - Y.labor i t h| < radius) ∧
    (∀ i, |X.loan i t h - Y.loan i t h| < radius) ∧
    (∀ i, |X.firmDeposit i t h - Y.firmDeposit i t h| < radius) ∧
    (∀ i, |X.firmFace i t h - Y.firmFace i t h| < radius) ∧
    (∀ i, |X.firmWealth i t h - Y.firmWealth i t h| < radius) ∧
    (∀ i, |X.collateralDual i t h - Y.collateralDual i t h| < radius) ∧
    |X.inputPrice t h - Y.inputPrice t h| < radius ∧
    |X.wage t h - Y.wage t h| < radius ∧
    |X.inflation t h - Y.inflation t h| < radius ∧
    |X.capitalPrice t h - Y.capitalPrice t h| < radius ∧
    |X.loanRate t h - Y.loanRate t h| < radius ∧
    |X.depositRate t h - Y.depositRate t h| < radius ∧
    |X.reserveRate t h - Y.reserveRate t h| < radius ∧
    |X.interbankRate t h - Y.interbankRate t h| < radius ∧
    |X.facilityRate t h - Y.facilityRate t h| < radius ∧
    |X.bankTightness t h - Y.bankTightness t h| < radius ∧
    |X.reservesPrePayment t h - Y.reservesPrePayment t h| < radius ∧
    |X.reservesPostPayment t h - Y.reservesPostPayment t h| < radius ∧
    |X.bankLoans t h - Y.bankLoans t h| < radius ∧
    |X.bankDeposits t h - Y.bankDeposits t h| < radius ∧
    |X.bankEquity t h - Y.bankEquity t h| < radius ∧
    |X.bankRetainedEquity t h - Y.bankRetainedEquity t h| < radius ∧
    |X.bankDividend t h - Y.bankDividend t h| < radius ∧
    |X.bankNetIncome t h - Y.bankNetIncome t h| < radius ∧
    |X.retailerNetIncome t h - Y.retailerNetIncome t h| < radius ∧
    |X.capitalProducerNetIncome t h - Y.capitalProducerNetIncome t h| < radius ∧
    |X.interbankPosition t h - Y.interbankPosition t h| < radius ∧
    |X.facilityBorrowing t h - Y.facilityBorrowing t h| < radius ∧
    |X.householdDeposits t h - Y.householdDeposits t h| < radius ∧
    |X.householdBonds t h - Y.householdBonds t h| < radius ∧
    |X.centralBankBonds t h - Y.centralBankBonds t h| < radius ∧
    |X.governmentBondRate t h - Y.governmentBondRate t h| < radius ∧
    |X.tax t h - Y.tax t h| < radius ∧
    |X.output t h - Y.output t h| < radius ∧
    |X.investment t h - Y.investment t h| < radius ∧
    |X.capitalCreationCost t h - Y.capitalCreationCost t h| < radius ∧
    |X.priceAdjustmentResourceCost t h - Y.priceAdjustmentResourceCost t h| < radius ∧
    |X.retailerLogRelativePrice t h - Y.retailerLogRelativePrice t h| < radius

noncomputable def localNormalizedSlackL
    (P : Primitives S) (Z : LocalPrefixCoordinates) : ℝ :=
  1 - Z.stateOne.firmFaceL /
    (P.pledgeability FirmType.L * (1 - P.depreciation) *
      Z.controlsOne.inflation * Z.controlsOne.capitalPrice *
      Z.stateOne.capitalL)

noncomputable def localNormalizedCollateralDualL
    (P : Primitives S) (Z : LocalPrefixCoordinates) : ℝ :=
  1 / Z.controlsZero.loanRate -
    (P.entrepreneurDiscount *
      crraMarginal P.entrepreneurRiskAversion Z.controlsOne.consumptionL /
      crraMarginal P.entrepreneurRiskAversion Z.controlsZero.consumptionL) /
      Z.controlsOne.inflation

def LocalScalarComplementarityL
    (P : Primitives S) (Z : LocalPrefixCoordinates) : Prop :=
  0 ≤ localNormalizedSlackL P Z ∧
  0 ≤ localNormalizedCollateralDualL P Z ∧
  localNormalizedSlackL P Z * localNormalizedCollateralDualL P Z = 0

/-! ### Scalar Schur/implicit reduction used by Proposition 4.2 -/

/-- Parameter order `(s,v_R,v_M,v_ρ,v_Δ)` used in the source expansion. -/
def localScalarParameterIntervention
    (y : Fin 5 → ℝ) : InitialPolicyIntervention where
  reserveRateInnovation := y 1
  reserveQuantityInnovation := y 2
  reserveRequirement := y 3
  corridorWidth := y 4

/-- The binding system with L's collateral row replaced by a prescribed
normalized slack.  The omitted interior-funding condition is evaluated after
solving and becomes the scalar map `M`. -/
noncomputable def localBindingResidualWithSlack
    (P : Primitives S) (I : InheritedState) (Z0 : LocalPrefixCoordinates)
    (dateOne recurrent : S) (tail : LocalPrefixContinuationRule)
    (y : Fin 5 → ℝ) (z : Fin 33 → ℝ) (row : Fin 33) : ℝ :=
  let Pv := initialIntervenedPrimitives P (localScalarParameterIntervention y)
  let Z := localPrefixLogChart Z0 z
  if localPrefixEquationOfIndex row = LocalPrefixEquation.firmRegimeZeroL then
    localNormalizedSlackL Pv Z - y 0
  else
    localReducedPrefixResidual LocalPrefixBranch.binding Pv I Z
      dateOne recurrent tail (localPrefixEquationOfIndex row)

/-- The reduced marginal value is not an arbitrary residual: it is exactly
the normalized L funding dual evaluated at the implicit economic coordinates. -/
noncomputable def localScalarReducedMap
    (P : Primitives S) (Z0 : LocalPrefixCoordinates)
    (solutionLog : (Fin 5 → ℝ) → (Fin 33 → ℝ))
    (y : Fin 5 → ℝ) : ℝ :=
  localNormalizedCollateralDualL P
    (localPrefixLogChart Z0 (solutionLog y))

def localScalarSlackDirection : Fin 5 → ℝ :=
  fun j ↦ if j = 0 then 1 else 0

def localScalarReserveRateDirection : Fin 5 → ℝ :=
  fun j ↦ if j = 1 then 1 else 0

/-- Exact local implicit reduction.  `solutionLog` is pinned to the zero bridge,
solves the actual modified 33-row system throughout a parameter neighborhood,
is locally unique there, and is differentiable.  The derivative inequalities
are imposed on the derivative of the resulting economic map itself, including
the source interval for `b = ∂s M`; they are OPEN numerical obligations. -/
def LocalScalarImplicitReduction
    (P : Primitives S) (I : InheritedState) (Z0 : LocalPrefixCoordinates)
    (dateOne recurrent : S) (tail : LocalPrefixContinuationRule)
    (solutionLog : (Fin 5 → ℝ) → (Fin 33 → ℝ)) : Prop :=
  let M := localScalarReducedMap P Z0 solutionLog
  let dM := fderiv ℝ M (0 : Fin 5 → ℝ)
  solutionLog 0 = 0 ∧
  ∃ radius : ℝ, 0 < radius ∧
    DifferentiableOn ℝ solutionLog (Metric.ball (0 : Fin 5 → ℝ) radius) ∧
    DifferentiableOn ℝ M (Metric.ball (0 : Fin 5 → ℝ) radius) ∧
    (∀ y ∈ Metric.ball (0 : Fin 5 → ℝ) radius,
      ∀ row, localBindingResidualWithSlack P I Z0 dateOne recurrent tail
        y (solutionLog y) row = 0) ∧
    (∀ y ∈ Metric.ball (0 : Fin 5 → ℝ) radius,
      ∀ z ∈ Metric.ball (solutionLog y) radius,
        (∀ row, localBindingResidualWithSlack P I Z0 dateOne recurrent tail
          y z row = 0) → z = solutionLog y) ∧
    -2.376742673 < dM localScalarSlackDirection ∧
    dM localScalarSlackDirection < -2.376742670 ∧
    dM localScalarReserveRateDirection < 0

def CompetitiveEquilibrium (P : Primitives S) (I : InheritedState)
    (X : Allocation S) : Prop :=
  MonetaryPolicyPrimitiveDomain P I ∧ PositiveDomain P X ∧
  MonetaryPolicyRules P I X ∧
  (∀ i, FirmOptimal P I X i) ∧
  HouseholdOptimal P I X ∧ BankPopulationEquilibrium P I X ∧ RetailOptimal P X ∧
  CapitalProducerOptimal P X ∧
  FirmBudgetFlows P I X ∧ HouseholdBudgetFlows P I X ∧
  InheritedNominalFaceConsistency P I ∧ CurrentNominalFaceConsistency P X ∧
  AggregateProduction P I X ∧
  CapitalProducerAccounts P X ∧ AccountingIdentities P X ∧
  BankBalance P X ∧ FiscalClosure P I X ∧
  CreditClears P X ∧ DepositsClear P X ∧ CapitalClears P I X ∧
  LaborClears P X ∧ ResourceClears P X

/-- A full competitive equilibrium carrying the finite strict bank witness and
its separate dynamic analytic data implies the six bank equations appearing at
dates zero and one of the reduced prefix.  The reverse prefix-to-equilibrium
direction is intentionally absent. -/
theorem competitiveEquilibrium_localPrefixBankRows
    (P : Primitives S) (I : InheritedState) (X : Allocation S)
    (dateOne : S)
    (hequilibrium : CompetitiveEquilibrium P I X)
    (hbank : FiniteBankPrefixDynamicWitness P I X dateOne) :
    (localLoanPricingResidual P X 0 (bridgeDateZeroHistory P) = 0 ∧
      localDepositPricingResidual P X 0 (bridgeDateZeroHistory P) = 0 ∧
      localBankBalanceResidual X 0 (bridgeDateZeroHistory P) = 0) ∧
    (localLoanPricingResidual P X 1 (bridgeDateOneHistory P dateOne) = 0 ∧
      localDepositPricingResidual P X 1 (bridgeDateOneHistory P dateOne) = 0 ∧
      localBankBalanceResidual X 1 (bridgeDateOneHistory P dateOne) = 0) := by
  exact localPrefixBankRows_eq_zero_of_dynamic_witness P I X dateOne hbank
    hequilibrium.2.1

/-- A sixteen-date contraction controls every residue class once the block
factor is dominated by the sixteenth power of the chosen temporal weight.
This is the analytic tail bridge used after a matrix certificate supplies the
one-block estimate; it does not itself certify that matrix estimate or a
nonlinear invariant neighborhood. -/
theorem recurrentTailBlockSixteen_geometric_bound
    (u : ℕ → ℝ) (q alpha C : ℝ)
    (hq : 0 ≤ q) (halpha : 0 ≤ alpha) (hC : 0 ≤ C)
    (hblock : q ≤ alpha ^ 16)
    (hstep : ∀ n, u (n + 16) ≤ q * u n)
    (hbase : ∀ r, r < 16 → u r ≤ C * alpha ^ r) :
    ∀ k r, r < 16 →
      u (16 * k + r) ≤ C * alpha ^ (16 * k + r) := by
  intro k
  induction k with
  | zero =>
      intro r hr
      simpa using hbase r hr
  | succ k ih =>
      intro r hr
      calc
        u (16 * (k + 1) + r) = u ((16 * k + r) + 16) := by
          congr 1
          omega
        _ ≤ q * u (16 * k + r) := hstep _
        _ ≤ q * (C * alpha ^ (16 * k + r)) :=
          mul_le_mul_of_nonneg_left (ih r hr) hq
        _ ≤ alpha ^ 16 * (C * alpha ^ (16 * k + r)) :=
          mul_le_mul_of_nonneg_right hblock
            (mul_nonneg hC (pow_nonneg halpha _))
        _ = C * alpha ^ (16 * (k + 1) + r) := by
          rw [show 16 * (k + 1) + r = (16 * k + r) + 16 by omega, pow_add]
          ring

/-- The outward-rounded sixteen-step state-transition bound recorded for the
pinned finite recurrent case fits the temporal weight `0.985` with strict
arithmetic slack.  Connecting the premise to the exact transition matrix is a
separate interval-certificate obligation. -/
theorem finiteRecurrent_sixteenStep_lt_weight :
    (774936 : ℝ) / 1000000 < ((197 : ℝ) / 200) ^ 16 := by
  norm_num [div_pow]

/-- Concrete specialization of the block estimate to the outward-rounded
transition bound and temporal weight used by the pinned finite recurrent case.
The hypothesis `hstep` is where the interval matrix certificate must be linked
to the actual state sequence. -/
theorem finiteRecurrent_weightedTail_bound
    (u : ℕ → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hstep : ∀ n, u (n + 16) ≤ ((774936 : ℝ) / 1000000) * u n)
    (hbase : ∀ r, r < 16 → u r ≤ C * ((197 : ℝ) / 200) ^ r) :
    ∀ k r, r < 16 →
      u (16 * k + r) ≤ C * ((197 : ℝ) / 200) ^ (16 * k + r) := by
  exact recurrentTailBlockSixteen_geometric_bound u
    ((774936 : ℝ) / 1000000) ((197 : ℝ) / 200) C
    (by norm_num) (by norm_num) hC
    finiteRecurrent_sixteenStep_lt_weight.le hstep hbase

/-- Once the pinned sixteen-date block estimate and the first sixteen weighted
bounds have been linked to a nonnegative tail quantity, that quantity is
summable and satisfies the required terminal decay.  This discharges the
analytic consequence of the block estimate; it does not construct the exact
recurrent continuation or certify the interval matrix estimate supplying
`hstep`. -/
theorem finiteRecurrent_weightedTail_summable_tendsto_zero
    (u : ℕ → ℝ) (C : ℝ) (hu : ∀ n, 0 ≤ u n) (hC : 0 ≤ C)
    (hstep : ∀ n, u (n + 16) ≤ ((774936 : ℝ) / 1000000) * u n)
    (hbase : ∀ r, r < 16 → u r ≤ C * ((197 : ℝ) / 200) ^ r) :
    Summable u ∧ Tendsto u atTop (nhds 0) := by
  have hall : ∀ n, u n ≤ C * ((197 : ℝ) / 200) ^ n := by
    intro n
    have hr : n % 16 < 16 := Nat.mod_lt n (by omega)
    have hbound := finiteRecurrent_weightedTail_bound u C hC hstep hbase
      (n / 16) (n % 16) hr
    have hn : 16 * (n / 16) + n % 16 = n := by omega
    simpa [hn] using hbound
  have hgeom : Summable (fun n : ℕ ↦ C * ((197 : ℝ) / 200) ^ n) :=
    (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left C
  have hpow : Tendsto (fun n : ℕ ↦ ((197 : ℝ) / 200) ^ n) atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hupper : Tendsto (fun n : ℕ ↦ C * ((197 : ℝ) / 200) ^ n) atTop (nhds 0) := by
    simpa using (Tendsto.const_mul C hpow)
  constructor
  · exact Summable.of_nonneg_of_le hu hall hgeom
  · exact squeeze_zero hu hall hupper

/-- A direct geometric absolute envelope gives both absolute summability and
terminal decay.  This is the analytic bridge appropriate for membership in a
weighted sequence-space ball: it does not assume that the enclosed nonlinear
path satisfies the linear candidate's sixteen-date recurrence. -/
theorem summable_tendsto_zero_of_abs_le_geometric
    (u : ℕ → ℝ) (C alpha : ℝ)
    (hC : 0 ≤ C) (halpha0 : 0 ≤ alpha) (halpha1 : alpha < 1)
    (hbound : ∀ n, |u n| ≤ C * alpha ^ n) :
    Summable u ∧ Tendsto u atTop (nhds 0) := by
  have hbound' : ∀ n, |u n| ≤ |C| * alpha ^ n := by
    intro n
    simpa [abs_of_nonneg hC] using hbound n
  have hgeom : Summable (fun n : ℕ ↦ |C| * alpha ^ n) :=
    (summable_geometric_of_lt_one halpha0 halpha1).mul_left |C|
  have habs : Summable (fun n : ℕ ↦ |u n|) :=
    Summable.of_nonneg_of_le (fun n ↦ abs_nonneg (u n)) hbound' hgeom
  have hpow : Tendsto (fun n : ℕ ↦ alpha ^ n) atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one halpha0 halpha1
  have hupper : Tendsto (fun n : ℕ ↦ |C| * alpha ^ n) atTop (nhds 0) := by
    simpa using (Tendsto.const_mul |C| hpow)
  have habsZero : Tendsto (fun n : ℕ ↦ |u n|) atTop (nhds 0) :=
    squeeze_zero (fun n ↦ abs_nonneg (u n)) hbound' hupper
  exact ⟨habs.of_abs, (tendsto_zero_iff_abs_tendsto_zero _).2 habsZero⟩

/-- Direct specialization to the `0.985` temporal weight used by the certified
finite recurrent experiment.  The premise is the weighted-envelope statement
that still has to be supplied for the exact nonlinear economic quantity. -/
theorem finiteRecurrent_weightedEnvelope_summable_tendsto_zero
    (u : ℕ → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ n, |u n| ≤ C * ((197 : ℝ) / 200) ^ n) :
    Summable u ∧ Tendsto u atTop (nhds 0) := by
  exact summable_tendsto_zero_of_abs_le_geometric u C
    ((197 : ℝ) / 200) hC (by norm_num) (by norm_num) hbound

/-- A direct weighted envelope for the literal owner-payoff terms is sufficient
for the candidate bank continuation objective to be well-defined.  This is
conditional and does not construct the candidate policy or its envelope. -/
theorem bankContinuationObjectiveWellDefinedAt_of_weightedEnvelope
    {S : Type*} [Fintype S]
    (P : Primitives S) (X : Allocation S) (t : ℕ) (h : History S t)
    (p : BankContinuationPolicy S P.paymentSupport) (C alpha : ℝ)
    (hC : 0 ≤ C) (halpha0 : 0 ≤ alpha) (halpha1 : alpha < 1)
    (hpayoff : ∀ n,
      |bankContinuationPayoffTermAt P X t h p n| ≤
        C * alpha ^ n) :
    BankContinuationObjectiveWellDefinedAt P X t h p := by
  exact (summable_tendsto_zero_of_abs_le_geometric
    (bankContinuationPayoffTermAt P X t h p) C alpha hC halpha0 halpha1
    hpayoff).1

/-- A separate weighted envelope for surviving discounted bank equity implies
the source terminal condition.  Payoff summability alone is deliberately not
used as a substitute for this terminal-wealth bound. -/
theorem bankContinuationTerminalConditionAt_of_weightedEnvelope
    {S : Type*} [Fintype S]
    (P : Primitives S) (X : Allocation S) (t : ℕ) (h : History S t)
    (p : BankContinuationPolicy S P.paymentSupport) (C alpha : ℝ)
    (hC : 0 ≤ C) (halpha0 : 0 ≤ alpha) (halpha1 : alpha < 1)
    (hterminal : ∀ T,
      |bankSurvivingValueTermAt P X t h p T| ≤
        C * alpha ^ T) :
    BankContinuationTerminalConditionAt P X t h p := by
  exact (summable_tendsto_zero_of_abs_le_geometric
    (bankSurvivingValueTermAt P X t h p) C alpha hC halpha0 halpha1
    hterminal).2

/-- The two weighted envelopes jointly discharge the analytic fields of bank
continuation optimality.  They remain separate premises because discounted
owner-payoff summability and surviving terminal wealth are different economic
objects. -/
theorem bankContinuationObjectiveAndTerminal_of_weightedEnvelopes
    {S : Type*} [Fintype S]
    (P : Primitives S) (X : Allocation S) (t : ℕ) (h : History S t)
    (p : BankContinuationPolicy S P.paymentSupport)
    (payoffBound payoffRate terminalBound terminalRate : ℝ)
    (hpayoffBound : 0 ≤ payoffBound)
    (hpayoffRate0 : 0 ≤ payoffRate) (hpayoffRate1 : payoffRate < 1)
    (hterminalBound : 0 ≤ terminalBound)
    (hterminalRate0 : 0 ≤ terminalRate) (hterminalRate1 : terminalRate < 1)
    (hpayoff : ∀ n,
      |bankContinuationPayoffTermAt P X t h p n| ≤
        payoffBound * payoffRate ^ n)
    (hterminal : ∀ T,
      |bankSurvivingValueTermAt P X t h p T| ≤
        terminalBound * terminalRate ^ T) :
    BankContinuationObjectiveWellDefinedAt P X t h p ∧
      BankContinuationTerminalConditionAt P X t h p := by
  exact ⟨bankContinuationObjectiveWellDefinedAt_of_weightedEnvelope
      P X t h p payoffBound payoffRate hpayoffBound hpayoffRate0
        hpayoffRate1 hpayoff,
    bankContinuationTerminalConditionAt_of_weightedEnvelope
      P X t h p terminalBound terminalRate hterminalBound hterminalRate0
        hterminalRate1 hterminal⟩

/-- Exact continuation theorem required by the source finite-prefix reduction.
For every nearby positive six-state input it constructs a full recurrent
competitive equilibrium (hence full individual optimality and terminal
conditions), realizes the ten controls, and is unique in the explicit full
allocation neighborhood.  The log response is differentiable on a
neighborhood, so the finite-prefix Jacobian uses an economic continuation
derivative rather than an arbitrary function derivative. -/
def LocalExactContinuationAround
    (P : Primitives S) (recurrent : S) (x0 : LocalPrefixStateSix)
    (tail : LocalPrefixContinuationRule) : Prop :=
  let Q := P.withInitialState recurrent
  let response := localContinuationLogResponse x0 tail
  LocalPrefixStateSixPositive x0 ∧
  (∀ j, 0 < localPrefixControlsTenVector (tail x0) j) ∧
  ∃ radius : ℝ, 0 < radius ∧
    DifferentiableOn ℝ response (Metric.ball (0 : Fin 6 → ℝ) radius) ∧
    ∃ inherited : LocalPrefixStateSix → InheritedState,
      ∃ continuation : LocalPrefixStateSix → Allocation S,
        ∀ x, LocalPrefixStateSixNear radius x0 x →
          LocalPrefixStateSixPositive x →
          LocalContinuationInheritedStateMatches Q x (inherited x) ∧
          CompetitiveEquilibrium Q (inherited x) (continuation x) ∧
          LocalContinuationInitialControlsRealized Q (continuation x) tail x ∧
          ∀ Y, CompetitiveEquilibrium Q (inherited x) Y →
            AllocationFullNear Q radius (continuation x) Y →
            Y = continuation x

/-- The actual economy indexed by an announced intervention.  In particular,
the scalar `h` used in Proposition 4.2 changes the monetary rule entering the
equilibrium equations; it is not an unused theorem parameter. -/
def CompetitiveEquilibriumWithInitialIntervention
    (P : Primitives S) (I : InheritedState)
    (v : InitialPolicyIntervention) (X : Allocation S) : Prop :=
  CompetitiveEquilibrium (initialIntervenedPrimitives P v) I X

/-- Aggregate bank renewal is recovered from the type population inside an
equilibrium; it is not an additional equilibrium certificate. -/
theorem competitiveEquilibrium_bankRenewalFlows
    (P : Primitives S) (I : InheritedState) (X : Allocation S)
    (H : CompetitiveEquilibrium P I X) : BankRenewalFlows P I X := by
  rcases H with ⟨_hpolicyDomain, _hpositive, _hpolicy, _hfirms, _hhousehold,
    hpopulation, _hretail, _hcapitalOptimal, _hfirmBudget, _hhouseholdBudget,
    hinheritedFaces, _hrest⟩
  exact bankRenewalFlows_of_population P I X hinheritedFaces.1 hpopulation

/-- Aggregate settlement is likewise recovered from the equilibrium's bank
population rather than assumed as a second carrier. -/
theorem competitiveEquilibrium_settlementClears
    (P : Primitives S) (I : InheritedState) (X : Allocation S)
    (H : CompetitiveEquilibrium P I X) : SettlementClears P X := by
  rcases H with ⟨_hpolicyDomain, _hpositive, _hpolicy, _hfirms, _hhousehold,
    hpopulation, _hrest⟩
  exact settlementClears_of_bankPopulation P I X hpopulation

/-- A financial branch is calculated from choices and the collateral
constraint, never supplied as a certificate that an equilibrium exists. -/
def SlackBorrowerBranch (P : Primitives S) (X : Allocation S)
    (i : FirmType) (t : ℕ) (h : History S t) : Prop :=
  0 < X.loan i t h ∧ X.collateralDual i t h = 0 ∧
    ∀ s, 0 < P.tree.transition (currentState h) s →
      X.loanRate t h * X.loan i t h <
        P.pledgeability i * (1 - P.depreciation) *
          (X.inflation (t + 1) (childHistory h s) *
            X.capitalPrice (t + 1) (childHistory h s)) * X.capital i t h

def BindingBorrowerBranch (P : Primitives S) (X : Allocation S)
    (i : FirmType) (t : ℕ) (h : History S t) : Prop :=
  0 < X.loan i t h ∧ 0 < X.collateralDual i t h ∧
    (∀ s, 0 < P.tree.transition (currentState h) s →
      X.loanRate t h * X.loan i t h ≤
        P.pledgeability i * (1 - P.depreciation) *
          (X.inflation (t + 1) (childHistory h s) *
            X.capitalPrice (t + 1) (childHistory h s)) * X.capital i t h) ∧
    ∃ s,
      0 < P.tree.transition (currentState h) s ∧
      X.loanRate t h * X.loan i t h =
        P.pledgeability i * (1 - P.depreciation) *
          (X.inflation (t + 1) (childHistory h s) *
            X.capitalPrice (t + 1) (childHistory h s)) * X.capital i t h

end Ventura26LiquidityAllocation
