import Ventura26LiquidityAllocation.CurrentSourcePinnedAggregateOutputContinuity
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# SOURCE Cobb-Douglas production: exact endogenous-labor closed form

The model's actual original functions are
  localPrefixLabor P d i =
    (beta * m * A * a_i * K_i^alpha / w) ^ (1/(1-beta))
  localPrefixOutput P d i =
    (A*a_i) * K_i^alpha * (localPrefixLabor P d i)^beta.

For the pinned stationary primitive exponents alpha=2/5, beta=1/2
and STRICTLY POSITIVE economic inputs A,a_i,K_i,m,w, their exact
off-root identity is
  Y_i = (m/(2*w)) * (A*a_i)^2 * K_i^(4/5).

All manipulations below are exact real rpow identities, not
linearizations or an auxiliary Python production equation.

The aggregate version retains both original masses P.mass i.
There is no false assumption of exogenous labor; labor is substituted
from its actual intratemporal choice formula.

The specialization to date-zero and date-one log coordinates and
Fréchet differentiation of aggregate output remain future tasks.
-/

namespace Ventura26LiquidityAllocation
namespace CurrentSourceFirmOutputClosedForm

open CurrentSourceFullFDeriv
open scoped Topology BigOperators

/-- Exact algebraic Cobb-Douglas output from endogenous optimal
labor at beta=1/2, under positive SOURCE economic inputs. -/
theorem original_half_labor_output_closed_form
    (aggregate productivity capital price wage : ℝ)
    (hA : 0 < aggregate) (hProd : 0 < productivity)
    (hK : 0 < capital) (hPrice : 0 < price) (hWage : 0 < wage) :
    operatingOutput (aggregate * productivity) capital
      (((1/2 : ℝ) * price * aggregate * productivity *
          capital ^ (2/5 : ℝ) / wage) ^
        (1 / (1 - (1/2 : ℝ))))
      (2/5 : ℝ) (1/2 : ℝ) =
    (price / (2*wage)) * (aggregate * productivity)^2 *
      capital ^ (4/5 : ℝ) := by
  have hKpow : 0 < capital ^ (2/5 : ℝ) :=
    Real.rpow_pos_of_pos hK _
  have hInput : 0 < (1/2 : ℝ) * price * aggregate *
      productivity * capital ^ (2/5 : ℝ) / wage := by
    positivity
  have hRoot :
      (((1/2 : ℝ) * price * aggregate *
        productivity * capital ^ (2/5 : ℝ) / wage)^2) ^
        (1/2 : ℝ) =
        ((1/2 : ℝ) * price * aggregate *
          productivity * capital ^ (2/5 : ℝ) / wage) := by
    simpa only [one_div] using
      (Real.pow_rpow_inv_natCast
        (x := (1/2 : ℝ) * price * aggregate *
          productivity * capital ^ (2/5 : ℝ) / wage)
        (n := 2) hInput.le (by norm_num))
  have hPowers :
      capital ^ (4/5 : ℝ) =
        capital ^ (2/5 : ℝ) * capital ^ (2/5 : ℝ) := by
    calc
      capital ^ (4/5 : ℝ) =
          capital ^ ((2/5 : ℝ) + (2/5 : ℝ)) := by norm_num
      _ = _ := Real.rpow_add hK (2/5 : ℝ) (2/5 : ℝ)
  change
    (aggregate * productivity) * capital ^ (2/5 : ℝ) *
      ((((1/2 : ℝ) * price * aggregate * productivity *
        capital ^ (2/5 : ℝ) / wage) ^
        (1 / (1 - (1/2 : ℝ)))) ^ (1/2 : ℝ)) =
      (price / (2*wage)) * (aggregate * productivity)^2 *
        capital ^ (4/5 : ℝ)
  rw [show (1 / (1 - (1/2 : ℝ))) = (2 : ℝ) by norm_num,
      Real.rpow_two, hRoot, hPowers]
  field_simp [ne_of_gt hWage] <;> ring

#print axioms original_half_labor_output_closed_form

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- The TRUE SOURCE firm output uses exactly the economic labor
substitution from EconomicModel and no other production proxy. -/
theorem original_SOURCE_localFirm_output_closed_form
    (P : Primitives S) (d : LocalPrefixDateData) (i : FirmType)
    (hAlpha : P.alpha = 2/5) (hBeta : P.beta = 1/2)
    (hAggregate : 0 < d.currentAggregateProductivity)
    (hProd : 0 < P.productivity i)
    (hCapital : 0 < d.currentCapital i)
    (hPrice : 0 < d.controls.inputPrice)
    (hWage : 0 < d.controls.wage) :
    localPrefixOutput P d i =
      (d.controls.inputPrice / (2 * d.controls.wage)) *
        (d.currentAggregateProductivity * P.productivity i)^2 *
          (d.currentCapital i)^(4/5 : ℝ) := by
  change operatingOutput
      (d.currentAggregateProductivity * P.productivity i)
      (d.currentCapital i)
      ((P.beta * d.controls.inputPrice *
          d.currentAggregateProductivity * P.productivity i *
          (d.currentCapital i)^P.alpha / d.controls.wage) ^
        (1 / (1-P.beta))) P.alpha P.beta = _
  rw [hAlpha, hBeta]
  exact original_half_labor_output_closed_form
    d.currentAggregateProductivity (P.productivity i)
    (d.currentCapital i) d.controls.inputPrice d.controls.wage
    hAggregate hProd hCapital hPrice hWage

#print axioms original_SOURCE_localFirm_output_closed_form

/-- Aggregate SOURCE output is a weighted sum with the ORIGINAL
mass parameters, and still responds endogenously to labor choice. -/
theorem original_SOURCE_aggregate_output_closed_form
    (P : Primitives S) (d : LocalPrefixDateData)
    (hAlpha : P.alpha = 2/5) (hBeta : P.beta = 1/2)
    (hAggregate : 0 < d.currentAggregateProductivity)
    (hProd : ∀ i : FirmType, 0 < P.productivity i)
    (hCapital : ∀ i : FirmType, 0 < d.currentCapital i)
    (hPrice : 0 < d.controls.inputPrice)
    (hWage : 0 < d.controls.wage) :
    localPrefixAggregateOutput P d =
      (d.controls.inputPrice / (2 * d.controls.wage)) *
        (P.mass .H *
            (d.currentAggregateProductivity * P.productivity .H)^2 *
              (d.currentCapital .H)^(4/5 : ℝ) +
         P.mass .L *
            (d.currentAggregateProductivity * P.productivity .L)^2 *
              (d.currentCapital .L)^(4/5 : ℝ)) := by
  unfold localPrefixAggregateOutput
  rw [sum_firmType_eq_H_add_L]
  rw [original_SOURCE_localFirm_output_closed_form P d .H
      hAlpha hBeta hAggregate (hProd .H) (hCapital .H) hPrice hWage,
      original_SOURCE_localFirm_output_closed_form P d .L
      hAlpha hBeta hAggregate (hProd .L) (hCapital .L) hPrice hWage]
  ring

#print axioms original_SOURCE_aggregate_output_closed_form

end CurrentSourceFirmOutputClosedForm
end Ventura26LiquidityAllocation
