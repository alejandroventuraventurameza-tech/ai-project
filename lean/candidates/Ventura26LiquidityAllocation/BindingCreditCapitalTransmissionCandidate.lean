import Ventura26LiquidityAllocation.EconomicModel

/-!
# Binding credit, internal funds, and capital: exact algebra

This candidate isolates a necessary, source-shaped transmission identity:
a binding collateral contract `R * b = gamma * kNext` and the entrepreneurial
budget `q * kNext = X + b`, where `X = N - c`.

No equilibrium, stochastic path, or empirical calibration is assumed.
A lower loan rate raises borrowing capacity if internal funds, q, and gamma
are held fixed; it need not raise chosen capital if internal funds change.
The numerical witness below is a logical counterexample, not an IRF.

The active branches S/B and the date-zero source model are not changed.
-/

namespace Ventura26LiquidityAllocation
namespace ProposedBindingCreditCapitalTransmission

/-- Price of a unit of next-period capital net of collateralized financing. -/
noncomputable def effectivePrice (q gamma R : ℝ) : ℝ :=
  q - gamma / R

/-- Capital funded from internal resources when collateral is binding. -/
noncomputable def bindingCapital (X q gamma R : ℝ) : ℝ :=
  X / effectivePrice q gamma R

/-- Loan principal consistent with the binding repayment ceiling. -/
noncomputable def bindingLoan (X q gamma R : ℝ) : ℝ :=
  gamma * bindingCapital X q gamma R / R

/-- Binding repayment determines principal without any claim of optimality. -/
theorem loan_from_binding
    {gamma R k b : ℝ} (hR : R ≠ 0)
    (hcollateral : R * b = gamma * k) :
    b = gamma * k / R := by
  apply (eq_div_iff hR).2
  nlinarith only [hcollateral]

/-- Derive, rather than posit, the binding capital formula from the budget
and repayment equality. The effective price must be nonzero. -/
theorem capital_from_budget_and_binding
    {X q gamma R k b : ℝ}
    (hR : R ≠ 0) (hD : effectivePrice q gamma R ≠ 0)
    (hbudget : q * k = X + b)
    (hcollateral : R * b = gamma * k) :
    k = bindingCapital X q gamma R := by
  have hb := loan_from_binding hR hcollateral
  rw [hb] at hbudget
  unfold bindingCapital
  apply (eq_div_iff hD).2
  dsimp [effectivePrice]
  calc
    k * (q - gamma / R) = q * k - gamma * k / R := by ring
    _ = X := by linarith only [hbudget]

/-- Holding collateral value gamma and asset price q fixed, a lower
strictly positive gross loan rate reduces the effective price. -/
theorem rate_cut_reduces_effective_price
    (q gamma R0 R1 : ℝ)
    (hgamma : 0 < gamma) (hR1 : 0 < R1) (hcut : R1 < R0) :
    effectivePrice q gamma R1 < effectivePrice q gamma R0 := by
  have hR0 : 0 < R0 := lt_trans hR1 hcut
  have hfrac : gamma / R0 < gamma / R1 := by
    apply (div_lt_div_iff₀ hR0 hR1).2
    exact mul_lt_mul_of_pos_left hcut hgamma
  unfold effectivePrice
  linarith only [hfrac]

/-- With the same positive internal funds X and positive effective prices,
a loan-rate cut strictly increases the financially feasible capital scale. -/
theorem rate_cut_raises_capacity_given_same_funds
    (X q gamma R0 R1 : ℝ)
    (hX : 0 < X) (hgamma : 0 < gamma)
    (hR1 : 0 < R1) (hcut : R1 < R0)
    (hD1 : 0 < effectivePrice q gamma R1) :
    bindingCapital X q gamma R0 < bindingCapital X q gamma R1 := by
  have hD := rate_cut_reduces_effective_price q gamma R0 R1 hgamma hR1 hcut
  have hD0 : 0 < effectivePrice q gamma R0 := lt_trans hD1 hD
  unfold bindingCapital
  apply (div_lt_div_iff₀ hD0 hD1).2
  exact mul_lt_mul_of_pos_left hD hX

/-- Exact necessary and sufficient threshold for declining capital:
X1/D1 < X0/D0 precisely when X1*D0 < X0*D1 (for D0,D1 > 0).
No comparative-static sign is smuggled in as an assumption. -/
theorem capital_falls_iff_cash_threshold
    {X0 X1 D0 D1 : ℝ} (hD0 : 0 < D0) (hD1 : 0 < D1) :
    X1 / D1 < X0 / D0 ↔ X1 * D0 < X0 * D1 := by
  exact div_lt_div_iff₀ hD1 hD0

/-- Credit may rise even if capital falls: the exact credit condition
at fixed gamma > 0 is k0*R1 < k1*R0. -/
theorem credit_rises_iff_capital_rate_threshold
    {gamma k0 k1 R0 R1 : ℝ}
    (hgamma : 0 < gamma) (hR0 : 0 < R0) (hR1 : 0 < R1) :
    gamma * k0 / R0 < gamma * k1 / R1 ↔ k0 * R1 < k1 * R0 := by
  calc
    gamma * k0 / R0 < gamma * k1 / R1
        ↔ (gamma * k0) * R1 < (gamma * k1) * R0 :=
          div_lt_div_iff₀ hR0 hR1
    _ ↔ gamma * (k0 * R1) < gamma * (k1 * R0) := by
          simp only [mul_assoc]
    _ ↔ k0 * R1 < k1 * R0 := by
          constructor
          · intro h
            by_contra hc
            have hle : k1 * R0 ≤ k0 * R1 := le_of_not_gt hc
            have hm := mul_le_mul_of_nonneg_left hle hgamma.le
            exact (not_lt_of_ge hm) h
          · intro h
            exact mul_lt_mul_of_pos_left h hgamma

/-- Concrete, exact rational witness: R falls 2 -> 3/2 and internal funds
fall 3/4 -> 3/5. Capital falls 1 -> 9/10 while credit rises 1/4 -> 3/10.
These figures illustrate logical coexistence, NOT calibrated magnitudes. -/
theorem lower_rate_more_credit_less_capital_witness :
    let q : ℝ := 1
    let gamma : ℝ := 1 / 2
    let R0 : ℝ := 2
    let R1 : ℝ := 3 / 2
    let X0 : ℝ := 3 / 4
    let X1 : ℝ := 3 / 5
    0 < X1 ∧ R1 < R0 ∧
      bindingCapital X1 q gamma R1 < bindingCapital X0 q gamma R0 ∧
      bindingLoan X0 q gamma R0 < bindingLoan X1 q gamma R1 := by
  dsimp [bindingCapital, bindingLoan, effectivePrice]
  norm_num

#print axioms capital_from_budget_and_binding
#print axioms rate_cut_raises_capacity_given_same_funds
#print axioms capital_falls_iff_cash_threshold
#print axioms credit_rises_iff_capital_rate_threshold
#print axioms lower_rate_more_credit_less_capital_witness

end ProposedBindingCreditCapitalTransmission
end Ventura26LiquidityAllocation
