import Ventura26LiquidityAllocation.StationaryHouseholdOptimalityCandidate
import Mathlib.Analysis.MeanInequalities

/-!
# Fundamentos de comparacion de H y L: PROPUESTA SIN COMPILAR

Proyecto: alejandroventuraventurameza-tech/ai-project.
Rama: work/chat-continuity.
Commit: 16e24fe828a5a0002ef13bb82bae9e295f190f86.
Base AppliedModelingLib: 194edcc95df74806a39b961d10dedddc6e730cce.
Lean previsto: leanprover/lean4:v4.30.0-rc2.
Mathlib: 5450b53e5ddc75d46418fabb605edbf36bd0beb6.
Destino propuesto: papers/Ventura26LiquidityAllocation/StationaryFirmComparisonFoundationCandidate.lean.
SHA256 de StationaryHouseholdOptimalityCandidate.lean utilizado:
e95df810ef829f96fd702ecb12c707d1710d01bd1731fc61acdcca3a4d9c9fb8

Todos los modulos propuestos de la cadena siguen SIN COMPILAR. Las
interfaces y las demostraciones se revisaron matematicamente y por lectura.
No se ejecutaron Lean ni simulaciones. No se acredita elaboracion, kernel,
inspeccion de axiomas ni aprobacion de la auditoria semantica.

Argumento matematico previo al codigo:
1. Se conserva todo FirmFeasible: c>0 y k,l,b,d>=0, con k=0 y financiacion
   simultanea incluidos. La cara es F=R*b-R_D*d; la garantia se impone
   sobre R*b, para cada hijo soportado. No se adopta el dominio signed.
2. A=q*k-b+d es la cartera literal de firmTerminalTerm. El presupuesto
   actual es c+A=wealth. La riqueza inicial usa K_i y F_i heredados;
   la sucesora usa k_t, l_(t+1) y F_t. Se derivan diferencias exactas.
3. La produccion alternativa se normaliza por K_i,L_i positivos del
   candidato. AM-GM con pesos 2/5,1/2,1/10 da un soporte afín valido
   para todo k,l>=0. Se cancelan solo potencias del candidato, nunca
   controles alternativos. Las identidades marginales dan
   pi_i(k,l)<=profit_i+userCost_i*(k-K_i).
4. Con betaE=24/25, R_D=100/99 y mu=1/R-betaE>0, la diferencia entre
   variacion de cartera y retorno descontado es exactamente
   mu*(theta_i*J*k-R*b)+d/33. Es no negativa por colateral y deposito.
5. R*q-theta_i*J=R*q*financingFraction_i>0. La igualdad
   R*A=(R*q-theta_i*J)*k+(theta_i*J*k-R*b)+R*d demuestra A>=0.

ALCANCE: soporte productivo global, identidades presupuestarias, soporte
financiero y cartera no negativa. No se reciben concavidad, optimalidad,
TVC alternativa, capital positivo alternativo o cotas uniformes como premisas.
G queda simbolico. Se conserva el padre con ambas garantias activas y las
ramas macroeconomicas S y B; no se construye aqui el prefijo perturbado.
-/

namespace Ventura26LiquidityAllocation
namespace ProposedStationaryFirmOptimality

/-! ## Dominio bruto y momento temporal de los presupuestos -/

open ProposedStationaryRealScale
open ProposedStationaryPrimitives
open ProposedStationaryInheritedState
open ProposedStationaryLiteralAccounts
open ProposedStationaryPrivateFeasibility
open ProposedStationaryHouseholdOptimality

noncomputable def firmPathConsumption (p : FirmPlan LocalBridgePhase) (t : ℕ) : ℝ :=
  p.consumption t (localBridgeHistory t)

noncomputable def firmPathCapital (p : FirmPlan LocalBridgePhase) (t : ℕ) : ℝ :=
  p.capital t (localBridgeHistory t)

noncomputable def firmPathLabor (p : FirmPlan LocalBridgePhase) (t : ℕ) : ℝ :=
  p.labor t (localBridgeHistory t)

noncomputable def firmPathLoan (p : FirmPlan LocalBridgePhase) (t : ℕ) : ℝ :=
  p.loan t (localBridgeHistory t)

noncomputable def firmPathDeposit (p : FirmPlan LocalBridgePhase) (t : ℕ) : ℝ :=
  p.deposit t (localBridgeHistory t)

noncomputable def firmPathFace (p : FirmPlan LocalBridgePhase) (t : ℕ) : ℝ :=
  p.face t (localBridgeHistory t)

noncomputable def firmPathWealth (p : FirmPlan LocalBridgePhase) (t : ℕ) : ℝ :=
  p.wealth t (localBridgeHistory t)

noncomputable def firmPathAssets (p : FirmPlan LocalBridgePhase) (t : ℕ) : ℝ :=
  capitalPrice * firmPathCapital p t - firmPathLoan p t + firmPathDeposit p t

noncomputable def parentFirmAssets (i : FirmType) : ℝ :=
  capitalPrice * capital i - loan i

noncomputable def firmAssetGap (i : FirmType)
    (p : FirmPlan LocalBridgePhase) (t : ℕ) : ℝ :=
  firmPathAssets p t - parentFirmAssets i

noncomputable def firmProfit (i : FirmType) (k ell : ℝ) : ℝ :=
  operatingProfit (5 / 6) (technology i) k ell (2 / 5) (1 / 2) wage

/-- Dominio literal de FirmFeasible, incluido el borde de capital cero. -/
theorem firm_path_domain (G : ℝ) (i : FirmType) (p : FirmPlan LocalBridgePhase)
    (hp : FirmFeasible (primitives G) (inheritedState G)
      (parentAllocation G) i p) (t : ℕ) :
    0 < firmPathConsumption p t ∧ 0 ≤ firmPathCapital p t ∧
      0 ≤ firmPathLabor p t ∧ 0 ≤ firmPathLoan p t ∧ 0 ≤ firmPathDeposit p t := by
  exact hp.1 t (localBridgeHistory t) (localBridgeHistory_admissible G t)

/-- La cara nominal conserva tanto el prestamo como el deposito bruto. -/
theorem firm_path_face (G : ℝ) (i : FirmType) (p : FirmPlan LocalBridgePhase)
    (hp : FirmFeasible (primitives G) (inheritedState G)
      (parentAllocation G) i p) (t : ℕ) :
    firmPathFace p t = ProposedStationaryBank.loanRate * firmPathLoan p t -
      ProposedStationaryBank.depositRate * firmPathDeposit p t := by
  have hface := hp.2.1 t (localBridgeHistory t) (localBridgeHistory_admissible G t)
  simpa only [firmPathFace, firmPathLoan, firmPathDeposit, parent_loanRate,
    parent_depositRate, signedFace] using hface

/-- Reagrupacion exacta del presupuesto actual, sin eliminar depositos. -/
theorem firm_path_budget (G : ℝ) (i : FirmType) (p : FirmPlan LocalBridgePhase)
    (hp : FirmFeasible (primitives G) (inheritedState G)
      (parentAllocation G) i p) (t : ℕ) :
    firmPathConsumption p t + firmPathAssets p t = firmPathWealth p t := by
  have hbudget := hp.2.2.1 t (localBridgeHistory t)
    (localBridgeHistory_admissible G t)
  simp only [parent_capitalPrice] at hbudget
  unfold firmPathConsumption firmPathAssets firmPathCapital firmPathLoan
    firmPathDeposit firmPathWealth
  linear_combination hbudget

/-- El hijo canonico es soportado. La prueba usa los pesos uno conservados,
no una hipotesis adicional sobre el plan alternativo. -/
private theorem canonical_transition_eq_one (G : ℝ) (t : ℕ) :
    (primitives G).tree.transition (currentState (localBridgeHistory t))
      (if t = 0 then LocalBridgePhase.dateOne else LocalBridgePhase.recurrent) = 1 := by
  change localBridgeTree.transition (currentState (localBridgeHistory t))
    (if t = 0 then LocalBridgePhase.dateOne else LocalBridgePhase.recurrent) = 1
  have hweight := localBridgeHistory_weight_one (t + 1)
  rw [FiniteMarkovTree.historyWeight, localBridgeHistory_previous_succ,
    localBridgeHistory_weight_one, one_mul, localBridgeHistory_current_succ] at hweight
  exact hweight

/-- Garantia sobre el prestamo bruto, tal como aparece en FirmFeasible. -/
theorem firm_path_collateral (G : ℝ) (i : FirmType) (p : FirmPlan LocalBridgePhase)
    (hp : FirmFeasible (primitives G) (inheritedState G)
      (parentAllocation G) i p) (t : ℕ) :
    ProposedStationaryBank.loanRate * firmPathLoan p t ≤
      pledgeability i * liquidationValue * firmPathCapital p t := by
  have hpossible : 0 < (primitives G).tree.transition
      (currentState (localBridgeHistory t))
      (if t = 0 then LocalBridgePhase.dateOne else LocalBridgePhase.recurrent) := by
    rw [canonical_transition_eq_one G t]
    norm_num
  have hcollateral := hp.2.2.2.1 t (localBridgeHistory t)
    (localBridgeHistory_admissible G t)
    (if t = 0 then LocalBridgePhase.dateOne else LocalBridgePhase.recurrent) hpossible
  simp only [parent_loanRate, parent_inflation, parent_capitalPrice] at hcollateral
  change ProposedStationaryBank.loanRate * firmPathLoan p t ≤
    pledgeability i * (1 - (1 / 40 : ℝ)) * (1 * capitalPrice) *
      firmPathCapital p t at hcollateral
  calc
    ProposedStationaryBank.loanRate * firmPathLoan p t ≤
        pledgeability i * (1 - (1 / 40 : ℝ)) * (1 * capitalPrice) *
          firmPathCapital p t := hcollateral
    _ = pledgeability i * liquidationValue * firmPathCapital p t := by
      unfold liquidationValue
      ring

/-- Escritura neta exacta de la garantia gross. El deposito no desaparece. -/
theorem firm_path_collateral_net (G : ℝ) (i : FirmType)
    (p : FirmPlan LocalBridgePhase)
    (hp : FirmFeasible (primitives G) (inheritedState G)
      (parentAllocation G) i p) (t : ℕ) :
    firmPathFace p t + ProposedStationaryBank.depositRate * firmPathDeposit p t ≤
      pledgeability i * liquidationValue * firmPathCapital p t := by
  calc
    firmPathFace p t + ProposedStationaryBank.depositRate * firmPathDeposit p t =
        ProposedStationaryBank.loanRate * firmPathLoan p t := by
      rw [firm_path_face G i p hp t]
      ring
    _ ≤ pledgeability i * liquidationValue * firmPathCapital p t :=
      firm_path_collateral G i p hp t

private theorem stationary_liquidation_factor :
    capitalPrice * (1 - (1 / 40 : ℝ)) = liquidationValue := by
  unfold liquidationValue
  ring

/-- Fecha cero: k_i y F_i son heredados; solo el trabajo es elegido en
el beneficio corriente de la alternativa. k_0 financiara la fecha siguiente. -/
theorem firm_path_wealth_zero (G : ℝ) (i : FirmType) (p : FirmPlan LocalBridgePhase)
    (hp : FirmFeasible (primitives G) (inheritedState G)
      (parentAllocation G) i p) :
    firmPathWealth p 0 = firmProfit i (capital i) (firmPathLabor p 0) +
      liquidationValue * capital i - firmFace i := by
  have hwealth := hp.2.2.2.2.1 (localBridgeHistory 0)
    (localBridgeHistory_admissible G 0)
  simp only [parent_inputPrice, parent_wage, parent_capitalPrice,
    parent_inflation] at hwealth
  change p.wealth 0 (localBridgeHistory 0) =
    operatingProfit (5 / 6) (1 * technology i) (capital i)
      (p.labor 0 (localBridgeHistory 0)) (2 / 5) (1 / 2) wage +
      capitalPrice * (1 - (1 / 40 : ℝ)) * capital i -
      realRepayment (firmFace i) 1 at hwealth
  simp only [one_mul, realRepayment, div_one] at hwealth
  rw [stationary_liquidation_factor] at hwealth
  exact hwealth

/-- Sucesor: beneficio y liquidacion usan k_t; el repago usa F_t completo.
La eleccion de trabajo de la fecha t+1 se mantiene independiente de l_t. -/
theorem firm_path_wealth_succ (G : ℝ) (i : FirmType) (p : FirmPlan LocalBridgePhase)
    (hp : FirmFeasible (primitives G) (inheritedState G)
      (parentAllocation G) i p) (t : ℕ) :
    firmPathWealth p (t + 1) =
      firmProfit i (firmPathCapital p t) (firmPathLabor p (t + 1)) +
        liquidationValue * firmPathCapital p t - firmPathFace p t := by
  have hchild := (localBridgeHistory_succ t).symm
  have hadmissible : FirmHistoryAdmissible (primitives G) (t + 1)
      (childHistory (localBridgeHistory t)
        (if t = 0 then LocalBridgePhase.dateOne else LocalBridgePhase.recurrent)) := by
    rw [hchild]
    exact localBridgeHistory_admissible G (t + 1)
  have hwealth := hp.2.2.2.2.2 t (localBridgeHistory t)
    (if t = 0 then LocalBridgePhase.dateOne else LocalBridgePhase.recurrent) hadmissible
  rw [hchild] at hwealth
  simp only [parent_inputPrice, parent_wage, parent_capitalPrice,
    parent_inflation] at hwealth
  change p.wealth (t + 1) (localBridgeHistory (t + 1)) =
    operatingProfit (5 / 6) (1 * technology i)
      (p.capital t (localBridgeHistory t))
      (p.labor (t + 1) (localBridgeHistory (t + 1))) (2 / 5) (1 / 2) wage +
      capitalPrice * (1 - (1 / 40 : ℝ)) * p.capital t (localBridgeHistory t) -
      realRepayment (p.face t (localBridgeHistory t)) 1 at hwealth
  simp only [one_mul, realRepayment, div_one] at hwealth
  rw [stationary_liquidation_factor] at hwealth
  exact hwealth

/-- La formula de beneficio del padre ya se identifico con la produccion
literal. No se repite ni se asume aqui la tangente de produccion. -/
@[simp] theorem firmProfit_at_parent (i : FirmType) :
    firmProfit i (capital i) (labor i) = profit i :=
  firm_operatingProfit_eq i

@[simp] theorem parent_firmPathConsumption (G : ℝ) (i : FirmType) (t : ℕ) :
    firmPathConsumption (firmPlanOfAllocation (parentAllocation G) i) t =
      firmConsumption i := by
  simp only [firmPathConsumption, firmPlanOfAllocation, parent_firmConsumption]

@[simp] theorem parent_firmPathCapital (G : ℝ) (i : FirmType) (t : ℕ) :
    firmPathCapital (firmPlanOfAllocation (parentAllocation G) i) t = capital i := by
  simp only [firmPathCapital, firmPlanOfAllocation, parent_capital]

@[simp] theorem parent_firmPathLabor (G : ℝ) (i : FirmType) (t : ℕ) :
    firmPathLabor (firmPlanOfAllocation (parentAllocation G) i) t = labor i := by
  simp only [firmPathLabor, firmPlanOfAllocation, parent_labor]

@[simp] theorem parent_firmPathLoan (G : ℝ) (i : FirmType) (t : ℕ) :
    firmPathLoan (firmPlanOfAllocation (parentAllocation G) i) t = loan i := by
  simp only [firmPathLoan, firmPlanOfAllocation, parent_loan]

@[simp] theorem parent_firmPathDeposit (G : ℝ) (i : FirmType) (t : ℕ) :
    firmPathDeposit (firmPlanOfAllocation (parentAllocation G) i) t = 0 := by
  simp only [firmPathDeposit, firmPlanOfAllocation, parent_firmDeposit]

@[simp] theorem parent_firmPathFace (G : ℝ) (i : FirmType) (t : ℕ) :
    firmPathFace (firmPlanOfAllocation (parentAllocation G) i) t = firmFace i := by
  simp only [firmPathFace, firmPlanOfAllocation, parent_firmFace]

@[simp] theorem parent_firmPathWealth (G : ℝ) (i : FirmType) (t : ℕ) :
    firmPathWealth (firmPlanOfAllocation (parentAllocation G) i) t = wealth i := by
  simp only [firmPathWealth, firmPlanOfAllocation, parent_firmWealth]

@[simp] theorem parent_firmPathAssets (G : ℝ) (i : FirmType) (t : ℕ) :
    firmPathAssets (firmPlanOfAllocation (parentAllocation G) i) t =
      parentFirmAssets i := by
  simp only [firmPathAssets, parent_firmPathCapital, parent_firmPathLoan,
    parent_firmPathDeposit, parentFirmAssets, add_zero]

@[simp] theorem parent_firmAssetGap_zero (G : ℝ) (i : FirmType) (t : ℕ) :
    firmAssetGap i (firmPlanOfAllocation (parentAllocation G) i) t = 0 := by
  simp only [firmAssetGap, parent_firmPathAssets, sub_self]

/-- Presupuesto del padre en las mismas unidades que A_t. Es una
reagrupacion del presupuesto empresarial ya demostrado. -/
theorem parentFirmAssets_budget (i : FirmType) :
    firmConsumption i + parentFirmAssets i =
      profit i + liquidationValue * capital i - firmFace i := by
  have hbudget := firm_budget_identity i
  change firmConsumption i + capitalPrice * capital i =
    (profit i + liquidationValue * capital i - firmFace i) + loan i at hbudget
  unfold parentFirmAssets
  linear_combination hbudget

/-- Diferencia inicial exacta. El capital y la cara heredados se cancelan. -/
theorem firm_budget_difference_zero (G : ℝ) (i : FirmType)
    (p : FirmPlan LocalBridgePhase)
    (hp : FirmFeasible (primitives G) (inheritedState G)
      (parentAllocation G) i p) :
    firmPathConsumption p 0 - firmConsumption i + firmAssetGap i p 0 =
      firmProfit i (capital i) (firmPathLabor p 0) - profit i := by
  have hbudget := firm_path_budget G i p hp 0
  have hwealth := firm_path_wealth_zero G i p hp
  have hparent := parentFirmAssets_budget i
  unfold firmAssetGap
  linear_combination hbudget + hwealth - hparent

/-- Diferencia sucesora con la cara nominal completa y el timing fuente. -/
theorem firm_budget_difference_succ (G : ℝ) (i : FirmType)
    (p : FirmPlan LocalBridgePhase)
    (hp : FirmFeasible (primitives G) (inheritedState G)
      (parentAllocation G) i p) (t : ℕ) :
    firmPathConsumption p (t + 1) - firmConsumption i + firmAssetGap i p (t + 1) =
      firmProfit i (firmPathCapital p t) (firmPathLabor p (t + 1)) - profit i +
        liquidationValue * (firmPathCapital p t - capital i) -
        (firmPathFace p t - firmFace i) := by
  have hbudget := firm_path_budget G i p hp (t + 1)
  have hwealth := firm_path_wealth_succ G i p hp t
  have hparent := parentFirmAssets_budget i
  unfold firmAssetGap
  linear_combination hbudget + hwealth - hparent

/-- Version gross de la misma diferencia. La alternativa puede mantener
prestamos y depositos a la vez; solamente el padre tiene deposito cero. -/
theorem firm_budget_difference_succ_gross (G : ℝ) (i : FirmType)
    (p : FirmPlan LocalBridgePhase)
    (hp : FirmFeasible (primitives G) (inheritedState G)
      (parentAllocation G) i p) (t : ℕ) :
    firmPathConsumption p (t + 1) - firmConsumption i + firmAssetGap i p (t + 1) =
      firmProfit i (firmPathCapital p t) (firmPathLabor p (t + 1)) - profit i +
        liquidationValue * (firmPathCapital p t - capital i) -
        ProposedStationaryBank.loanRate * (firmPathLoan p t - loan i) +
        ProposedStationaryBank.depositRate * firmPathDeposit p t := by
  calc
    _ = firmProfit i (firmPathCapital p t) (firmPathLabor p (t + 1)) - profit i +
        liquidationValue * (firmPathCapital p t - capital i) -
        (firmPathFace p t - firmFace i) := firm_budget_difference_succ G i p hp t
    _ = _ := by
      rw [firm_path_face G i p hp t, ← firm_loan_face_identity i]
      ring


/-! ## Soporte afín global de la produccion, incluidas las esquinas -/

open ProposedStationaryRealScale
open ProposedStationaryProductionBridge

/-- AM-GM ponderada con el tercer factor constante. La holgura de los
exponentes, 1-2/5-1/2=1/10, se conserva en el termino constante. -/
theorem normalized_cobbDouglas_support
    (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    x ^ (2 / 5 : ℝ) * y ^ (1 / 2 : ℝ) ≤
      (2 / 5 : ℝ) * x + (1 / 2 : ℝ) * y + 1 / 10 := by
  have h := Real.geom_mean_le_arith_mean3_weighted
    (w₁ := (2 / 5 : ℝ)) (w₂ := (1 / 2 : ℝ)) (w₃ := (1 / 10 : ℝ))
    (p₁ := x) (p₂ := y) (p₃ := (1 : ℝ))
    (by norm_num) (by norm_num) (by norm_num)
    hx hy (by norm_num) (by norm_num)
  simpa only [Real.one_rpow, mul_one] using h

/-- Factorizacion relativa al punto positivo. Los denominadores que se
cancelan son potencias de K,L, no potencias de los controles alternativos. -/
theorem stationary_valuedOutput_factorization
    (i : FirmType) (k ell : ℝ) (hk : 0 ≤ k) (hell : 0 ≤ ell) :
    (5 / 6 : ℝ) * (technology i * k ^ (2 / 5 : ℝ) * ell ^ (1 / 2 : ℝ)) =
      ((5 / 6 : ℝ) * output i) *
        ((k / capital i) ^ (2 / 5 : ℝ) * (ell / labor i) ^ (1 / 2 : ℝ)) := by
  have hcapitalPow : capital i ^ (2 / 5 : ℝ) ≠ 0 :=
    (Real.rpow_pos_of_pos (capital_pos i) (2 / 5 : ℝ)).ne'
  have hlaborPow : labor i ^ (1 / 2 : ℝ) ≠ 0 :=
    (Real.rpow_pos_of_pos (labor_pos i) (1 / 2 : ℝ)).ne'
  rw [← production_identity i,
    Real.div_rpow hk (capital_pos i).le (2 / 5 : ℝ),
    Real.div_rpow hell (labor_pos i).le (1 / 2 : ℝ)]
  field_simp [hcapitalPow, hlaborPow] <;> ring

/-- Coeficiente del capital en el soporte, identificado con userCost. -/
theorem stationary_capital_revenue_coefficient (i : FirmType) :
    (((5 / 6 : ℝ) * output i) * (2 / 5 : ℝ)) / capital i = userCost i := by
  unfold output
  field_simp [ne_of_gt (capital_pos i)] <;> ring

/-- Coeficiente del trabajo en el soporte, identificado con el salario. -/
theorem stationary_labor_revenue_coefficient (i : FirmType) :
    (((5 / 6 : ℝ) * output i) * (1 / 2 : ℝ)) / labor i = wage := by
  apply (div_eq_iff (ne_of_gt (labor_pos i))).2
  unfold output labor
  field_simp [ne_of_gt wage_pos] <;> ring

theorem stationary_revenue_remainder (i : FirmType) :
    ((5 / 6 : ℝ) * output i) * (1 / 10 : ℝ) =
      profit i - userCost i * capital i := by
  unfold profit output
  ring

/-- El soporte toca al beneficio literal en el punto del candidato. -/
theorem stationary_operatingProfit_at_candidate (i : FirmType) :
    operatingProfit (5 / 6) (technology i) (capital i) (labor i)
      (2 / 5) (1 / 2) wage = profit i := by
  have hlabor := (div_eq_iff (ne_of_gt (labor_pos i))).1
    (stationary_labor_revenue_coefficient i)
  unfold operatingProfit operatingOutput
  rw [production_identity i, ← hlabor]
  unfold profit
  ring

/-- Soporte global de beneficio: cubre capital y trabajo alternativos
no negativos, incluidas ambas esquinas. No presupone concavidad. -/
theorem stationary_operatingProfit_support
    (i : FirmType) (k ell : ℝ) (hk : 0 ≤ k) (hell : 0 ≤ ell) :
    operatingProfit (5 / 6) (technology i) k ell (2 / 5) (1 / 2) wage ≤
      profit i + userCost i * (k - capital i) := by
  have hnormalized := normalized_cobbDouglas_support
    (k / capital i) (ell / labor i)
    (div_nonneg hk (capital_pos i).le) (div_nonneg hell (labor_pos i).le)
  have hvaluedOutput : 0 ≤ (5 / 6 : ℝ) * output i :=
    mul_nonneg (by norm_num) (output_pos i).le
  have hbound := mul_le_mul_of_nonneg_left hnormalized hvaluedOutput
  calc
    operatingProfit (5 / 6) (technology i) k ell (2 / 5) (1 / 2) wage =
        ((5 / 6 : ℝ) * output i) *
          ((k / capital i) ^ (2 / 5 : ℝ) * (ell / labor i) ^ (1 / 2 : ℝ)) -
          wage * ell := by
      unfold operatingProfit operatingOutput
      rw [stationary_valuedOutput_factorization i k ell hk hell]
    _ ≤ ((5 / 6 : ℝ) * output i) *
          ((2 / 5 : ℝ) * (k / capital i) +
            (1 / 2 : ℝ) * (ell / labor i) + 1 / 10) - wage * ell :=
      sub_le_sub_right hbound (wage * ell)
    _ = ((((5 / 6 : ℝ) * output i) * (2 / 5 : ℝ)) / capital i) * k +
          ((((5 / 6 : ℝ) * output i) * (1 / 2 : ℝ)) / labor i) * ell +
          ((5 / 6 : ℝ) * output i) * (1 / 10 : ℝ) - wage * ell := by
      ring
    _ = userCost i * k + wage * ell +
          (profit i - userCost i * capital i) - wage * ell := by
      rw [stationary_capital_revenue_coefficient,
        stationary_labor_revenue_coefficient, stationary_revenue_remainder]
    _ = profit i + userCost i * (k - capital i) := by ring


/-! ## Soporte financiero y cartera terminal no negativa -/

open ProposedStationaryRealScale
open ProposedStationaryProductionBridge

/-- Identidad exacta de los sobrantes financiero y de deposito.
El candidato ya satisface R*loan i=theta_i*J*capital i. -/
theorem firm_financial_slack_identity (i : FirmType) (k b d : ℝ) :
    (capitalPrice * (k - capital i) - (b - loan i) + d) -
      (24 / 25 : ℝ) *
        ((userCost i + liquidationValue) * (k - capital i) -
          ProposedStationaryBank.loanRate * (b - loan i) +
          ProposedStationaryBank.depositRate * d) =
      collateralMultiplier *
        (pledgeability i * liquidationValue * k -
          ProposedStationaryBank.loanRate * b) + (1 / 33 : ℝ) * d := by
  simp only [userCost, liquidationValue, collateralMultiplier, loan, firmFace,
    ProposedStationaryBank.depositRate]
  field_simp [ne_of_gt loanRate_pos] <;> ring

/-- Soporte financiero para todo prestamo y deposito admitidos por el
colateral bruto. No se presupone exclusividad entre ambos instrumentos. -/
theorem firm_financial_support (i : FirmType) (k b d : ℝ)
    (hcollateral : ProposedStationaryBank.loanRate * b ≤
      pledgeability i * liquidationValue * k)
    (hd : 0 ≤ d) :
    (24 / 25 : ℝ) *
        ((userCost i + liquidationValue) * (k - capital i) -
          ProposedStationaryBank.loanRate * (b - loan i) +
          ProposedStationaryBank.depositRate * d) ≤
      capitalPrice * (k - capital i) - (b - loan i) + d := by
  apply sub_nonneg.mp
  rw [firm_financial_slack_identity]
  exact add_nonneg
    (mul_nonneg collateralMultiplier_pos.le (sub_nonneg.mpr hcollateral))
    (mul_nonneg (by norm_num) hd)

/-- Margen de capital financiado positivo, antes de multiplicar por k.
Se reutiliza el signo previamente construido de financingFraction. -/
theorem firm_net_capital_margin_pos (i : FirmType) :
    0 < ProposedStationaryBank.loanRate * capitalPrice -
      pledgeability i * liquidationValue := by
  have hid : ProposedStationaryBank.loanRate * capitalPrice -
      pledgeability i * liquidationValue =
        ProposedStationaryBank.loanRate * capitalPrice * financingFraction i := by
    simp only [financingFraction, liquidationValue]
    field_simp [ne_of_gt loanRate_pos] <;> ring
  rw [hid]
  exact mul_pos (mul_pos loanRate_pos capitalPrice_pos)
    (financing_and_expenditure_pos i).1

/-- La cartera terminal fuente es no negativa tambien cuando k=0.
No se requiere una cota superior de k, b o d ni una TVC alternativa. -/
theorem firm_portfolio_nonneg (i : FirmType) (k b d : ℝ)
    (hk : 0 ≤ k)
    (hcollateral : ProposedStationaryBank.loanRate * b ≤
      pledgeability i * liquidationValue * k)
    (hd : 0 ≤ d) :
    0 ≤ capitalPrice * k - b + d := by
  have hproduct : 0 ≤ ProposedStationaryBank.loanRate *
      (capitalPrice * k - b + d) := by
    calc
      0 ≤ (ProposedStationaryBank.loanRate * capitalPrice -
            pledgeability i * liquidationValue) * k +
          (pledgeability i * liquidationValue * k -
            ProposedStationaryBank.loanRate * b) +
          ProposedStationaryBank.loanRate * d :=
        add_nonneg
          (add_nonneg (mul_nonneg (firm_net_capital_margin_pos i).le hk)
            (sub_nonneg.mpr hcollateral))
          (mul_nonneg loanRate_pos.le hd)
      _ = ProposedStationaryBank.loanRate * (capitalPrice * k - b + d) := by ring
  by_contra hnegative
  have hportfolioNegative : capitalPrice * k - b + d < 0 :=
    lt_of_not_ge hnegative
  have hproductNegative := mul_neg_of_pos_of_neg loanRate_pos hportfolioNegative
  exact (not_lt_of_ge hproduct) hproductNegative

end ProposedStationaryFirmOptimality
end Ventura26LiquidityAllocation
