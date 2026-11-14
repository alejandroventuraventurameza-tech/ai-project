import Ventura26LiquidityAllocation.StationaryObjectiveTerminalCandidate

/-!
# Fundamentos de comparacion del hogar: PROPUESTA SIN COMPILAR

Proyecto: alejandroventuraventurameza-tech/ai-project.
Rama: work/chat-continuity.
Commit: 16e24fe828a5a0002ef13bb82bae9e295f190f86.
Base AppliedModelingLib: 194edcc95df74806a39b961d10dedddc6e730cce.
Lean previsto: leanprover/lean4:v4.30.0-rc2.
Mathlib: 5450b53e5ddc75d46418fabb605edbf36bd0beb6.
Destino propuesto: papers/Ventura26LiquidityAllocation/StationaryHouseholdComparisonFoundationCandidate.lean.
SHA256 de StationaryObjectiveTerminalCandidate.lean utilizado:
1b8f3b288484cc3f4a0b8c85264436210b4f56da3a1612b098f19b10f3dc6b22

Todos los modulos propuestos de la cadena siguen SIN COMPILAR. No se han
ejecutado Lean ni simulaciones. La revision matematica y estatica no
acredita elaboracion, kernel, inspeccion de axiomas o auditoria semantica.

Argumento matematico previo al codigo:
1. El calendario tiene una historia canonica de peso uno en cada fecha.
   Se evalua sobre ella cualquier alternativa, sin volverla estacionaria.
   HouseholdFeasible proporciona c_t>0, l_t>=0, d_t>=0 y b_t>=0.
2. Sea a_t=d_t+b_t y A=D+(G-Mpre). La resta literal de presupuestos da
   (c_0-Cw)-w*(l_0-L)=-(a_0-A) y, para sucesores,
   (c_(t+1)-Cw)-w*(l_(t+1)-L)=R_D*(a_t-A)-(a_(t+1)-A).
   El mismo repago heredado se cancela en fecha cero; todos los ingresos
   de propiedad e impuestos permanecen fijos bajo la desviacion.
3. log(c/C)<=c/C-1 para c,C>0 da la tangente logaritmica. El cuadrado
   (l-L)^2>=0 da la tangente laboral. Con w=C*L, ambas implican
   u(c,l)-u(C,L)<=((c-C)-w*(l-L))/C.
4. La igualdad salarial procede de worker_labor_equation ya construido.
   Las firmas de Real.log_le_sub_one_of_pos, Real.log_div y Real.rpow_two
   se consultaron en el Mathlib fijado antes de proponer estas aplicaciones.

ALCANCE: dominio, diferencias presupuestarias y desigualdad global de utilidad.
No se introduce TVC, acotacion o estacionariedad de alternativas ni se
presupone optimalidad. G permanece simbolico; estas identidades valen
para todo G. La factibilidad economica del candidato se trata por separado
bajo G>=Mpre. Las ramas macroeconomicas S y B se conservan.
-/

namespace Ventura26LiquidityAllocation
namespace ProposedStationaryHouseholdOptimality

/-! ## Trayectorias arbitrarias y diferencias presupuestarias -/

open ProposedStationaryRealScale
open ProposedStationaryPrimitives
open ProposedStationaryInheritedState
open ProposedStationaryLiteralAccounts
open ProposedStationaryPrivateFeasibility

noncomputable def pathConsumption
    (p : HouseholdPlan LocalBridgePhase) (t : ℕ) : ℝ :=
  p.consumption t (localBridgeHistory t)

noncomputable def pathLabor
    (p : HouseholdPlan LocalBridgePhase) (t : ℕ) : ℝ :=
  p.labor t (localBridgeHistory t)

noncomputable def pathAssets
    (p : HouseholdPlan LocalBridgePhase) (t : ℕ) : ℝ :=
  p.deposits t (localBridgeHistory t) + p.bonds t (localBridgeHistory t)

noncomputable def parentAssets (G : ℝ) : ℝ :=
  bankDeposits + (G - reservesPre)

noncomputable def assetGap (G : ℝ)
    (p : HouseholdPlan LocalBridgePhase) (t : ℕ) : ℝ :=
  pathAssets p t - parentAssets G

/-- Cada historia canonica es admisible para la instancia construida. -/
theorem localBridgeHistory_admissible (G : ℝ) (t : ℕ) :
    FirmHistoryAdmissible (primitives G) t (localBridgeHistory t) := by
  change 0 < localBridgeTree.historyWeight t (localBridgeHistory t)
  rw [localBridgeHistory_weight_one]
  norm_num

/-- Compatibilidad exacta con el hijo utilizado en HouseholdFeasible. -/
theorem localBridgeHistory_succ (t : ℕ) :
    localBridgeHistory (t + 1) = childHistory (localBridgeHistory t)
      (if t = 0 then LocalBridgePhase.dateOne else LocalBridgePhase.recurrent) :=
  rfl

/-- No negatividad de los activos de toda alternativa factible. No se
introduce ninguna condicion terminal o cota superior de sus tenencias. -/
theorem path_domain (G : ℝ) (p : HouseholdPlan LocalBridgePhase)
    (hp : HouseholdFeasible (primitives G) (inheritedState G)
      (parentAllocation G) p) (t : ℕ) :
    0 < pathConsumption p t ∧ 0 ≤ pathLabor p t ∧ 0 ≤ pathAssets p t := by
  rcases hp.1 t (localBridgeHistory t) (localBridgeHistory_admissible G t) with
    ⟨hconsumption, hlabor, hdeposits, hbonds⟩
  exact ⟨hconsumption, hlabor, add_nonneg hdeposits hbonds⟩

@[simp] theorem parent_pathConsumption (G : ℝ) (t : ℕ) :
    pathConsumption (householdPlanOfAllocation (parentAllocation G)) t =
      workerConsumption := by
  simp only [pathConsumption, householdPlanOfAllocation, parent_workerConsumption]

@[simp] theorem parent_pathLabor (G : ℝ) (t : ℕ) :
    pathLabor (householdPlanOfAllocation (parentAllocation G)) t =
      aggregateLabor := by
  simp only [pathLabor, householdPlanOfAllocation, parent_workerLabor]

@[simp] theorem parent_pathAssets (G : ℝ) (t : ℕ) :
    pathAssets (householdPlanOfAllocation (parentAllocation G)) t =
      parentAssets G := by
  simp only [pathAssets, householdPlanOfAllocation, parent_householdDeposits,
    parent_householdBonds, parentAssets]

@[simp] theorem parent_assetGap_zero (G : ℝ) (t : ℕ) :
    assetGap G (householdPlanOfAllocation (parentAllocation G)) t = 0 := by
  simp only [assetGap, parent_pathAssets, sub_self]

/-- La cota inferior del diferencial procede solo de a_t >= 0. -/
theorem assetGap_lower_bound (G : ℝ) (p : HouseholdPlan LocalBridgePhase)
    (hp : HouseholdFeasible (primitives G) (inheritedState G)
      (parentAllocation G) p) (t : ℕ) :
    -parentAssets G ≤ assetGap G p t := by
  have hassets := (path_domain G p hp t).2.2
  unfold assetGap
  linarith

/-- Diferencia del presupuesto inicial: el repago heredado es comun a los
dos planes y se cancela sin imponer restricciones nuevas a la alternativa. -/
theorem budget_difference_zero (G : ℝ) (p : HouseholdPlan LocalBridgePhase)
    (hp : HouseholdFeasible (primitives G) (inheritedState G)
      (parentAllocation G) p) :
    pathConsumption p 0 - workerConsumption -
        wage * (pathLabor p 0 - aggregateLabor) = -assetGap G p 0 := by
  have hadmissible := localBridgeHistory_admissible G 0
  have halternative := hp.2.1 (localBridgeHistory 0) hadmissible
  have hparent := (parent_householdBudgetFlows G).1
    (localBridgeHistory 0) hadmissible
  simp only [parent_wage, parent_inflation, div_one] at halternative
  simp only [parent_workerConsumption, parent_householdDeposits,
    parent_householdBonds, parent_wage, parent_workerLabor,
    parent_inflation, div_one] at hparent
  unfold pathConsumption pathLabor assetGap pathAssets parentAssets
  linear_combination halternative - hparent

/-- Diferencia del presupuesto sucesor: los dos activos tienen la misma
tasa nominal 100/99 y la inflacion del padre es uno. -/
theorem budget_difference_succ (G : ℝ) (p : HouseholdPlan LocalBridgePhase)
    (hp : HouseholdFeasible (primitives G) (inheritedState G)
      (parentAllocation G) p) (t : ℕ) :
    pathConsumption p (t + 1) - workerConsumption -
        wage * (pathLabor p (t + 1) - aggregateLabor) =
      (100 / 99 : ℝ) * assetGap G p t - assetGap G p (t + 1) := by
  have hchild : childHistory (localBridgeHistory t)
      (if t = 0 then LocalBridgePhase.dateOne else LocalBridgePhase.recurrent) =
      localBridgeHistory (t + 1) := (localBridgeHistory_succ t).symm
  have hadmissible : FirmHistoryAdmissible (primitives G) (t + 1)
      (childHistory (localBridgeHistory t)
        (if t = 0 then LocalBridgePhase.dateOne else LocalBridgePhase.recurrent)) := by
    rw [hchild]
    exact localBridgeHistory_admissible G (t + 1)
  have halternative := hp.2.2 t (localBridgeHistory t)
    (if t = 0 then LocalBridgePhase.dateOne else LocalBridgePhase.recurrent) hadmissible
  have hparent := (parent_householdBudgetFlows G).2 t (localBridgeHistory t)
    (if t = 0 then LocalBridgePhase.dateOne else LocalBridgePhase.recurrent) hadmissible
  rw [hchild] at halternative hparent
  simp only [parent_wage, parent_depositRate, parent_governmentBondRate,
    parent_inflation, div_one, ProposedStationaryBank.depositRate] at halternative
  simp only [parent_workerConsumption, parent_householdDeposits,
    parent_householdBonds, parent_wage, parent_workerLabor,
    parent_depositRate, parent_governmentBondRate, parent_inflation,
    div_one, ProposedStationaryBank.depositRate] at hparent
  unfold pathConsumption pathLabor assetGap pathAssets parentAssets
  linear_combination halternative - hparent


/-! ## Desigualdad global de utilidad -/

open ProposedStationaryRealScale

theorem crra_one_eq_log (c : ℝ) :
    crraUtility 1 c = Real.log c := by
  unfold crraUtility
  rw [if_pos rfl]

/-- Tangente logaritmica en el consumo positivo de referencia. -/
theorem log_tangent (c C : ℝ) (hc : 0 < c) (hC : 0 < C) :
    Real.log c - Real.log C ≤ (c - C) / C := by
  have hlog := Real.log_le_sub_one_of_pos (div_pos hc hC)
  rw [Real.log_div (ne_of_gt hc) (ne_of_gt hC)] at hlog
  calc
    Real.log c - Real.log C ≤ c / C - 1 := hlog
    _ = (c - C) / C := by
      field_simp [ne_of_gt hC] <;> ring

/-- La tangente de la desutilidad cuadratica usa solo un cuadrado
no negativo; no precisa restricciones de signo sobre sus argumentos. -/
theorem quadratic_labor_tangent (ell L : ℝ) :
    -(ell ^ (2 : ℕ)) / 2 + L ^ (2 : ℕ) / 2 ≤ -L * (ell - L) := by
  nlinarith [sq_nonneg (ell - L)]

/-- Desigualdad de utilidad con las potencias reales de la fuente.
El salario queda identificado con la pendiente marginal C*L. -/
theorem household_utility_tangent
    (c ell C L w : ℝ) (hc : 0 < c) (hC : 0 < C) (hw : w = C * L) :
    (crraUtility 1 c - ell ^ (2 : ℝ) / 2) -
        (crraUtility 1 C - L ^ (2 : ℝ) / 2) ≤
      ((c - C) - w * (ell - L)) / C := by
  rw [crra_one_eq_log c, crra_one_eq_log C,
    Real.rpow_two ell, Real.rpow_two L]
  calc
    (Real.log c - ell ^ (2 : ℕ) / 2) -
        (Real.log C - L ^ (2 : ℕ) / 2) =
      (Real.log c - Real.log C) + (-(ell ^ (2 : ℕ)) / 2 + L ^ (2 : ℕ) / 2) := by
        ring
    _ ≤ (c - C) / C + (-L * (ell - L)) :=
      add_le_add (log_tangent c C hc hC) (quadratic_labor_tangent ell L)
    _ = ((c - C) - w * (ell - L)) / C := by
      rw [hw]
      field_simp [ne_of_gt hC] <;> ring

/-- Instancia del candidato exacto: el cierre salarial ya construido
proporciona wage=workerConsumption*aggregateLabor. -/
theorem stationary_household_utility_tangent
    (c ell : ℝ) (hc : 0 < c) :
    (crraUtility 1 c - ell ^ (2 : ℝ) / 2) -
        (crraUtility 1 workerConsumption - aggregateLabor ^ (2 : ℝ) / 2) ≤
      ((c - workerConsumption) - wage * (ell - aggregateLabor)) /
        workerConsumption := by
  exact household_utility_tangent c ell workerConsumption aggregateLabor wage
    hc workerConsumption_pos worker_labor_equation

end ProposedStationaryHouseholdOptimality
end Ventura26LiquidityAllocation
