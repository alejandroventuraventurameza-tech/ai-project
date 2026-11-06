import Ventura26LiquidityAllocation.StationaryBankOptimalityCandidate
import Mathlib.Algebra.Order.Ring.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Topology.Order.OrderClosed

/-!
# Optimalidad del productor de capital y del minorista: PROPUESTA SIN COMPILAR

Proyecto: alejandroventuraventurameza-tech/ai-project.
Rama: work/chat-continuity.
Commit: 16e24fe828a5a0002ef13bb82bae9e295f190f86.
Base AppliedModelingLib: 194edcc95df74806a39b961d10dedddc6e730cce.
Lean previsto: leanprover/lean4:v4.30.0-rc2.
Mathlib: 5450b53e5ddc75d46418fabb605edbf36bd0beb6.

ESTADO: PROPUESTA SIN COMPILAR. No se han ejecutado Lean, Lake ni
simulaciones. Las demostraciones matematicas y las revisiones de codigo
no acreditan elaboracion, compilacion, comprobacion por el kernel ni
una auditoria transitiva de axiomas. Toda la cadena propuesta conserva
este estado. Las fuentes fijadas no se modifican.

Las cantidades son las del padre estacionario. G permanece simbolico;
no se fija a un multiplo de reservas. Se conservan S y B como ramas
macroeconomicas separadas. Ningun resultado de estos modulos acredita
una continuacion perturbada, una IRF o unicidad del equilibrio completo.

Destino propuesto: papers/Ventura26LiquidityAllocation/StationaryProductionSectorsCandidate.lean.
SHA256 de StationaryBankOptimalityCandidate.lean utilizado:
2f13e9b1f8e455cbc8e3676066a5dde674b4acf285292990330f21bed84bc918

Argumento matematico previo al codigo:
1. El productor de capital compara toda inversion j>=0. Con K>0,
   q=81/80 y costo de ajuste 1/2, su ganancia es j/80-j^2/(4*K).
   La perdida respecto de I=K/40 es exactamente (j-K/40)^2/(4*K).
   Esto prueba optimalidad global y unicidad de esa inversion a precios dados.
2. El minorista elige un log-precio real x, cuyo precio relativo exp(x)
   es positivo. La fuente permite todos esos procesos, sin caja local.
3. Con y=exp(-x)>0, la perdida de margen CES respecto de 1/6 es
   (y-1)^2*(5*y^4+4*y^3+3*y^2+2*y+1)/6>=0.
   El costo Rotemberg 75*(exp(x-xprev)-1)^2 tambien es no negativo;
   xprev pertenece a la propia alternativa y es cero en la fecha heredada.
4. El candidato x=0 en todas las fechas alcanza beneficio Y/6 y costo
   de ajuste cero. El cociente de marginales del hogar es uno por consumo
   constante positivo, y el objetivo es (99/100)^t*Y/6.
5. Se prueba sumabilidad del candidato, cuyo pago es (50/3)*Y. Toda
   alternativa del dominio fuente tiene sumas finitas menores; su propia
   sumabilidad permite pasar al limite. No se agrega TVC ni concavidad global.

ALCANCE: CapitalProducerAccounts, CapitalProducerOptimal y RetailOptimal
literales del padre. El soporte minorista global usa sus precios e inflacion
estacionarios; no se transporta automaticamente a S o B perturbadas.
-/

open scoped BigOperators
open Filter

namespace Ventura26LiquidityAllocation
namespace ProposedStationaryProductionSectors

open ProposedStationaryRealScale
open ProposedStationaryPrimitives
open ProposedStationaryInheritedState
open ProposedStationaryLiteralAccounts

/-- Diferencia exacta de ganancias, valida para toda inversion real.
Solo el capital instalado del padre se usa como denominador. -/
theorem stationary_capitalProducer_profit_gap (G j : ℝ) :
    capitalPrice * j - capitalCreationTechnology (primitives G) j aggregateCapital -
        aggregateCapital / 6400 =
      -((j - aggregateCapital / 40) ^ 2 / (4 * aggregateCapital)) := by
  unfold capitalCreationTechnology capitalPrice
  rw [(stationary_parameters G).capitalAdjustmentCost_eq]
  field_simp [ne_of_gt aggregates_pos.1] <;> ring

theorem stationary_capitalProducer_profit_le (G j : ℝ) :
    capitalPrice * j - capitalCreationTechnology (primitives G) j aggregateCapital ≤
      aggregateCapital / 6400 := by
  have hden : 0 < 4 * aggregateCapital := mul_pos (by norm_num) aggregates_pos.1
  have hloss : 0 ≤ (j - aggregateCapital / 40) ^ 2 / (4 * aggregateCapital) :=
    div_nonneg (sq_nonneg _) hden.le
  have hgap := stationary_capitalProducer_profit_gap G j
  linarith

/-- El costo estrictamente cuadratico da unicidad global de la inversion
a estos precios. No se extiende esa unicidad a los otros mercados. -/
theorem stationary_capitalProducer_profit_lt (G j : ℝ)
    (hj : j ≠ aggregateCapital / 40) :
    capitalPrice * j - capitalCreationTechnology (primitives G) j aggregateCapital <
      aggregateCapital / 6400 := by
  have hden : 0 < 4 * aggregateCapital := mul_pos (by norm_num) aggregates_pos.1
  have hloss : 0 < (j - aggregateCapital / 40) ^ 2 / (4 * aggregateCapital) :=
    div_pos (sq_pos_of_ne_zero (sub_ne_zero.mpr hj)) hden
  have hgap := stationary_capitalProducer_profit_gap G j
  linarith

theorem stationary_capitalProducer_profit_eq_iff (G j : ℝ) :
    capitalPrice * j - capitalCreationTechnology (primitives G) j aggregateCapital =
        aggregateCapital / 6400 ↔
      j = aggregateCapital / 40 := by
  constructor
  · intro heq
    by_contra hj
    exact (ne_of_lt (stationary_capitalProducer_profit_lt G j hj)) heq
  · intro hj
    subst j
    have hgap := stationary_capitalProducer_profit_gap G (aggregateCapital / 40)
    simpa only [sub_self, pow_two, zero_mul, zero_div, neg_zero, sub_eq_zero] using hgap

/-- Las cuatro cuentas fuente, con dominio positivo del capital y
no negatividad de la inversion. Los campos contables son la completacion
literal ya construida, no premisas economicas adicionales. -/
theorem parent_capitalProducerAccounts (G : ℝ) :
    CapitalProducerAccounts (primitives G) (parentAllocation G) := by
  intro t h _hh
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [parent_aggregateCapital]
    exact aggregates_pos.1
  · rw [parent_investment]
    exact (div_pos aggregates_pos.1 (by norm_num)).le
  · rfl
  · rfl

/-- Cota de desviacion escrita con los campos literales del Allocation. -/
theorem parent_capitalProducer_deviation_le (G : ℝ) (t : ℕ)
    (h : History LocalBridgePhase t) (j : ℝ) :
    (parentAllocation G).capitalPrice t h * j -
        capitalCreationTechnology (primitives G) j
          ((parentAllocation G).aggregateCapital t h) ≤
      (parentAllocation G).capitalPrice t h * (parentAllocation G).investment t h -
        (parentAllocation G).capitalCreationCost t h := by
  simp only [parent_capitalPrice, parent_aggregateCapital, parent_investment,
    parent_capitalCreationCost]
  have hcandidate : capitalPrice * (aggregateCapital / 40) -
      (161 / 6400 : ℝ) * aggregateCapital = aggregateCapital / 6400 := by
    unfold capitalPrice
    ring
  rw [hcandidate]
  exact stationary_capitalProducer_profit_le G j

/-- Optimalidad global del productor de capital en el predicado fuente.
Se cubren todas las inversiones j>=0 sin usar solo una condicion de primer orden. -/
theorem parent_capitalProducerOptimal (G : ℝ) :
    CapitalProducerOptimal (primitives G) (parentAllocation G) := by
  refine ⟨parent_capitalProducerAccounts G, ?_⟩
  intro t h _hh j _hj
  exact parent_capitalProducer_deviation_le G t h j

open ProposedStationaryRealScale
open ProposedStationaryPrimitives
open ProposedStationaryInheritedState
open ProposedStationaryLiteralAccounts

/-- Identidad algebraica global. El cociente es por la constante positiva
seis, sin division por precios alternativos. -/
theorem retailer_ces_gap_identity (y : ℝ) :
    (1 / 6 : ℝ) - (y ^ 5 - (5 / 6 : ℝ) * y ^ 6) =
      (y - 1) ^ 2 * (5 * y ^ 4 + 4 * y ^ 3 + 3 * y ^ 2 + 2 * y + 1) / 6 := by
  ring

theorem retailer_ces_gap_nonneg (y : ℝ) (hy : 0 ≤ y) :
    0 ≤ (1 / 6 : ℝ) - (y ^ 5 - (5 / 6 : ℝ) * y ^ 6) := by
  rw [retailer_ces_gap_identity]
  positivity

/-- Puente exponencial consultado en la revision fijada de Mathlib:
Real.exp_nat_mul (x) (n) afirma exp(n*x)=(exp x)^n. -/
theorem retailer_exp_neg_nat_mul (x : ℝ) (n : ℕ) :
    Real.exp (-(n : ℝ) * x) = (Real.exp (-x)) ^ n := by
  have harg : -(n : ℝ) * x = (n : ℝ) * (-x) := by ring
  rw [harg, Real.exp_nat_mul]

/-- La parte CES tiene soporte global 1/6 en todo logaritmo real. -/
theorem retailer_ces_six_upper (x : ℝ) :
    Real.exp (-5 * x) - (5 / 6 : ℝ) * Real.exp (-6 * x) ≤ (1 / 6 : ℝ) := by
  rw [retailer_exp_neg_nat_mul x 5, retailer_exp_neg_nat_mul x 6]
  exact sub_nonneg.mp
    (retailer_ces_gap_nonneg (Real.exp (-x)) (Real.exp_pos (-x)).le)

/-- Descomposicion exacta de la perdida, incluida la diferencia entre el
precio actual y su propio precio anterior. -/
theorem retailer_stationary_unit_gap_identity (x previous : ℝ) :
    (1 / 6 : ℝ) -
      (Real.exp (-5 * x) - (5 / 6 : ℝ) * Real.exp (-6 * x) -
        75 * (Real.exp (x - previous) - 1) ^ 2) =
      (Real.exp (-x) - 1) ^ 2 *
          (5 * (Real.exp (-x)) ^ 4 + 4 * (Real.exp (-x)) ^ 3 +
            3 * (Real.exp (-x)) ^ 2 + 2 * Real.exp (-x) + 1) / 6 +
        75 * (Real.exp (x - previous) - 1) ^ 2 := by
  rw [retailer_exp_neg_nat_mul x 5, retailer_exp_neg_nat_mul x 6]
  ring

/-- Restar un costo cuadratico no negativo conserva el soporte global.
No se supone ninguna relacion entre x y previous. -/
theorem retailer_stationary_unit_profit_le (x previous : ℝ) :
    Real.exp (-5 * x) - (5 / 6 : ℝ) * Real.exp (-6 * x) -
      75 * (Real.exp (x - previous) - 1) ^ 2 ≤ (1 / 6 : ℝ) := by
  have hcost : 0 ≤ (75 : ℝ) * (Real.exp (x - previous) - 1) ^ 2 := by
    positivity
  calc
    _ ≤ Real.exp (-5 * x) - (5 / 6 : ℝ) * Real.exp (-6 * x) :=
      sub_le_self _ hcost
    _ ≤ (1 / 6 : ℝ) := retailer_ces_six_upper x

/-- Especializacion literal del beneficio fuente del minorista. La
historia anterior pertenece al propio plan alternativo, no al candidato. -/
theorem parent_retailerProfit_formula (G : ℝ)
    (p : RetailerPlan LocalBridgePhase) (t : ℕ)
    (h : History LocalBridgePhase t) :
    retailerProfit (primitives G) (parentAllocation G) p t h =
      aggregateOutput *
        (Real.exp (-5 * p.logRelativePrice t h) -
          (5 / 6 : ℝ) * Real.exp (-6 * p.logRelativePrice t h) -
          75 * (Real.exp (p.logRelativePrice t h - previousRetailLog p t h) - 1) ^ 2) := by
  simp only [retailerProfit, parent_output, parent_inputPrice, parent_inflation]
  change aggregateOutput *
      (Real.exp ((1 - (6 : ℝ)) * p.logRelativePrice t h) -
        (5 / 6 : ℝ) * Real.exp (-(6 : ℝ) * p.logRelativePrice t h) -
        (150 : ℝ) / 2 *
          (1 * Real.exp (p.logRelativePrice t h - previousRetailLog p t h) - 1) ^ 2) = _
  norm_num

/-- Cota de beneficios en cada historia para TODO plan minorista de la
fuente, sin caja local ni hipotesis adicional de factibilidad. -/
theorem parent_retailerProfit_le (G : ℝ)
    (p : RetailerPlan LocalBridgePhase) (t : ℕ)
    (h : History LocalBridgePhase t) :
    retailerProfit (primitives G) (parentAllocation G) p t h ≤ aggregateOutput / 6 := by
  rw [parent_retailerProfit_formula]
  calc
    _ ≤ aggregateOutput * (1 / 6 : ℝ) :=
      mul_le_mul_of_nonneg_left
        (retailer_stationary_unit_profit_le (p.logRelativePrice t h)
          (previousRetailLog p t h)) aggregates_pos.2.1.le
    _ = aggregateOutput / 6 := by ring

open ProposedStationaryRealScale
open ProposedStationaryPrimitives
open ProposedStationaryInheritedState
open ProposedStationaryLiteralAccounts
open ProposedStationaryTerminalFoundation

@[simp] theorem parent_retailerLogRelativePrice (G : ℝ) (t : ℕ)
    (h : History LocalBridgePhase t) :
    (parentAllocation G).retailerLogRelativePrice t h = 0 := rfl

@[simp] theorem parent_retailerPlan_log (G : ℝ) (t : ℕ)
    (h : History LocalBridgePhase t) :
    (retailerPlanOfAllocation (parentAllocation G)).logRelativePrice t h = 0 := rfl

/-- Incluye la fecha cero: el log-precio heredado fuente tambien es cero. -/
@[simp] theorem parent_previousRetailLog (G : ℝ) (t : ℕ)
    (h : History LocalBridgePhase t) :
    previousRetailLog (retailerPlanOfAllocation (parentAllocation G)) t h = 0 := by
  cases t <;> rfl

/-- El candidato alcanza el maximo de margen y tiene costo de ajuste nulo. -/
theorem parent_retailerProfit (G : ℝ) (t : ℕ)
    (h : History LocalBridgePhase t) :
    retailerProfit (primitives G) (parentAllocation G)
      (retailerPlanOfAllocation (parentAllocation G)) t h = aggregateOutput / 6 := by
  rw [parent_retailerProfit_formula]
  simp only [parent_retailerPlan_log, parent_previousRetailLog]
  norm_num <;> ring

/-- El descuento marginal de consumo se normaliza por el mismo consumo
positivo del padre, tambien en la historia raiz. -/
theorem parent_retailerDiscountRatio (G : ℝ) (t : ℕ)
    (h : History LocalBridgePhase t) :
    crraMarginal (primitives G).workerRiskAversion
        ((parentAllocation G).workerConsumption t h) /
      crraMarginal (primitives G).workerRiskAversion
        ((parentAllocation G).workerConsumption 0 (rootHistory (primitives G).tree)) =
      1 := by
  unfold crraMarginal
  simp only [parent_workerConsumption]
  change workerConsumption ^ (-(1 : ℝ)) /
      workerConsumption ^ (-(1 : ℝ)) = 1
  exact div_self (Real.rpow_pos_of_pos workerConsumption_pos (-(1 : ℝ))).ne'

/-- Evaluacion de la expectativa literal en la historia canonica.
La alternativa puede variar libremente en las otras historias. -/
theorem parent_retailerPayoffTerm_path (G : ℝ)
    (p : RetailerPlan LocalBridgePhase) (t : ℕ) :
    retailerPayoffTerm (primitives G) (parentAllocation G) p t =
      (99 / 100 : ℝ) ^ t *
        retailerProfit (primitives G) (parentAllocation G) p t (localBridgeHistory t) := by
  unfold retailerPayoffTerm
  rw [primitives_expectationAt_eq]
  rw [parent_retailerDiscountRatio, one_mul]

theorem parent_retailerPayoffTerm (G : ℝ) (t : ℕ) :
    retailerPayoffTerm (primitives G) (parentAllocation G)
      (retailerPlanOfAllocation (parentAllocation G)) t =
      (99 / 100 : ℝ) ^ t * (aggregateOutput / 6) := by
  rw [parent_retailerPayoffTerm_path, parent_retailerProfit]

/-- Objetivo sumable del candidato, demostrado antes de comparar series. -/
theorem parent_retailObjectiveWellDefined (G : ℝ) :
    RetailObjectiveWellDefined (primitives G) (parentAllocation G)
      (retailerPlanOfAllocation (parentAllocation G)) := by
  change Summable (retailerPayoffTerm (primitives G) (parentAllocation G)
    (retailerPlanOfAllocation (parentAllocation G)))
  simpa only [parent_retailerPayoffTerm] using
    (fixed_beta_geometric (99 / 100 : ℝ) (aggregateOutput / 6)
      (by norm_num) (by norm_num)).1

/-- Valor exacto del flujo constante del candidato: no se omite ningun
descuento marginal de consumo al sumar. -/
theorem parent_retailPayoff_value (G : ℝ) :
    RetailPayoff (primitives G) (parentAllocation G)
      (retailerPlanOfAllocation (parentAllocation G)) =
      (50 / 3 : ℝ) * aggregateOutput := by
  have hgeo : Summable (fun n : ℕ ↦ (99 / 100 : ℝ) ^ n) :=
    summable_geometric_of_lt_one (by norm_num) (by norm_num)
  unfold RetailPayoff
  simp_rw [parent_retailerPayoffTerm]
  rw [hgeo.tsum_mul_right,
    tsum_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 99 / 100)
      (by norm_num : (99 / 100 : ℝ) < 1)]
  norm_num <;> ring

/-- Comparacion fecha a fecha sin suponer concavidad global de la funcion
de log-precio: el certificado polinomico provee el soporte necesario. -/
theorem parent_retailerPayoffTerm_le (G : ℝ)
    (p : RetailerPlan LocalBridgePhase) (t : ℕ) :
    retailerPayoffTerm (primitives G) (parentAllocation G) p t ≤
      retailerPayoffTerm (primitives G) (parentAllocation G)
        (retailerPlanOfAllocation (parentAllocation G)) t := by
  rw [parent_retailerPayoffTerm_path, parent_retailerPayoffTerm]
  exact mul_le_mul_of_nonneg_left
    (parent_retailerProfit_le G p t (localBridgeHistory t))
    (pow_nonneg (by norm_num : (0 : ℝ) ≤ 99 / 100) t)

/-- La sumabilidad fuente permite pasar de sumas finitas ordenadas a sus
limites. No se exige signo al beneficio de la alternativa ni TVC propia. -/
theorem parent_retailer_dominates (G : ℝ) (p : RetailerPlan LocalBridgePhase)
    (hpDefined : RetailObjectiveWellDefined (primitives G) (parentAllocation G) p) :
    RetailPayoff (primitives G) (parentAllocation G) p ≤
      RetailPayoff (primitives G) (parentAllocation G)
        (retailerPlanOfAllocation (parentAllocation G)) := by
  have hpSum : Summable (retailerPayoffTerm (primitives G) (parentAllocation G) p) :=
    hpDefined
  have hxSum : Summable (retailerPayoffTerm (primitives G) (parentAllocation G)
      (retailerPlanOfAllocation (parentAllocation G))) :=
    parent_retailObjectiveWellDefined G
  unfold RetailPayoff
  apply le_of_tendsto_of_tendsto' hpSum.hasSum.tendsto_sum_nat
    hxSum.hasSum.tendsto_sum_nat
  intro N
  exact Finset.sum_le_sum (fun t _ ↦ parent_retailerPayoffTerm_le G p t)

/-- Optimalidad minorista GLOBAL para el padre estacionario en el dominio
literal de RetailOptimal. No transporta esta propiedad a precios perturbados. -/
theorem parent_retailOptimal (G : ℝ) :
    RetailOptimal (primitives G) (parentAllocation G) := by
  refine ⟨parent_retailObjectiveWellDefined G, ?_⟩
  intro p hpDefined
  exact parent_retailer_dominates G p hpDefined

end ProposedStationaryProductionSectors
end Ventura26LiquidityAllocation
