import Ventura26LiquidityAllocation.StationaryFirmComparisonFoundationCandidate
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Group
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Topology.Order.OrderClosed

/-!
# Comparacion global de H y L: PROPUESTA SIN COMPILAR

Proyecto: alejandroventuraventurameza-tech/ai-project.
Rama: work/chat-continuity.
Commit: 16e24fe828a5a0002ef13bb82bae9e295f190f86.
Base AppliedModelingLib: 194edcc95df74806a39b961d10dedddc6e730cce.
Lean previsto: leanprover/lean4:v4.30.0-rc2.
Mathlib: 5450b53e5ddc75d46418fabb605edbf36bd0beb6.
Destino propuesto: papers/Ventura26LiquidityAllocation/StationaryFirmOptimalityCandidate.lean.
SHA256 de StationaryFirmComparisonFoundationCandidate.lean utilizado:
1428f28c85fac33756737360ec6c6ca3a560133294d937e4dac3828084c74df4

Todos los modulos propuestos de la cadena siguen SIN COMPILAR. Las
interfaces y las demostraciones se revisaron matematicamente y por lectura.
No se ejecutaron Lean ni simulaciones. No se acredita elaboracion, kernel,
inspeccion de axiomas ni aprobacion de la auditoria semantica.

Argumento previo al codigo:
- Para toda alternativa de FirmFeasible, la produccion admite el soporte
  global pi_i(k,l)<=pi_i*+u_i*(k-K_i), incluidos k=0 y l=0.
- A_t=q*k_t-b_t+d_t es la cartera literal de firmTerminalTerm. La
  garantia sobre R*b_t y el margen R*q-theta_i*J>0 implican A_t>=0.
- En fecha cero el capital es heredado K_i, por lo que la diferencia
  de riqueza es <=0. De aqui Delta c_0<=-Delta A_0.
- En sucesores se usan k_t y l_(t+1). La tangente productiva y la
  identidad financiera mu*(theta_i*J*k_t-R*b_t)+d_t/33>=0 dan
  betaE*Delta c_(t+1)<=Delta A_t-betaE*Delta A_(t+1).
- La tangente logaritmica, valorada con 1/c_i*, transforma estos pasos
  en f_0<=-v_0 y f_(t+1)<=v_t-v_(t+1), con
  v_t=betaE^t*Delta A_t/c_i*. La suma finita queda acotada por
  betaE^N*(A_i*-A_N)/c_i*<=betaE^N*A_i*/c_i* ->0.
- La sumabilidad de ambos objetivos permite el paso al limite y la
  comparacion global. No se impone TVC, capital positivo, acotacion
  ni exclusion de financiacion simultanea a la alternativa.

ALCANCE: FirmOptimal literal para H y L, a los precios e ingresos del
padre construido, para cualquier G. El paquete con HouseholdOptimal
conserva G>=Mpre, requerido por la factibilidad del hogar.
No se afirma optimalidad bancaria o minorista, unicidad, continuacion
perturbada ni equilibrio completo. La deuda queda simbolica y se conservan
las ramas macroeconomicas S y B; el padre no sustituye sus impactos.
-/

open scoped BigOperators
open Filter

namespace Ventura26LiquidityAllocation
namespace ProposedStationaryFirmOptimality

open ProposedStationaryRealScale
open ProposedStationaryPrimitives
open ProposedStationaryInheritedState
open ProposedStationaryPrivateFeasibility
open ProposedStationaryTerminalFoundation
open ProposedStationaryTerminal
open ProposedStationaryHouseholdOptimality

noncomputable def firmUtilityGap (G : ℝ) (i : FirmType)
    (p : FirmPlan LocalBridgePhase) (t : ℕ) : ℝ :=
  firmUtilityTerm (primitives G) p t -
    firmUtilityTerm (primitives G) (firmPlanOfAllocation (parentAllocation G) i) t

noncomputable def discountedFirmAssetGap (i : FirmType)
    (p : FirmPlan LocalBridgePhase) (t : ℕ) : ℝ :=
  (24 / 25 : ℝ) ^ t * firmAssetGap i p t / firmConsumption i

/-- La cartera terminal es no negativa para toda alternativa factible,
incluidos capital cero y prestamos/depositos simultaneos. -/
theorem firm_path_assets_nonneg (G : ℝ) (i : FirmType)
    (p : FirmPlan LocalBridgePhase)
    (hp : FirmFeasible (primitives G) (inheritedState G)
      (parentAllocation G) i p) (t : ℕ) :
    0 ≤ firmPathAssets p t := by
  have hdom := firm_path_domain G i p hp t
  exact firm_portfolio_nonneg i (firmPathCapital p t)
    (firmPathLoan p t) (firmPathDeposit p t) hdom.2.1
    (firm_path_collateral G i p hp t) hdom.2.2.2.2

/-- La expectativa se evalua en la historia canonica sin imponer
constancia de consumo a un plan alternativo. -/
theorem firmUtilityTerm_path (G : ℝ)
    (p : FirmPlan LocalBridgePhase) (t : ℕ) :
    firmUtilityTerm (primitives G) p t =
      (24 / 25 : ℝ) ^ t * crraUtility 1 (firmPathConsumption p t) := by
  unfold firmUtilityTerm
  rw [primitives_expectationAt_eq]
  change (24 / 25 : ℝ) ^ t *
    crraUtility 1 (p.consumption t (localBridgeHistory t)) =
      (24 / 25 : ℝ) ^ t * crraUtility 1 (firmPathConsumption p t)
  rfl

/-- Soporte global de la utilidad empresarial, usando el consumo positivo
del candidato como punto de tangencia. -/
theorem firmUtilityGap_le_consumption (G : ℝ) (i : FirmType)
    (p : FirmPlan LocalBridgePhase)
    (hp : FirmFeasible (primitives G) (inheritedState G)
      (parentAllocation G) i p) (t : ℕ) :
    firmUtilityGap G i p t ≤ (24 / 25 : ℝ) ^ t *
      (firmPathConsumption p t - firmConsumption i) / firmConsumption i := by
  have hc := (firm_path_domain G i p hp t).1
  have htangent : crraUtility 1 (firmPathConsumption p t) -
      crraUtility 1 (firmConsumption i) ≤
        (firmPathConsumption p t - firmConsumption i) / firmConsumption i := by
    simpa only [crra_one_eq_log] using
      log_tangent (firmPathConsumption p t) (firmConsumption i) hc
        (firmConsumption_pos i)
  calc
    firmUtilityGap G i p t = (24 / 25 : ℝ) ^ t *
        (crraUtility 1 (firmPathConsumption p t) - crraUtility 1 (firmConsumption i)) := by
      unfold firmUtilityGap
      rw [firmUtilityTerm_path, parent_firmUtilityTerm]
      unfold firmUtilityCoefficient
      ring
    _ ≤ (24 / 25 : ℝ) ^ t *
        ((firmPathConsumption p t - firmConsumption i) / firmConsumption i) :=
      mul_le_mul_of_nonneg_left htangent (pow_nonneg (by norm_num) t)
    _ = _ := by ring

/-- Fecha cero: la tangente se aplica al capital heredado K_i; solo
el trabajo corriente de la alternativa varia en su beneficio inicial. -/
theorem firm_consumption_difference_zero_le (G : ℝ) (i : FirmType)
    (p : FirmPlan LocalBridgePhase)
    (hp : FirmFeasible (primitives G) (inheritedState G)
      (parentAllocation G) i p) :
    firmPathConsumption p 0 - firmConsumption i ≤ -firmAssetGap i p 0 := by
  have hbudget := firm_budget_difference_zero G i p hp
  have hprofit : firmProfit i (capital i) (firmPathLabor p 0) ≤ profit i := by
    simpa only [firmProfit, sub_self, mul_zero, add_zero] using
      stationary_operatingProfit_support i (capital i) (firmPathLabor p 0)
        (capital_pos i).le (firm_path_domain G i p hp 0).2.2.1
  linarith

/-- La tangente productiva respeta el capital de t y el trabajo de t+1. -/
theorem firm_return_difference_le (G : ℝ) (i : FirmType)
    (p : FirmPlan LocalBridgePhase)
    (hp : FirmFeasible (primitives G) (inheritedState G)
      (parentAllocation G) i p) (t : ℕ) :
    firmPathConsumption p (t + 1) - firmConsumption i + firmAssetGap i p (t + 1) ≤
      (userCost i + liquidationValue) * (firmPathCapital p t - capital i) -
        ProposedStationaryBank.loanRate * (firmPathLoan p t - loan i) +
        ProposedStationaryBank.depositRate * firmPathDeposit p t := by
  have hbudget := firm_budget_difference_succ_gross G i p hp t
  have hprofit : firmProfit i (firmPathCapital p t) (firmPathLabor p (t + 1)) ≤
      profit i + userCost i * (firmPathCapital p t - capital i) :=
    stationary_operatingProfit_support i (firmPathCapital p t) (firmPathLabor p (t + 1))
      (firm_path_domain G i p hp t).2.1
      (firm_path_domain G i p hp (t + 1)).2.2.1
  nlinarith

/-- El soporte financiero incorpora los dos sobrantes no negativos:
mu*(theta*J*k-R*b) y d/33. No se impone colateral activo a la alternativa. -/
theorem firm_consumption_difference_succ_le (G : ℝ) (i : FirmType)
    (p : FirmPlan LocalBridgePhase)
    (hp : FirmFeasible (primitives G) (inheritedState G)
      (parentAllocation G) i p) (t : ℕ) :
    (24 / 25 : ℝ) * (firmPathConsumption p (t + 1) - firmConsumption i) ≤
      firmAssetGap i p t - (24 / 25 : ℝ) * firmAssetGap i p (t + 1) := by
  have hreturn := firm_return_difference_le G i p hp t
  have hscaled := mul_le_mul_of_nonneg_left hreturn (by norm_num : 0 ≤ (24 / 25 : ℝ))
  have hfinancial := firm_financial_support i (firmPathCapital p t)
    (firmPathLoan p t) (firmPathDeposit p t)
    (firm_path_collateral G i p hp t) (firm_path_domain G i p hp t).2.2.2.2
  have hgap : capitalPrice * (firmPathCapital p t - capital i) -
      (firmPathLoan p t - loan i) + firmPathDeposit p t = firmAssetGap i p t := by
    unfold firmAssetGap firmPathAssets parentFirmAssets
    ring
  rw [hgap] at hfinancial
  linarith

theorem firmUtilityGap_zero_le (G : ℝ) (i : FirmType)
    (p : FirmPlan LocalBridgePhase)
    (hp : FirmFeasible (primitives G) (inheritedState G)
      (parentAllocation G) i p) :
    firmUtilityGap G i p 0 ≤ -discountedFirmAssetGap i p 0 := by
  have hconsumption := firm_consumption_difference_zero_le G i p hp
  have hscaled := mul_le_mul_of_nonneg_right hconsumption
    (inv_pos.mpr (firmConsumption_pos i)).le
  calc
    firmUtilityGap G i p 0 ≤
        (firmPathConsumption p 0 - firmConsumption i) / firmConsumption i := by
      simpa only [pow_zero, one_mul] using firmUtilityGap_le_consumption G i p hp 0
    _ ≤ (-firmAssetGap i p 0) / firmConsumption i := by
      simpa only [div_eq_mul_inv] using hscaled
    _ = -discountedFirmAssetGap i p 0 := by
      simp only [discountedFirmAssetGap, pow_zero, one_mul, neg_div]

theorem firmUtilityGap_succ_le (G : ℝ) (i : FirmType)
    (p : FirmPlan LocalBridgePhase)
    (hp : FirmFeasible (primitives G) (inheritedState G)
      (parentAllocation G) i p) (t : ℕ) :
    firmUtilityGap G i p (t + 1) ≤
      discountedFirmAssetGap i p t - discountedFirmAssetGap i p (t + 1) := by
  have hconsumption := firm_consumption_difference_succ_le G i p hp t
  have hfactor : 0 ≤ (24 / 25 : ℝ) ^ t / firmConsumption i :=
    div_nonneg (pow_nonneg (by norm_num) t) (firmConsumption_pos i).le
  have hscaled := mul_le_mul_of_nonneg_left hconsumption hfactor
  calc
    firmUtilityGap G i p (t + 1) ≤ (24 / 25 : ℝ) ^ (t + 1) *
        (firmPathConsumption p (t + 1) - firmConsumption i) / firmConsumption i :=
      firmUtilityGap_le_consumption G i p hp (t + 1)
    _ = ((24 / 25 : ℝ) ^ t / firmConsumption i) *
        ((24 / 25 : ℝ) * (firmPathConsumption p (t + 1) - firmConsumption i)) := by
      rw [pow_succ]
      ring
    _ ≤ ((24 / 25 : ℝ) ^ t / firmConsumption i) *
        (firmAssetGap i p t - (24 / 25 : ℝ) * firmAssetGap i p (t + 1)) := hscaled
    _ = discountedFirmAssetGap i p t - discountedFirmAssetGap i p (t + 1) := by
      simp only [discountedFirmAssetGap, pow_succ]
      ring

/-- Cota unilateral hasta todo horizonte N. La cartera alternativa no
negativa permite descartar su valor final sin exigir que converja. -/
theorem firmUtilityGap_partial_sum_bound (G : ℝ) (i : FirmType)
    (p : FirmPlan LocalBridgePhase)
    (hp : FirmFeasible (primitives G) (inheritedState G)
      (parentAllocation G) i p) (N : ℕ) :
    (∑ t ∈ Finset.range (N + 1), firmUtilityGap G i p t) ≤
      (24 / 25 : ℝ) ^ N * (parentFirmAssets i / firmConsumption i) := by
  have htelescope := sum_range_succ_le_neg_last
    (firmUtilityGap G i p) (discountedFirmAssetGap i p)
    (firmUtilityGap_zero_le G i p hp) (firmUtilityGap_succ_le G i p hp) N
  have hassets := firm_path_assets_nonneg G i p hp N
  have hnonneg : 0 ≤
      ((24 / 25 : ℝ) ^ N * firmPathAssets p N) / firmConsumption i :=
    div_nonneg (mul_nonneg (pow_nonneg (by norm_num) N) hassets)
      (firmConsumption_pos i).le
  calc
    (∑ t ∈ Finset.range (N + 1), firmUtilityGap G i p t) ≤
        -discountedFirmAssetGap i p N := htelescope
    _ = (24 / 25 : ℝ) ^ N * (parentFirmAssets i / firmConsumption i) -
        ((24 / 25 : ℝ) ^ N * firmPathAssets p N) / firmConsumption i := by
      unfold discountedFirmAssetGap firmAssetGap
      ring
    _ ≤ (24 / 25 : ℝ) ^ N * (parentFirmAssets i / firmConsumption i) :=
      sub_le_self _ hnonneg

/-- Comparacion de utilidad en todo el dominio literal de FirmOptimal.
La alternativa solo aporta factibilidad y un objetivo bien definido. -/
theorem parent_firm_dominates (G : ℝ) (i : FirmType)
    (p : FirmPlan LocalBridgePhase)
    (hp : FirmFeasible (primitives G) (inheritedState G)
      (parentAllocation G) i p)
    (hpDefined : FirmObjectiveWellDefined (primitives G) p) :
    discountedFirmUtility (primitives G) p ≤
      discountedFirmUtility (primitives G) (firmPlanOfAllocation (parentAllocation G) i) := by
  have hpSum : Summable (firmUtilityTerm (primitives G) p) := hpDefined
  have hxSum : Summable (firmUtilityTerm (primitives G)
      (firmPlanOfAllocation (parentAllocation G) i)) := parent_firmObjectiveWellDefined G i
  have hgapSum : Summable (firmUtilityGap G i p) := hpSum.sub hxSum
  have hpartial : Tendsto
      (fun N : ℕ ↦ ∑ t ∈ Finset.range (N + 1), firmUtilityGap G i p t)
      atTop (nhds (∑' t : ℕ, firmUtilityGap G i p t)) := by
    simpa only [Function.comp_def] using
      hgapSum.hasSum.tendsto_sum_nat.comp (Filter.tendsto_add_atTop_nat 1)
  have hupper : Tendsto
      (fun N : ℕ ↦ (24 / 25 : ℝ) ^ N * (parentFirmAssets i / firmConsumption i))
      atTop (nhds 0) :=
    (fixed_beta_geometric (24 / 25 : ℝ) (parentFirmAssets i / firmConsumption i)
      (by norm_num) (by norm_num)).2
  have hnonpos : (∑' t : ℕ, firmUtilityGap G i p t) ≤ 0 :=
    le_of_tendsto_of_tendsto' hpartial hupper
      (firmUtilityGap_partial_sum_bound G i p hp)
  have hdiff : (∑' t : ℕ, firmUtilityGap G i p t) =
      discountedFirmUtility (primitives G) p -
        discountedFirmUtility (primitives G)
          (firmPlanOfAllocation (parentAllocation G) i) := by
    unfold firmUtilityGap discountedFirmUtility
    exact hpSum.tsum_sub hxSum
  rw [hdiff] at hnonpos
  exact sub_nonpos.mp hnonpos

/-- Optimalidad empresarial del padre vinculante, para cualquiera de H/L.
La prueba no impone vinculacion a las alternativas y no depende de G. -/
theorem parent_firmOptimal (G : ℝ) (i : FirmType) :
    FirmOptimal (primitives G) (inheritedState G) (parentAllocation G) i := by
  refine ⟨parent_firmFeasible G i, parent_firmObjectiveWellDefined G i,
    parent_firmSourceTerminalCondition G i, ?_⟩
  intro p hp hpDefined
  exact parent_firm_dominates G i p hp hpDefined

/-- Reune solamente los problemas privados ya comparados globalmente.
El banco, las firmas minoristas y la continuacion perturbada son obligaciones
separadas; este paquete no se denomina equilibrio. -/
theorem parent_firms_and_householdOptimal (G : ℝ) (hG : reservesPre ≤ G) :
    (∀ i, FirmOptimal (primitives G) (inheritedState G) (parentAllocation G) i) ∧
      HouseholdOptimal (primitives G) (inheritedState G) (parentAllocation G) := by
  exact ⟨parent_firmOptimal G, parent_householdOptimal G hG⟩

end ProposedStationaryFirmOptimality
end Ventura26LiquidityAllocation
