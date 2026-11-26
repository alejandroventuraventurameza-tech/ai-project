import Ventura26LiquidityAllocation.StationaryHouseholdComparisonFoundationCandidate
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Group
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Topology.Order.OrderClosed

/-!
# Comparacion global del hogar: PROPUESTA SIN COMPILAR

Proyecto: alejandroventuraventurameza-tech/ai-project.
Rama: work/chat-continuity.
Commit: 16e24fe828a5a0002ef13bb82bae9e295f190f86.
Base AppliedModelingLib: 194edcc95df74806a39b961d10dedddc6e730cce.
Lean previsto: leanprover/lean4:v4.30.0-rc2.
Mathlib: 5450b53e5ddc75d46418fabb605edbf36bd0beb6.
Destino propuesto: papers/Ventura26LiquidityAllocation/StationaryHouseholdOptimalityCandidate.lean.
SHA256 de StationaryHouseholdComparisonFoundationCandidate.lean utilizado:
8f34b2bbe848b756def840dd5cec12e48f150125138c0d5f913a354c6218a58d

Todos los modulos propuestos de la cadena siguen SIN COMPILAR. Se han
consultado las definiciones y las firmas en las versiones fijadas.
No se han ejecutado Lean ni simulaciones. La revision matematica y estatica
no acredita elaboracion, kernel, inspeccion de axiomas o auditoria semantica.

Argumento previo al codigo:
- La alternativa es cualquier HouseholdPlan factible del dominio fuente.
  La historia canonica evalua su expectativa sin volver constante su plan.
- La concavidad global de log y el cuadrado laboral dan
  u(c,l)-u(C,L) <= ((c-C)-w*(l-L))/C, usando w=C*L.
- Al restar presupuestos, el flujo inicial es -assetGap_0; el sucesor
  es R_D*assetGap_t-assetGap_(t+1). Como betaW*R_D=1, los terminos
  interiores se cancelan en toda suma finita descontada.
- La ganancia de utilidad hasta N queda acotada por
  betaW^N*(A-a_N)/C <= betaW^N*A/C. Solo se usa a_N>=0.
- Summable de ambas utilidades permite el limite de sus sumas parciales.
  La cota geometrica tiende a cero. No se impone TVC a la alternativa,
  ni se supone convergencia o sumabilidad de sus activos o flujos.
- La comparacion y los tres resultados previos del candidato construyen
  exactamente HouseholdOptimal cuando G>=Mpre.

ALCANCE: optimalidad global del hogar del padre, en el dominio literal
HouseholdOptimal. No se afirma optimalidad empresarial o bancaria,
unicidad de la cartera del hogar, continuacion perturbada ni equilibrio
completo. La deuda publica queda simbolica; las ramas S y B se conservan.
-/

open scoped BigOperators
open Filter

namespace Ventura26LiquidityAllocation
namespace ProposedStationaryHouseholdOptimality

open ProposedStationaryRealScale
open ProposedStationaryPrimitives
open ProposedStationaryInheritedState
open ProposedStationaryPrivateFeasibility
open ProposedStationaryTerminalFoundation
open ProposedStationaryTerminal

/-- Diferencia de los terminos literales de utilidad, incluida la expectativa. -/
noncomputable def householdUtilityGap (G : ℝ)
    (p : HouseholdPlan LocalBridgePhase) (t : ℕ) : ℝ :=
  householdUtilityTerm (primitives G) p t -
    householdUtilityTerm (primitives G)
      (householdPlanOfAllocation (parentAllocation G)) t

/-- Diferencia patrimonial descontada y valorada con el marginal del candidato. -/
noncomputable def discountedAssetGap (G : ℝ)
    (p : HouseholdPlan LocalBridgePhase) (t : ℕ) : ℝ :=
  (99 / 100 : ℝ) ^ t * assetGap G p t / workerConsumption

/-- Evaluacion de la utilidad de un plan arbitrario sobre el calendario
determinista. No se supone que ese plan sea estacionario ni factible aqui. -/
theorem householdUtilityTerm_path (G : ℝ)
    (p : HouseholdPlan LocalBridgePhase) (t : ℕ) :
    householdUtilityTerm (primitives G) p t =
      (99 / 100 : ℝ) ^ t *
        (crraUtility 1 (pathConsumption p t) - pathLabor p t ^ (2 : ℝ) / 2) := by
  unfold householdUtilityTerm
  rw [primitives_expectationAt_eq]
  change (99 / 100 : ℝ) ^ t *
    (crraUtility 1 (p.consumption t (localBridgeHistory t)) -
      (1 : ℝ) * p.labor t (localBridgeHistory t) ^ (1 + (1 : ℝ)) /
        (1 + (1 : ℝ))) = _
  norm_num [pathConsumption, pathLabor]

/-- La desigualdad tangente global se multiplica por un descuento positivo. -/
theorem householdUtilityGap_le_flow (G : ℝ)
    (p : HouseholdPlan LocalBridgePhase)
    (hp : HouseholdFeasible (primitives G) (inheritedState G)
      (parentAllocation G) p) (t : ℕ) :
    householdUtilityGap G p t ≤
      (99 / 100 : ℝ) ^ t *
        (pathConsumption p t - workerConsumption -
          wage * (pathLabor p t - aggregateLabor)) / workerConsumption := by
  have hc := (path_domain G p hp t).1
  calc
    householdUtilityGap G p t = (99 / 100 : ℝ) ^ t *
        ((crraUtility 1 (pathConsumption p t) - pathLabor p t ^ (2 : ℝ) / 2) -
          householdUtilityCoefficient) := by
      unfold householdUtilityGap
      rw [householdUtilityTerm_path, parent_householdUtilityTerm]
      ring
    _ ≤ (99 / 100 : ℝ) ^ t *
        ((pathConsumption p t - workerConsumption -
          wage * (pathLabor p t - aggregateLabor)) / workerConsumption) := by
      exact mul_le_mul_of_nonneg_left
        (stationary_household_utility_tangent (pathConsumption p t) (pathLabor p t) hc)
        (pow_nonneg (by norm_num) t)
    _ = _ := by ring

/-- Fecha inicial: no aparece una diferencia de posiciones heredadas. -/
theorem householdUtilityGap_zero_le (G : ℝ)
    (p : HouseholdPlan LocalBridgePhase)
    (hp : HouseholdFeasible (primitives G) (inheritedState G)
      (parentAllocation G) p) :
    householdUtilityGap G p 0 ≤ -discountedAssetGap G p 0 := by
  have hbound := householdUtilityGap_le_flow G p hp 0
  rw [budget_difference_zero G p hp] at hbound
  simpa only [discountedAssetGap, pow_zero, one_mul, neg_div] using hbound

/-- Sucesores: betaW*R_D=1 transforma el flujo en una diferencia telescopica. -/
theorem householdUtilityGap_succ_le (G : ℝ)
    (p : HouseholdPlan LocalBridgePhase)
    (hp : HouseholdFeasible (primitives G) (inheritedState G)
      (parentAllocation G) p) (t : ℕ) :
    householdUtilityGap G p (t + 1) ≤
      discountedAssetGap G p t - discountedAssetGap G p (t + 1) := by
  have hbound := householdUtilityGap_le_flow G p hp (t + 1)
  rw [budget_difference_succ G p hp t] at hbound
  calc
    householdUtilityGap G p (t + 1) ≤
        (99 / 100 : ℝ) ^ (t + 1) *
          ((100 / 99 : ℝ) * assetGap G p t - assetGap G p (t + 1)) /
            workerConsumption := hbound
    _ = discountedAssetGap G p t - discountedAssetGap G p (t + 1) := by
      simp only [discountedAssetGap, pow_succ]
      ring

/-- Telescopado finito de desigualdades. No requiere sumar la sucesion v. -/
theorem sum_range_succ_le_neg_last (u v : ℕ → ℝ)
    (hzero : u 0 ≤ -v 0)
    (hstep : ∀ t, u (t + 1) ≤ v t - v (t + 1)) (N : ℕ) :
    (∑ t ∈ Finset.range (N + 1), u t) ≤ -v N := by
  induction N with
  | zero => simpa using hzero
  | succ N ih =>
      rw [Finset.sum_range_succ]
      have hnext := hstep N
      linarith

/-- Ganancia de utilidad de cualquier alternativa hasta el horizonte N.
La cota usa solo a_N>=0 y no exige una condicion terminal de la alternativa. -/
theorem householdUtilityGap_partial_sum_bound (G : ℝ)
    (p : HouseholdPlan LocalBridgePhase)
    (hp : HouseholdFeasible (primitives G) (inheritedState G)
      (parentAllocation G) p) (N : ℕ) :
    (∑ t ∈ Finset.range (N + 1), householdUtilityGap G p t) ≤
      (99 / 100 : ℝ) ^ N * (parentAssets G / workerConsumption) := by
  have htelescope := sum_range_succ_le_neg_last
    (householdUtilityGap G p) (discountedAssetGap G p)
    (householdUtilityGap_zero_le G p hp)
    (householdUtilityGap_succ_le G p hp) N
  have hassets := (path_domain G p hp N).2.2
  have hnonneg : 0 ≤
      ((99 / 100 : ℝ) ^ N * pathAssets p N) / workerConsumption :=
    div_nonneg (mul_nonneg (pow_nonneg (by norm_num) N) hassets)
      workerConsumption_pos.le
  calc
    (∑ t ∈ Finset.range (N + 1), householdUtilityGap G p t) ≤
        -discountedAssetGap G p N := htelescope
    _ = (99 / 100 : ℝ) ^ N * (parentAssets G / workerConsumption) -
        ((99 / 100 : ℝ) ^ N * pathAssets p N) / workerConsumption := by
      unfold discountedAssetGap assetGap
      ring
    _ ≤ (99 / 100 : ℝ) ^ N * (parentAssets G / workerConsumption) :=
      sub_le_self _ hnonneg

/-- Comparacion de horizonte infinito sobre todo el dominio de alternativas
de HouseholdOptimal. Solo se agrega objetivo bien definido a su factibilidad. -/
theorem parent_household_dominates (G : ℝ)
    (p : HouseholdPlan LocalBridgePhase)
    (hp : HouseholdFeasible (primitives G) (inheritedState G)
      (parentAllocation G) p)
    (hpDefined : HouseholdObjectiveWellDefined (primitives G) p) :
    discountedHouseholdUtility (primitives G) p ≤
      discountedHouseholdUtility (primitives G)
        (householdPlanOfAllocation (parentAllocation G)) := by
  have hpSum : Summable (householdUtilityTerm (primitives G) p) := hpDefined
  have hxSum : Summable (householdUtilityTerm (primitives G)
      (householdPlanOfAllocation (parentAllocation G))) :=
    parent_householdObjectiveWellDefined G
  have hgapSum : Summable (householdUtilityGap G p) := hpSum.sub hxSum
  have hpartial : Tendsto
      (fun N : ℕ ↦ ∑ t ∈ Finset.range (N + 1), householdUtilityGap G p t)
      atTop (nhds (∑' t : ℕ, householdUtilityGap G p t)) := by
    simpa only [Function.comp_def] using
      hgapSum.hasSum.tendsto_sum_nat.comp (Filter.tendsto_add_atTop_nat 1)
  have hupper : Tendsto
      (fun N : ℕ ↦ (99 / 100 : ℝ) ^ N * (parentAssets G / workerConsumption))
      atTop (nhds 0) :=
    (fixed_beta_geometric (99 / 100 : ℝ) (parentAssets G / workerConsumption)
      (by norm_num) (by norm_num)).2
  have hnonpos : (∑' t : ℕ, householdUtilityGap G p t) ≤ 0 :=
    le_of_tendsto_of_tendsto' hpartial hupper
      (householdUtilityGap_partial_sum_bound G p hp)
  have hdiff : (∑' t : ℕ, householdUtilityGap G p t) =
      discountedHouseholdUtility (primitives G) p -
        discountedHouseholdUtility (primitives G)
          (householdPlanOfAllocation (parentAllocation G)) := by
    unfold householdUtilityGap discountedHouseholdUtility
    exact hpSum.tsum_sub hxSum
  rw [hdiff] at hnonpos
  exact sub_nonpos.mp hnonpos

/-- Optimalidad del hogar del padre en el sentido literal de la fuente.
G>=Mpre se utiliza para la factibilidad del candidato, no para restringir
el conjunto de alternativas o asumir la desigualdad de comparacion. -/
theorem parent_householdOptimal (G : ℝ) (hG : reservesPre ≤ G) :
    HouseholdOptimal (primitives G) (inheritedState G) (parentAllocation G) := by
  refine ⟨parent_householdFeasible G hG,
    parent_householdObjectiveWellDefined G,
    parent_householdSourceTerminalCondition G, ?_⟩
  intro p hp hpDefined
  exact parent_household_dominates G p hp hpDefined

end ProposedStationaryHouseholdOptimality
end Ventura26LiquidityAllocation
