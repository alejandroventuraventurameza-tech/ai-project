import Ventura26LiquidityAllocation.StationaryReducedSystemCandidate

/-!
# Primitivas explicitas del padre: PROPUESTA SIN COMPILAR

Proyecto: alejandroventuraventurameza-tech/ai-project.
Rama de referencia: work/chat-continuity.
Commit: 16e24fe828a5a0002ef13bb82bae9e295f190f86.
AppliedModelingLib: 194edcc95df74806a39b961d10dedddc6e730cce.
Lean previsto: leanprover/lean4:v4.30.0-rc2.
Mathlib fijado: 5450b53e5ddc75d46418fabb605edbf36bd0beb6.
SHA256 de StationaryReducedSystemCandidate.lean utilizado:
ea4d23c907fae69458c6005dd22b670333fceda9fbad7058b3f0d1ae40f6f94f
Destino propuesto:
papers/Ventura26LiquidityAllocation/StationaryPrimitivesCandidate.lean.

Se reutiliza localBridgeTree, con calendario 0 -> 1 -> recurrente.
Las productividades agregadas son uno y las innovaciones son cero en
las tres fases. Los dos pagos se etiquetan con los naturales 0 y 1;
sus realizaciones son -1/5 y 1/5, con masas 1/2.

Las primitivas reales y bancarias proceden de los candidatos anteriores.
La calibracion adicional conserva priceAdjustmentCost=150,
rho_R=rho_M=1/2, phi_pi=3/2 y phi_y=1/8, tal como aparecen en
code/irf/finite_irf.py (formulas 315--351 y parametros 835--846).
Los limites bancarios son 4 y 6; las rutas son rho=1/10 y Delta=1/50.

governmentBondSupply es el argumento G, sin elegir G=2*Mpre ni suponer
G positivo para construir Primitives. Ese registro no exige el signo
de G. La admisibilidad del cierre fiscal y MonetaryPolicyPrimitiveDomain
mantienen sus condiciones correspondientes sobre G y el estado heredado.

No se han ejecutado Lean ni simulaciones. Los terminos de prueba siguientes son
candidatos sin compilar y dependen de otros cuatro candidatos sin compilar.
Construir Primitives y verificar sus campos no construye una Allocation,
un estado heredado fiscal ni una continuacion de equilibrio. Se mantienen
los alcances de stationary_reduced_system y de su transporte recurrente;
no se identifica el padre vinculante con el impacto S.
-/

open scoped BigOperators

namespace Ventura26LiquidityAllocation
namespace ProposedStationaryPrimitives

open ProposedStationaryRealScale
open ProposedStationaryProductionBridge
open ProposedStationaryReducedSystem

/-- Etiquetas contables del shock de pagos; BankPayment es Nat en la base. -/
def binarySupport : Finset BankPayment := {0, 1}

noncomputable def binaryProbability (omega : BankPayment) : ℝ :=
  if omega ∈ binarySupport then 1 / 2 else 0

noncomputable def binaryShock (omega : BankPayment) : ℝ :=
  if omega = 0 then -(1 / 5 : ℝ)
  else if omega = 1 then (1 / 5 : ℝ) else 0

theorem mem_binarySupport (omega : BankPayment) :
    omega ∈ binarySupport ↔ omega = 0 ∨ omega = 1 := by
  simp [binarySupport]

theorem binaryProbability_nonneg (omega : BankPayment) :
    0 ≤ binaryProbability omega := by
  by_cases h : omega ∈ binarySupport <;> norm_num [binaryProbability, h]

theorem binaryProbability_pos_on_support (omega : BankPayment)
    (h : omega ∈ binarySupport) : 0 < binaryProbability omega := by
  norm_num [binaryProbability, h]

theorem binaryShock_gt_neg_one_on_support (omega : BankPayment)
    (h : omega ∈ binarySupport) : -1 < binaryShock omega := by
  rcases (mem_binarySupport omega).mp h with hzero | hone
  · subst omega
    norm_num [binaryShock]
  · subst omega
    norm_num [binaryShock]

theorem binaryProbability_zero_outside (omega : BankPayment)
    (h : omega ∉ binarySupport) : binaryProbability omega = 0 := by
  simp only [binaryProbability, if_neg h]

theorem binaryProbability_sum_one :
    (∑ omega ∈ binarySupport, binaryProbability omega) = 1 := by
  norm_num [binarySupport, binaryProbability]

theorem binaryShock_mean_zero :
    (∑ omega ∈ binarySupport, binaryProbability omega * binaryShock omega) = 0 := by
  norm_num [binarySupport, binaryProbability, binaryShock]

/-- Instancia literal del padre, con deuda publica G conservada como parametro. -/
noncomputable def primitives (G : ℝ) : Primitives LocalBridgePhase where
  tree := localBridgeTree
  mass := fun _ ↦ 1 / 2
  productivity := technology
  aggregateProductivity := fun _ ↦ 1
  pledgeability := pledgeability
  alpha := 2 / 5
  beta := 1 / 2
  depreciation := 1 / 40
  entrepreneurDiscount := 24 / 25
  workerDiscount := 99 / 100
  entrepreneurRiskAversion := 1
  workerRiskAversion := 1
  laborCurvature := 1
  laborScale := 1
  priceElasticity := 6
  priceAdjustmentCost := 150
  capitalAdjustmentCost := 1 / 2
  bankExit := 1 / 10
  bankSeedShare := seedShare
  bankDepositCap := 4
  bankLoanCap := 6
  matchingIntensity := Real.log 2
  governmentBondSupply := G
  reserveRatePersistence := 1 / 2
  reserveQuantityPersistence := 1 / 2
  reserveRateSteady := ProposedStationaryBank.reserveRate
  reserveQuantitySteady := reservesPre
  outputReference := aggregateOutput
  inflationResponse := 3 / 2
  outputResponse := 1 / 8
  reserveRateInnovation := fun _ ↦ 0
  reserveQuantityInnovation := fun _ ↦ 0
  reserveRequirementPath := fun _ _ ↦ 1 / 10
  corridorWidthPath := fun _ _ ↦ 1 / 50
  paymentSupport := binarySupport
  paymentProbability := binaryProbability
  paymentShock := binaryShock
  mass_pos := by
    intro i
    norm_num
  productivity_pos := technology_pos
  productivity_order := by
    norm_num [technology]
  aggregate_productivity_pos := by
    intro phase
    norm_num
  pledgeability_mem := by
    intro i
    exact ⟨(pledgeability_bounds i).1.le, (pledgeability_bounds i).2⟩
  alpha_pos := by norm_num
  beta_pos := by norm_num
  decreasing_returns := by norm_num
  price_elasticity_gt_one := by norm_num
  capital_adjustment_cost_pos := by norm_num
  matching_intensity_pos := Real.log_pos (by norm_num)
  depreciation_mem := by norm_num
  discount_order := by norm_num
  bank_exit_mem := by norm_num
  bank_seed_mem :=
    ⟨(bank_entry_parameters_admissible.2.1).le,
      (bank_entry_parameters_admissible.2.2).le⟩
  bank_caps_nonneg := by norm_num
  payment_probability_nonneg := binaryProbability_nonneg
  payment_probability_pos_on_support := binaryProbability_pos_on_support
  payment_shock_gt_neg_one_on_support := binaryShock_gt_neg_one_on_support
  payment_probability_zero_outside := binaryProbability_zero_outside
  payment_probability_sum_one := binaryProbability_sum_one
  payment_shock_mean_zero := binaryShock_mean_zero

@[simp] theorem primitives_tree (G : ℝ) :
    (primitives G).tree = localBridgeTree := rfl

@[simp] theorem governmentBondSupply_eq (G : ℝ) :
    (primitives G).governmentBondSupply = G := rfl

theorem binary_payment_law (G : ℝ) :
    BinarySymmetricPaymentLaw (primitives G) 0 1 (1 / 5) := by
  refine ⟨by norm_num, by norm_num, ?_, ?_, ?_, ?_, ?_⟩
  · intro omega
    change omega ∈ binarySupport ↔ omega = 0 ∨ omega = 1
    exact mem_binarySupport omega
  · change binaryProbability 0 = 1 / 2
    norm_num [binaryProbability, binarySupport]
  · change binaryProbability 1 = 1 / 2
    norm_num [binaryProbability, binarySupport]
  · change binaryShock 0 = -(1 / 5 : ℝ)
    norm_num [binaryShock]
  · change binaryShock 1 = (1 / 5 : ℝ)
    norm_num [binaryShock]

/-- Todas las calibraciones del paquete conjunto son definicionales. -/
theorem stationary_parameters (G : ℝ) : StationaryParameters (primitives G) :=
  { toStationaryRealParameters :=
      { alpha_eq := rfl
        beta_eq := rfl
        productivity_eq := fun _ ↦ rfl
        mass_eq := fun _ ↦ rfl
        depreciation_eq := rfl
        pledgeability_eq := fun _ ↦ rfl
        entrepreneurDiscount_eq := rfl
        workerDiscount_eq := rfl
        laborScale_eq := rfl
        workerRiskAversion_eq := rfl
        laborCurvature_eq := rfl
        capitalAdjustmentCost_eq := rfl
        priceElasticity_eq := rfl }
    bankExit_eq := rfl
    bankSeedShare_eq := rfl
    matchingIntensity_eq := rfl
    reserveRateSteady_eq := rfl
    reserveQuantitySteady_eq := rfl
    outputReference_eq := rfl }

theorem stationary_recurrent_inputs (G : ℝ) :
    StationaryRecurrentInputs (primitives G) :=
  { productivity_eq := rfl
    rateInnovation_eq := rfl
    quantityInnovation_eq := rfl
    requirement_eq := fun _ ↦ rfl
    width_eq := fun _ ↦ rfl }

/-- Se descargan los parametros y la ley binaria del resultado previo. -/
theorem concrete_reduced_system (G : ℝ) :
    (∀ row : Fin 11, localReducedRemainingResidual (primitives G) dateData row = 0) ∧
      (∀ i, localReducedFirmBudgetResidual (primitives G) dateData i = 0 ∧
        localReducedFirmCapitalEulerResidual .binding (primitives G) dateData i = 0 ∧
        localReducedFirmRegimeResidual .binding (primitives G) dateData i = 0) :=
  stationary_reduced_system (primitives G) (stationary_parameters G)
    0 1 (binary_payment_law G)

/-- Transporte sobre el constructor recurrente conservado; no es una
afirmacion sobre la existencia de una Allocation de equilibrio. -/
theorem concrete_recurrent_reduced_system (G : ℝ) :
    ∀ n,
      (∀ row : Fin 11,
        localReducedRemainingResidual (primitives G)
          (localRecurrentDateData (primitives G)
            (fun _ ↦ stateSix) (fun _ ↦ controls) n) row = 0) ∧
      (∀ i,
        localReducedFirmBudgetResidual (primitives G)
          (localRecurrentDateData (primitives G)
            (fun _ ↦ stateSix) (fun _ ↦ controls) n) i = 0 ∧
        localReducedFirmCapitalEulerResidual .binding (primitives G)
          (localRecurrentDateData (primitives G)
            (fun _ ↦ stateSix) (fun _ ↦ controls) n) i = 0 ∧
        localReducedFirmRegimeResidual .binding (primitives G)
          (localRecurrentDateData (primitives G)
            (fun _ ↦ stateSix) (fun _ ↦ controls) n) i = 0) :=
  constant_recurrent_reduced_system (primitives G) (stationary_parameters G)
    (stationary_recurrent_inputs G) 0 1 (binary_payment_law G)

end ProposedStationaryPrimitives
end Ventura26LiquidityAllocation
