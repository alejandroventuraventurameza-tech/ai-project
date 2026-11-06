import Ventura26LiquidityAllocation.StationaryEquilibriumCandidate

/-!
# Barrera de actividad financiera: PROPUESTA SIN COMPILAR

Proyecto: alejandroventuraventurameza-tech/ai-project.
Rama: work/chat-continuity.
Commit: 16e24fe828a5a0002ef13bb82bae9e295f190f86.
Base AppliedModelingLib: 194edcc95df74806a39b961d10dedddc6e730cce.
Lean previsto: leanprover/lean4:v4.30.0-rc2.
Mathlib: 5450b53e5ddc75d46418fabb605edbf36bd0beb6.

ESTADO: PROPUESTA SIN COMPILAR. No se ha ejecutado Lean ni Lake.
Las fuentes conservadas FinancialCore.lean y EconomicModel.lean no se
modifican. Las KKT financieras son una hipotesis explicita: FirmOptimal
por si solo no identifica el campo collateralDual de una Allocation.

Argumento matematico:
1. FinancialCore clasifica las KKT firmadas en cinco casos: prestamo
   activo con dual positivo, prestamo holgado, autofinanciacion,
   deposito y frontera activa con dual cero. Si D<1/R, los ultimos
   cuatro casos son incompatibles con sus condiciones de descuento.
2. Si mu*=1/R*-D*>0, las dos desigualdades
   |1/R-1/R*|<mu*/4 y |D-D*|<mu*/4 implican
   mu*/2<1/R-D. Las KKT conservan entonces la rama activa y dual
   estrictamente positivo. Esto no afirma que exista una solucion
   de equilibrio en esa vecindad.
3. La complementariedad normalizada de EconomicModel y un dual
   reconstruido positivo fuerzan holgura cero.
4. La fila de financiacion S de la fuente es exactamente
   -R*localNormalizedCollateralDualL. Con R>0 y dual positivo no
   puede anularse, por lo que no se cumplen las ecuaciones S.

D es el descuento nominal empresarial (SDF real dividido por la
inflacion siguiente), no la cantidad de depositos bancarios. Los
resultados son algebraicos; no aportan un Jacobiano, una funcion de
continuacion, optimalidad fuera del padre o una prueba de existencia.
-/

/-!
Destino propuesto: papers/Ventura26LiquidityAllocation/ActiveSetBarrierCandidate.lean.
Dependencia propuesta StationaryEquilibriumCandidate.lean SHA256:
c6b97bdfd9662db5c1c29ee4e1bf0d8a80a7cbd9a9b218f060f18cbc45418baf.
EconomicModel.lean SHA256:
d5e9bb95aad09ff515cc1418778c241d1b91ca3095c02b31eb369f496ea38d86.
FinancialCore.lean SHA256:
4130b338183b3e5e659df7a7f2f517fc356967404c2571a82cea0154f9fc58fa.
-/

namespace Ventura26LiquidityAllocation
namespace ProposedStationaryBranchBridge

/-- La brecha de descuento estricta selecciona el primer caso de la
clasificacion financiera conservada. Las KKT permanecen explicitas. -/
theorem valuableCollateral_of_discount_lt_loanInverse
    {loanRate depositRate collateral capital discount promise dual : ℝ}
    (hdomain : PositiveFinancialDomain
      loanRate depositRate collateral capital discount)
    (hkkt : SignedFinancialKKT
      loanRate depositRate collateral capital discount promise dual)
    (hdiscount : discount < 1 / loanRate) :
    ValuableCollateralLoan loanRate collateral capital discount promise dual := by
  have hinverse : 1 / loanRate < 1 / depositRate :=
    one_div_lt_one_div_of_lt hdomain.1.1 hdomain.1.2
  rcases (signedFinancialKKT_iff_five_regimes hdomain).mp hkkt with
    hvaluable | hslack | hself | hdeposit | hboundary
  · exact hvaluable
  · rcases hslack with ⟨_hpromise, _hslack, _hdual, hdiscountEq⟩
    exfalso
    linarith
  · rcases hself with ⟨_hpromise, _hdual, hlower, _hupper⟩
    exfalso
    linarith
  · rcases hdeposit with ⟨_hpromise, _hdual, hdiscountEq⟩
    exfalso
    linarith
  · rcases hboundary with ⟨_hpromise, _hpositive, _hdual, hdiscountEq⟩
    exfalso
    linarith

/-- Dentro del sistema financiero fuente, la brecha es una
caracterizacion de la rama con colateral estrictamente valioso. -/
theorem valuableCollateral_iff_discount_lt_loanInverse
    {loanRate depositRate collateral capital discount promise dual : ℝ}
    (hdomain : PositiveFinancialDomain
      loanRate depositRate collateral capital discount)
    (hkkt : SignedFinancialKKT
      loanRate depositRate collateral capital discount promise dual) :
    ValuableCollateralLoan loanRate collateral capital discount promise dual ↔
      discount < 1 / loanRate := by
  constructor
  · intro hvaluable
    exact hvaluable.2.2.2.1
  · exact valuableCollateral_of_discount_lt_loanInverse hdomain hkkt

/-- Radio finito en las dos cantidades que determinan el dual:
la tasa inversa y el descuento nominal empresarial. -/
theorem fundingDual_gt_half_of_near_funding_data
    {loanRate discount referenceRate referenceDiscount : ℝ}
    (hmargin : 0 < 1 / referenceRate - referenceDiscount)
    (hrate : |1 / loanRate - 1 / referenceRate| <
      (1 / referenceRate - referenceDiscount) / 4)
    (hdiscount : |discount - referenceDiscount| <
      (1 / referenceRate - referenceDiscount) / 4) :
    (1 / referenceRate - referenceDiscount) / 2 <
      1 / loanRate - discount := by
  have hlower := (abs_lt.mp hrate).1
  have hupper := (abs_lt.mp hdiscount).2
  linarith

/-- Persistencia condicional del conjunto activo. Ademas de clasificar
la rama, se conserva un margen dual cuantitativo. -/
theorem valuableCollateral_of_near_funding_data
    {loanRate depositRate collateral capital discount promise dual
      referenceRate referenceDiscount : ℝ}
    (hdomain : PositiveFinancialDomain
      loanRate depositRate collateral capital discount)
    (hkkt : SignedFinancialKKT
      loanRate depositRate collateral capital discount promise dual)
    (hmargin : 0 < 1 / referenceRate - referenceDiscount)
    (hrate : |1 / loanRate - 1 / referenceRate| <
      (1 / referenceRate - referenceDiscount) / 4)
    (hdiscount : |discount - referenceDiscount| <
      (1 / referenceRate - referenceDiscount) / 4) :
    ValuableCollateralLoan loanRate collateral capital discount promise dual ∧
      (1 / referenceRate - referenceDiscount) / 2 < dual := by
  have hgap := fundingDual_gt_half_of_near_funding_data hmargin hrate hdiscount
  have hstrict : discount < 1 / loanRate := by linarith
  have hvaluable := valuableCollateral_of_discount_lt_loanInverse
    hdomain hkkt hstrict
  refine ⟨hvaluable, ?_⟩
  rw [hvaluable.2.2.2.2]
  exact hgap

/-- La vecindad anterior se centra en el padre concreto, cuyo descuento
nominal es 24/25 y cuyo dual positivo ya fue demostrado matematicamente. -/
theorem valuableCollateral_of_near_parent_funding
    {loanRate depositRate collateral capital discount promise dual : ℝ}
    (hdomain : PositiveFinancialDomain
      loanRate depositRate collateral capital discount)
    (hkkt : SignedFinancialKKT
      loanRate depositRate collateral capital discount promise dual)
    (hrate : |1 / loanRate - 1 / ProposedStationaryBank.loanRate| <
      ProposedStationaryProductionBridge.collateralMultiplier / 4)
    (hdiscount : |discount - (24 / 25 : ℝ)| <
      ProposedStationaryProductionBridge.collateralMultiplier / 4) :
    ValuableCollateralLoan loanRate collateral capital discount promise dual ∧
      ProposedStationaryProductionBridge.collateralMultiplier / 2 < dual := by
  exact valuableCollateral_of_near_funding_data hdomain hkkt
    ProposedStationaryProductionBridge.collateralMultiplier_pos hrate hdiscount

/-- Una desigualdad escalar de cercania conserva la mitad del margen. -/
theorem fundingDual_gt_half_of_abs_sub_lt_half
    {dual referenceDual : ℝ} (hreference : 0 < referenceDual)
    (hnear : |dual - referenceDual| < referenceDual / 2) :
    referenceDual / 2 < dual := by
  have hlower := (abs_lt.mp hnear).1
  linarith

/-- Identidad algebraica que relaciona la ecuacion de financiacion S
con el dual normalizado reconstruido; solo requiere tasa no nula. -/
theorem fundingResidual_eq_neg_rate_mul_gap
    {loanRate discount : ℝ} (hrate : loanRate ≠ 0) :
    loanRate * discount - 1 =
      -loanRate * (1 / loanRate - discount) := by
  field_simp [hrate] <;> ring

section SourcePrefix

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- Complementariedad fuente: un dual reconstruido estrictamente
positivo excluye holgura positiva. -/
theorem localScalarSlack_eq_zero_of_dual_pos
    (P : Primitives S) (Z : LocalPrefixCoordinates)
    (hcomp : LocalScalarComplementarityL P Z)
    (hdual : 0 < localNormalizedCollateralDualL P Z) :
    localNormalizedSlackL P Z = 0 := by
  exact (mul_eq_zero.mp hcomp.2.2).resolve_right hdual.ne'

/-- Version cuantitativa directamente en el predicado de
complementariedad de la fuente, sin identificar un campo dual libre. -/
theorem localScalarSlack_eq_zero_of_near_positive_dual
    (P : Primitives S) (Z : LocalPrefixCoordinates)
    {referenceDual : ℝ} (hreference : 0 < referenceDual)
    (hcomp : LocalScalarComplementarityL P Z)
    (hnear : |localNormalizedCollateralDualL P Z - referenceDual| <
      referenceDual / 2) :
    localNormalizedSlackL P Z = 0 := by
  have hhalf := fundingDual_gt_half_of_abs_sub_lt_half hreference hnear
  apply localScalarSlack_eq_zero_of_dual_pos P Z hcomp
  linarith

/-- La fila reducida S se identifica con el dual construido usando los
consumos y precios, no con el campo collateralDual de Allocation. -/
theorem localSlackFundingResidual_eq_neg_rate_mul_dual
    (P : Primitives S) (I : InheritedState)
    (Z : LocalPrefixCoordinates) (dateOne : S)
    (hrate : Z.controlsZero.loanRate ≠ 0) :
    localReducedFirmRegimeResidual .slack P
        (localPrefixDateZeroData P I Z dateOne) .L =
      -Z.controlsZero.loanRate * localNormalizedCollateralDualL P Z := by
  dsimp only [localReducedFirmRegimeResidual, localPrefixDateZeroData,
    localPrefixEntrepreneurSDF, localPrefixFirmConsumption,
    localNormalizedCollateralDualL]
  simpa only [mul_div_assoc] using
    (fundingResidual_eq_neg_rate_mul_gap
      (loanRate := Z.controlsZero.loanRate)
      (discount :=
        (P.entrepreneurDiscount *
          crraMarginal P.entrepreneurRiskAversion Z.controlsOne.consumptionL /
            crraMarginal P.entrepreneurRiskAversion Z.controlsZero.consumptionL) /
          Z.controlsOne.inflation)
      hrate)

/-- Un dual reconstruido positivo impide resolver las ecuaciones S.
No se necesita asumir complementariedad para esta incompatibilidad. -/
theorem localReducedPrefix_not_slack_of_dual_pos
    (P : Primitives S) (I : InheritedState)
    (Z : LocalPrefixCoordinates) (dateOne recurrent : S)
    (tail : LocalPrefixContinuationRule)
    (hrate : 0 < Z.controlsZero.loanRate)
    (hdual : 0 < localNormalizedCollateralDualL P Z) :
    ¬ LocalReducedPrefixEquationsHold .slack P I Z dateOne recurrent tail := by
  intro hrows
  have hfunding := hrows LocalPrefixEquation.firmRegimeZeroL
  change localReducedFirmRegimeResidual .slack P
    (localPrefixDateZeroData P I Z dateOne) .L = 0 at hfunding
  rw [localSlackFundingResidual_eq_neg_rate_mul_dual P I Z dateOne
    hrate.ne'] at hfunding
  have hproduct := mul_pos hrate hdual
  nlinarith

/-- Radio de exclusion S expresado en el dual reconstruido de la
fuente. La condicion de tasa positiva es economica y explicita. -/
theorem localReducedPrefix_not_slack_of_near_positive_dual
    (P : Primitives S) (I : InheritedState)
    (Z : LocalPrefixCoordinates) (dateOne recurrent : S)
    (tail : LocalPrefixContinuationRule)
    {referenceDual : ℝ} (hreference : 0 < referenceDual)
    (hrate : 0 < Z.controlsZero.loanRate)
    (hnear : |localNormalizedCollateralDualL P Z - referenceDual| <
      referenceDual / 2) :
    ¬ LocalReducedPrefixEquationsHold .slack P I Z dateOne recurrent tail := by
  have hhalf := fundingDual_gt_half_of_abs_sub_lt_half hreference hnear
  apply localReducedPrefix_not_slack_of_dual_pos P I Z dateOne recurrent tail hrate
  linarith

end SourcePrefix

end ProposedStationaryBranchBridge
end Ventura26LiquidityAllocation
