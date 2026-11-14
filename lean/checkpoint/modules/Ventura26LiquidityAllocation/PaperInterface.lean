import Ventura26LiquidityAllocation.MainTheorems
import Ventura26LiquidityAllocation.Assumptions
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.LinearAlgebra.Dimension.Finite

/-!
# Human-Facing Paper Interface: Monetary Policy, Bank Liquidity and Capital Allocation

Transparent statement-first surface for the 57 numbered source results.  The
declarations below are specifications, not proofs.  Exact-type proof endpoints
live in `ProofInterface.lean`.
-/

open scoped BigOperators

namespace Ventura26LiquidityAllocation

/-! ## Paper-facing vocabulary used by several results -/

def UniformlyBounded (x : ℕ → ℝ) : Prop := ∃ C, 0 ≤ C ∧ ∀ t, |x t| ≤ C

def UniformlyPositive (x : ℕ → ℝ) : Prop := ∃ c, 0 < c ∧ ∀ t, c ≤ x t

def ExactRootOn (f : ℝ → ℝ) (a b : ℝ) : Prop :=
  ∃! x : ℝ, a ≤ x ∧ x ≤ b ∧ f x = 0

def ProcessNear {S : Type*} (r : ℝ) (x y : AdaptedProcess S) : Prop :=
  0 < r ∧ ∀ t h, |x t h - y t h| < r

def AllocationNear {S : Type*} (r : ℝ) (X Y : Allocation S) : Prop :=
  ProcessNear r X.workerConsumption Y.workerConsumption ∧
  ProcessNear r X.workerLabor Y.workerLabor ∧
  (∀ i, ProcessNear r (X.firmConsumption i) (Y.firmConsumption i)) ∧
  (∀ i, ProcessNear r (X.capital i) (Y.capital i)) ∧
  (∀ i, ProcessNear r (X.loan i) (Y.loan i)) ∧
  (∀ i, ProcessNear r (X.firmDeposit i) (Y.firmDeposit i)) ∧
  (∀ i, ProcessNear r (X.firmFace i) (Y.firmFace i)) ∧
  (∀ i, ProcessNear r (X.collateralDual i) (Y.collateralDual i)) ∧
  ProcessNear r X.loanRate Y.loanRate ∧
  ProcessNear r X.depositRate Y.depositRate ∧
  ProcessNear r X.inflation Y.inflation ∧
  ProcessNear r X.capitalPrice Y.capitalPrice ∧
  ProcessNear r X.output Y.output

def DateZeroSlackBorrower {S : Type*} [Fintype S]
    (P : Primitives S) (X : Allocation S) (i : FirmType) : Prop :=
  ∀ h : History S 0,
    0 < X.loan i 0 h ∧ X.collateralDual i 0 h = 0 ∧
      ∀ s, 0 < P.tree.transition (currentState h) s →
        X.loanRate 0 h * X.loan i 0 h <
          P.pledgeability i * (1 - P.depreciation) *
            (X.inflation 1 (childHistory h s) *
              X.capitalPrice 1 (childHistory h s)) * X.capital i 0 h

def DateZeroBindingBorrower {S : Type*} [Fintype S]
    (P : Primitives S) (X : Allocation S) (i : FirmType) : Prop :=
  ∀ h : History S 0,
    0 < X.loan i 0 h ∧ 0 < X.collateralDual i 0 h ∧
      RobustCollateral (P.pledgeability i) P.depreciation
        (X.loanRate 0 h) (X.loan i 0 h) (X.capital i 0 h)
        (fun s ↦ 0 < P.tree.transition (currentState h) s)
        (fun s ↦ X.inflation 1 (childHistory h s))
        (fun s ↦ X.capitalPrice 1 (childHistory h s)) ∧
      ∃ s, 0 < P.tree.transition (currentState h) s ∧
        X.loanRate 0 h * X.loan i 0 h =
          P.pledgeability i * (1 - P.depreciation) *
            (X.inflation 1 (childHistory h s) *
              X.capitalPrice 1 (childHistory h s)) * X.capital i 0 h

def RestrictedFromDate {S : Type*} [Fintype S]
    (P : Primitives S) (X : Allocation S) (i : FirmType) (t0 : ℕ) : Prop :=
  ∀ t, t0 ≤ t → ∀ h : History S t,
    0 < X.loan i t h ∧ 0 < X.collateralDual i t h ∧
      RobustCollateral (P.pledgeability i) P.depreciation
        (X.loanRate t h) (X.loan i t h) (X.capital i t h)
        (fun s ↦ 0 < P.tree.transition (currentState h) s)
        (fun s ↦ X.inflation (t + 1) (childHistory h s))
        (fun s ↦ X.capitalPrice (t + 1) (childHistory h s))

def SameInheritedAndPrimitives {S : Type*} [Fintype S]
    (P₁ P₂ : Primitives S) (I₁ I₂ : InheritedState) : Prop :=
  P₁ = P₂ ∧ I₁ = I₂

def RightDirectionalDerivativeAt (f : ℝ → ℝ) (x v d : ℝ) : Prop :=
  Filter.Tendsto (fun ε : ℝ ↦ (f (x + ε * v) - f x) / ε)
    (nhdsWithin 0 (Set.Ioi 0)) (nhds d)

noncomputable def finiteMinimum {ι : Type*} [Fintype ι] [Nonempty ι]
    (f : ι → ℝ → ℝ) (x : ℝ) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty (fun i ↦ f i x)

def ActiveAt {ι : Type*} [Fintype ι] [Nonempty ι]
    (f : ι → ℝ → ℝ) (x : ℝ) (i : ι) : Prop :=
  f i x = finiteMinimum f x

def BoundedSequence (x : ℕ → ℝ) : Prop := UniformlyBounded x

def SequenceOperatorHasBoundedInverse (L : (ℕ → ℝ) → (ℕ → ℝ)) : Prop :=
  ∃ R : (ℕ → ℝ) → (ℕ → ℝ), ∃ C : ℝ, 0 ≤ C ∧
    (∀ b, L (R b) = b) ∧ (∀ y, R (L y) = y) ∧
    ∀ b M, (∀ t, |b t| ≤ M) → ∀ t, |R b t| ≤ C * M

def SequenceOperatorHasLipschitzInverse
    (L : (ℕ → ℝ) → (ℕ → ℝ)) (C : ℝ) : Prop :=
  ∃ R : (ℕ → ℝ) → (ℕ → ℝ),
    (∀ b, L (R b) = b) ∧ (∀ y, R (L y) = y) ∧
      ∀ b c M, (∀ t, |b t - c t| ≤ M) →
        ∀ t, |R b t - R c t| ≤ C * M

/-- Installed capital used for production at a history: inherited at date zero
and the parent history's choice thereafter. -/
def firmInstalledCapitalAt {S : Type*} [Fintype S]
    (I : InheritedState) (X : Allocation S) (i : FirmType) :
    (t : ℕ) → History S t → ℝ
  | 0, _ => I.capital i
  | t + 1, h => X.capital i t (previousHistory h)

/-- Static labour optimality inside the reduced operating-profit function. -/
def FirmLaborOptimal {S : Type*} [Fintype S] [DecidableEq S]
    (P : Primitives S) (I : InheritedState) (X : Allocation S)
    (i : FirmType) : Prop :=
  ∀ t h, FirmHistoryAdmissible P t h → ∀ alternative, 0 ≤ alternative →
    operatingProfit (X.inputPrice t h)
        (P.aggregateProductivity (currentState h) * P.productivity i)
        (firmInstalledCapitalAt I X i t h) alternative P.alpha P.beta
        (X.wage t h) ≤
      operatingProfit (X.inputPrice t h)
        (P.aggregateProductivity (currentState h) * P.productivity i)
        (firmInstalledCapitalAt I X i t h) (X.labor i t h) P.alpha P.beta
        (X.wage t h)

/-- Marginal operating product of the capital chosen at `t` in child `s`. -/
noncomputable def firmMarginalCapitalProductAt {S : Type*} [Fintype S]
    (P : Primitives S) (X : Allocation S) (i : FirmType)
    (t : ℕ) (h : History S t) (s : S) : ℝ :=
  X.inputPrice (t + 1) (childHistory h s) *
    (P.aggregateProductivity s * P.productivity i) * P.alpha *
    (X.capital i t h) ^ (P.alpha - 1) *
    (X.labor i (t + 1) (childHistory h s)) ^ P.beta

/-- The complete source KKT block for a firm's capital and signed funding
choice.  The marginal discount is constructed from the firm's own CRRA
marginal utility and future inflation; the collateral coefficient uses the
endogenous worst supported child. -/
def GeneralFirmFinancialKKT {S : Type*} [Fintype S] [DecidableEq S]
    (P : Primitives S) (X : Allocation S) (i : FirmType) : Prop :=
  ∀ t h, FirmHistoryAdmissible P t h →
    let face := X.firmFace i t h
    let cashMultiplier := crraMarginal P.entrepreneurRiskAversion
      (X.firmConsumption i t h)
    let marginalDiscount := P.entrepreneurDiscount *
      (∑ s, if 0 < P.tree.transition (currentState h) s then
        P.tree.transition (currentState h) s *
          crraMarginal P.entrepreneurRiskAversion
            (X.firmConsumption i (t + 1) (childHistory h s)) /
            X.inflation (t + 1) (childHistory h s)
        else 0) / cashMultiplier
    ∃ liquidation, SupportedWorstChildValue P X t h liquidation ∧
      let collateralCoefficient :=
        P.pledgeability i * (1 - P.depreciation) * liquidation
      0 < cashMultiplier ∧ 0 < marginalDiscount ∧
      X.capitalPrice t h =
        (∑ s, if 0 < P.tree.transition (currentState h) s then
          P.tree.transition (currentState h) s * P.entrepreneurDiscount *
            crraMarginal P.entrepreneurRiskAversion
              (X.firmConsumption i (t + 1) (childHistory h s)) /
              cashMultiplier *
            (firmMarginalCapitalProductAt P X i t h s +
              (1 - P.depreciation) *
                X.capitalPrice (t + 1) (childHistory h s))
          else 0) + X.collateralDual i t h * collateralCoefficient ∧
      0 ≤ collateralCoefficient * X.capital i t h - face ∧
      0 ≤ X.collateralDual i t h ∧
      X.collateralDual i t h *
        (collateralCoefficient * X.capital i t h - face) = 0 ∧
      ∀ alternative,
        fundingCash (X.loanRate t h) (X.depositRate t h) alternative ≤
          fundingCash (X.loanRate t h) (X.depositRate t h) face +
            (marginalDiscount + X.collateralDual i t h) * (alternative - face)

/-! ## Main text, in source order -/

/-- Lemma 3.1. -/
def repaymentSpec : Prop :=
  ∀ (qNext inflationNext theta depreciation loanRate depositRate loan deposit
      capitalNext operatingProfit : ℝ),
    0 < qNext → 0 < inflationNext → 0 ≤ theta → theta < 1 →
    0 < depreciation → depreciation < 1 → 0 ≤ operatingProfit →
    0 < loanRate → 0 < depositRate → 0 ≤ loan → 0 ≤ deposit →
    0 ≤ capitalNext →
    loanRate * loan ≤
      theta * (1 - depreciation) * (inflationNext * qNext) * capitalNext →
    loanRate * loan / inflationNext ≤
        theta * (1 - depreciation) * qNext * capitalNext ∧
      operatingProfit + (1 - theta) * (1 - depreciation) * qNext * capitalNext +
          depositRate * deposit / inflationNext ≤
        operatingProfit + (1 - depreciation) * qNext * capitalNext -
          loanRate * loan / inflationNext + depositRate * deposit / inflationNext ∧
      0 ≤ operatingProfit + (1 - theta) * (1 - depreciation) * qNext * capitalNext +
          depositRate * deposit / inflationNext ∧
      ((0 < capitalNext ∨ 0 < deposit) →
        0 < operatingProfit + (1 - depreciation) * qNext * capitalNext -
          loanRate * loan / inflationNext + depositRate * deposit / inflationNext)

/-- Lemma 3.2. -/
def noSimultaneousSavingBorrowingSpec : Prop :=
  ∀ {W : Type*} [Fintype W]
      (probability marginalValueNext inflationNext : W → ℝ)
      (entrepreneurDiscount cashMultiplier discount loanRate depositRate collateralDual
        loanCornerDual depositCornerDual loan deposit : ℝ),
    NormalizedFirmMarginalDiscount probability marginalValueNext inflationNext
      entrepreneurDiscount cashMultiplier discount →
    0 < depositRate → depositRate < loanRate →
    0 ≤ collateralDual → 0 ≤ loanCornerDual → 0 ≤ depositCornerDual →
    0 ≤ loan → 0 ≤ deposit →
    loanRate * (discount + collateralDual) - 1 = loanCornerDual →
    loanCornerDual * loan = 0 →
    1 - depositRate * discount = depositCornerDual →
    depositCornerDual * deposit = 0 →
    loan = 0 ∨ deposit = 0

/-- Proposition 3.3. -/
def financingCapacityComparativeSpec : Prop :=
  ∀ ownResources capitalPrice collateral loanRate : ℝ,
    0 < ownResources → 0 < collateral → 0 < loanRate →
    collateral / loanRate < capitalPrice →
    HasDerivAt
      (fun r ↦ ownResources / (capitalPrice - collateral / r))
      (-ownResources * collateral /
        (loanRate ^ 2 * (capitalPrice - collateral / loanRate) ^ 2)) loanRate ∧
    -ownResources * collateral /
      (loanRate ^ 2 * (capitalPrice - collateral / loanRate) ^ 2) < 0

/-- Lemma 3.4.  A one-history deviation rules out simultaneous borrowing and
saving at every positive-probability history of a gross optimum; no global
summability closure is assumed for that argument.  Conversely every feasible
signed choice, not only a signed optimum, has the literal recovered gross
implementation.  The final optimality implication exposes only the precise
objective-domain closure it needs, rather than imposing the auxiliary strong
bounds on every alternative. -/
def signedFundingEquivalenceSpec : Prop :=
  ∀ {S : Type*} [Fintype S] [DecidableEq S]
      (P : Primitives S) (I : InheritedState) (X : Allocation S) (i : FirmType),
    (∀ t h, 0 < X.depositRate t h ∧ X.depositRate t h < X.loanRate t h) →
    (∀ t h s, 0 < P.tree.transition (currentState h) s →
      0 < P.pledgeability i * (1 - P.depreciation) *
      (X.inflation (t + 1) (childHistory h s) *
        X.capitalPrice (t + 1) (childHistory h s))) →
    StrictMonoOn (crraUtility P.entrepreneurRiskAversion) (Set.Ioi 0) →
    (∀ p : FirmPlan S,
      PositiveCapitalFirmPlanOptimal P I X i p →
        (∀ t h, FirmHistoryAdmissible P t h →
          (p.loan t h = 0 ∨ p.deposit t h = 0) ∧
          p.loan t h = signedLoanPosition (X.loanRate t h) (p.face t h) ∧
          p.deposit t h = signedDepositPosition (X.depositRate t h) (p.face t h) ∧
          (signedFirmPlanOfGross X p).consumption t h = p.consumption t h) ∧
        SignedFirmFeasible P I X i (signedFirmPlanOfGross X p) ∧
        SignedFirmObjectiveWellDefined P (signedFirmPlanOfGross X p) ∧
        discountedSignedFirmUtility P (signedFirmPlanOfGross X p) =
          discountedFirmUtility P p ∧
        SignedFirmPlanOptimal P I X i (signedFirmPlanOfGross X p)) ∧
    (∀ p : SignedFirmPlan S,
      SignedFirmFeasible P I X i p →
        let q := grossFirmPlanOfSigned X p
        FirmFeasible P I X i q ∧
        (∀ t h,
          q.face t h = p.face t h ∧
          q.consumption t h = p.consumption t h ∧
          q.capital t h = p.capital t h ∧ q.labor t h = p.labor t h ∧
          q.wealth t h = p.wealth t h ∧
          q.loan t h - q.deposit t h =
            fundingCash (X.loanRate t h) (X.depositRate t h) (p.face t h)) ∧
        (SignedFirmObjectiveWellDefined P p →
          FirmObjectiveWellDefined P q ∧
          discountedFirmUtility P q = discountedSignedFirmUtility P p)) ∧
    (∀ p : SignedFirmPlan S,
      SignedFirmPlanOptimal P I X i p →
      (∀ q : FirmPlan S,
        FirmFeasible P I X i q → (∀ t h, 0 < q.capital t h) →
        FirmObjectiveWellDefined P q →
          SignedFirmObjectiveWellDefined P (signedFirmPlanOfGross X q)) →
      PositiveCapitalFirmPlanOptimal P I X i (grossFirmPlanOfSigned X p))

/-- Lemma 3.5. -/
def fundingSupergradientSpec : Prop :=
  ∀ loanRate depositRate face slope,
    0 < depositRate → depositRate < loanRate →
    (∀ g, fundingCash loanRate depositRate g ≤
      fundingCash loanRate depositRate face + slope * (g - face)) ↔
    ((face < 0 ∧ slope = 1 / depositRate) ∨
      (face = 0 ∧ 1 / loanRate ≤ slope ∧ slope ≤ 1 / depositRate) ∨
      (0 < face ∧ slope = 1 / loanRate))

/-- Lemma 3.6. -/
def financialKKTEquivalenceSpec : Prop :=
  ∀ loanRate depositRate collateral capital discount loan deposit dual,
    0 < depositRate → depositRate < loanRate → 0 < collateral →
    0 < capital → 0 < discount → 0 ≤ loan → 0 ≤ deposit →
    let face := loanRate * loan - depositRate * deposit
    (GrossFinancialKKT loanRate depositRate collateral capital discount
        loan deposit dual ↔
      loan = signedLoanPosition loanRate face ∧
        deposit = signedDepositPosition depositRate face ∧
        SignedFinancialKKT loanRate depositRate collateral capital discount face dual) ∧
    (SignedFinancialKKT loanRate depositRate collateral capital discount face dual ↔
      FinancialRegimeCases loanRate depositRate collateral capital discount face dual)

/-- Lemma 3.7. -/
def otcCorridorMonotonicitySpec : Prop :=
  ∀ reserveRate facilityRate matchingIntensity deficitSupply surplusSupply
      tightness : ℝ,
    reserveRate < facilityRate → 0 < matchingIntensity →
    BilateralOTCActivity deficitSupply surplusSupply tightness →
    let value := otcCorridorWeight matchingIntensity
    let negotiatedRate := fun tightness ↦
      reserveRate + (facilityRate - reserveRate) * value tightness
    (∀ tightness, 0 < tightness →
      reserveRate < negotiatedRate tightness ∧
        negotiatedRate tightness < facilityRate) ∧
    ContinuousAt value 1 ∧ value 1 = 1 / 2 ∧
      StrictMonoOn value (Set.Ioi 0)

/-- Proposition 3.8. -/
def bankSpreadNonnegativeSpec : Prop :=
  ∀ {S J : Type*} [Fintype S] [DecidableEq S] [Fintype J]
      (P : Primitives S) (X : Allocation S)
      (candidatePlan : BankPlan S)
      (t : ℕ) (h : History S t)
      (mass retainedEquityByType loansByType reservesByType depositsByType : J → ℝ)
      (depositCapByType loanCapByType : J → ℝ)
      (paymentSupportByType : J → Finset BankPayment)
      (paymentProbabilityByType paymentShockByType : J → BankPayment → ℝ)
      (candidateType : J) (bankValue : BankValueProcess S)
      (deficitSupply surplusSupply tightness : ℝ),
    0 < X.reserveRate t h →
    X.reserveRate t h < X.facilityRate t h →
    0 ≤ (P.reserveRequirementPath t h) → (P.reserveRequirementPath t h) < 1 →
    (P.reserveRequirementPath t h) < X.depositRate t h / X.reserveRate t h →
    BankInteriorSpreadLocalRegime P X candidatePlan t h mass retainedEquityByType
      loansByType reservesByType depositsByType depositCapByType loanCapByType
      paymentSupportByType
      paymentProbabilityByType paymentShockByType candidateType bankValue
      deficitSupply surplusSupply tightness →
    let shock := P.paymentShock
    let rho := (P.reserveRequirementPath t h)
    let xi := X.depositRate t h / X.reserveRate t h
    let deficitSlope := bankOTCDeficitSlopeAt P X t h tightness
    let surplusSlope := bankOTCSurplusSlopeAt P X t h tightness
    let retainedEquity := candidatePlan.retainedEquity t h
    let loans := candidatePlan.loans t h
    let reserves := candidatePlan.reservesPre t h
    let deposits := candidatePlan.deposits t h
    let settlementSurplus := fun ω ↦
      bankSettlementSurplus reserves rho xi deposits (shock ω)
    ∃ (marginalLiquidity : BankPayment → ℝ) (loanCapDual depositCapDual : ℝ),
      (∀ ω ∈ P.paymentSupport,
        IsOTCLiquiditySupergradient deficitSlope surplusSlope
          (settlementSurplus ω) (marginalLiquidity ω)) ∧
      0 ≤ loanCapDual ∧ 0 ≤ depositCapDual ∧
      loanCapDual * (P.bankLoanCap * retainedEquity - loans) = 0 ∧
      depositCapDual * (P.bankDepositCap * retainedEquity - deposits) = 0 ∧
      X.loanRate t h - X.depositRate t h =
        rho * finiteSupportExpectation P.paymentSupport P.paymentProbability
            marginalLiquidity -
          (xi - rho) * finiteSupportExpectation P.paymentSupport
            P.paymentProbability
            (fun ω ↦ marginalLiquidity ω * shock ω) +
          loanCapDual + depositCapDual ∧
      0 ≤ X.loanRate t h - X.depositRate t h

/-- Proposition 3.9. -/
def aggregateFlowConsistencySpec : Prop :=
  ∀ {S : Type*} [Fintype S] [DecidableEq S]
      (P : Primitives S) (I : InheritedState) (X : Allocation S),
    FirmBudgetFlows P I X → HouseholdBudgetFlows P I X →
    InheritedNominalFaceConsistency P I →
    CurrentNominalFaceConsistency P X →
    BankBalance P X → BankRenewalFlows P I X → ExactSettlementFlows P X →
    CreditClears P X → DepositsClear P X → CapitalClears P I X →
    LaborClears P X → AggregateProduction P I X →
    CapitalProducerAccounts P X → AccountingIdentities P X →
    FiscalClosure P I X → ResourceClears P X

/-! The common bridge candidate used by Propositions 4.1 and 4.2.  Sharing this
predicate prevents the local multiplicity statement from choosing an unrelated
economy after Proposition 4.1. -/
def BoundaryEquilibriumCandidate {S : Type*} [Fintype S] [DecidableEq S]
    (P : Primitives S) (I : InheritedState) (X : Allocation S) : Prop :=
  P.alpha = 2 / 5 ∧ P.beta = 1 / 2 ∧ P.entrepreneurRiskAversion = 1 ∧
    P.workerRiskAversion = 1 ∧ P.laborCurvature = 1 ∧
    P.priceElasticity = 6 ∧ P.priceAdjustmentCost = 150 ∧
    CompetitiveEquilibrium P I X ∧
    DateZeroBindingBorrower P X FirmType.H ∧
    (∀ h : History S 0, 0 < X.loan FirmType.L 0 h ∧
      X.collateralDual FirmType.L 0 h = 0) ∧
    RestrictedFromDate P X FirmType.H 1 ∧ RestrictedFromDate P X FirmType.L 1

/-- Proposition 4.1.  The remaining bridge-root task is to replace the current
`Phi` carrier by the literal resource residual of the algebraic construction. -/
def boundaryEquilibriumSpec : Prop :=
  ∃ (S : Type) (_ : Fintype S) (_ : DecidableEq S)
      (P : Primitives S) (I : InheritedState) (X : Allocation S) (Phi : ℝ → ℝ),
    ExactRootOn Phi 1.025 1.032 ∧ BoundaryEquilibriumCandidate P I X

/-- Proposition 4.2. -/
def localMacroMultiplicitySpec : Prop :=
  ∃ (S : Type) (_ : Fintype S) (_ : DecidableEq S)
      (P : Primitives S) (I : InheritedState) (X0 : Allocation S)
      (dateOne recurrent : S) (Z0 : LocalPrefixCoordinates)
      (tail : LocalPrefixContinuationRule)
      (solutionLog : (Fin 5 → ℝ) → (Fin 33 → ℝ)) (hStar r : ℝ),
    BoundaryEquilibriumCandidate P I X0 ∧
    InitialCalendarStateIsTransient P ∧
    DeterministicBridgeCalendar P dateOne recurrent ∧
    LocalMacroStrictBankRegime P I X0 dateOne ∧
    LocalPrefixCoordinatesRealized P X0 dateOne recurrent Z0 ∧
    LocalContinuationControlsRealized P X0 dateOne recurrent tail Z0.stateTwo ∧
    LocalExactContinuationAround P recurrent Z0.stateTwo tail ∧
    LocalPrefixEquationsHold LocalPrefixBranch.slack P I X0 dateOne recurrent ∧
    LocalPrefixEquationsHold LocalPrefixBranch.binding P I X0 dateOne recurrent ∧
    LocalReducedPrefixEquationsHold LocalPrefixBranch.slack P I Z0
      dateOne recurrent tail ∧
    LocalReducedPrefixEquationsHold LocalPrefixBranch.binding P I Z0
      dateOne recurrent tail ∧
    LocalReducedPrefixLogJacobianCertifiedAt LocalPrefixBranch.slack P I Z0
      dateOne recurrent tail 54.297 ∧
    LocalReducedPrefixLogJacobianCertifiedAt LocalPrefixBranch.binding P I Z0
      dateOne recurrent tail 75.023 ∧
    LocalScalarImplicitReduction P I Z0 dateOne recurrent tail solutionLog ∧
    LocalScalarComplementarityL P Z0 ∧
    localNormalizedSlackL P Z0 = 0 ∧
    localNormalizedCollateralDualL P Z0 = 0 ∧
    0 < hStar ∧ 0 < r ∧
    CompetitiveEquilibriumWithInitialIntervention P I
      zeroInitialPolicyIntervention X0 ∧
    (∀ h, -hStar < h → h < 0 →
      let Ph := initialIntervenedPrimitives P (pureReserveRateIntervention h)
      ∃ (Xs Xb : Allocation S) (Zs Zb : LocalPrefixCoordinates),
        Xs ≠ Xb ∧
        CompetitiveEquilibriumWithInitialIntervention P I
          (pureReserveRateIntervention h) Xs ∧
        CompetitiveEquilibriumWithInitialIntervention P I
          (pureReserveRateIntervention h) Xb ∧
        LocalMacroStrictBankRegime Ph I Xs dateOne ∧
        LocalMacroStrictBankRegime Ph I Xb dateOne ∧
        LocalPrefixCoordinatesRealized Ph Xs dateOne recurrent Zs ∧
        LocalPrefixCoordinatesRealized Ph Xb dateOne recurrent Zb ∧
        LocalContinuationControlsRealized Ph Xs dateOne recurrent tail Zs.stateTwo ∧
        LocalContinuationControlsRealized Ph Xb dateOne recurrent tail Zb.stateTwo ∧
        LocalPrefixEquationsHold LocalPrefixBranch.slack Ph I Xs
          dateOne recurrent ∧
        LocalPrefixEquationsHold LocalPrefixBranch.binding Ph I Xb
          dateOne recurrent ∧
        LocalReducedPrefixEquationsHold LocalPrefixBranch.slack Ph I Zs
          dateOne recurrent tail ∧
        LocalReducedPrefixEquationsHold LocalPrefixBranch.binding Ph I Zb
          dateOne recurrent tail ∧
        LocalScalarComplementarityL Ph Zs ∧
        LocalScalarComplementarityL Ph Zb ∧
        0 < localNormalizedSlackL Ph Zs ∧
        localNormalizedCollateralDualL Ph Zs = 0 ∧
        localNormalizedSlackL Ph Zb = 0 ∧
        0 < localNormalizedCollateralDualL Ph Zb ∧
        AllocationNear r X0 Xs ∧ AllocationNear r X0 Xb ∧
        DateZeroSlackBorrower Ph Xs FirmType.L ∧
        DateZeroBindingBorrower Ph Xb FirmType.L ∧
        DateZeroBindingBorrower Ph Xs FirmType.H ∧
        DateZeroBindingBorrower Ph Xb FirmType.H ∧
        RestrictedFromDate Ph Xs FirmType.H 1 ∧
        RestrictedFromDate Ph Xs FirmType.L 1 ∧
        RestrictedFromDate Ph Xb FirmType.H 1 ∧
        RestrictedFromDate Ph Xb FirmType.L 1 ∧
        (∀ X, CompetitiveEquilibriumWithInitialIntervention P I
            (pureReserveRateIntervention h) X → AllocationNear r X0 X →
          X = Xs ∨ X = Xb)) ∧
    (∀ h, 0 < h → h < hStar →
      ¬ ∃ X, CompetitiveEquilibriumWithInitialIntervention P I
          (pureReserveRateIntervention h) X ∧ AllocationNear r X0 X)

/-- Lemma 4.3. -/
def allocationLossIdentitySpec : Prop :=
  ∀ v A k labor alpha beta : FirmType → ℝ,
    (∀ i, 0 < v i ∧ 0 < A i ∧ 0 < k i ∧ 0 < labor i) →
    0 < alpha FirmType.H → 0 < beta FirmType.H →
    alpha FirmType.H + beta FirmType.H < 1 →
    let a := alpha FirmType.H
    let b := beta FirmType.H
    let d := 1 - a - b
    let L := ∑ i, v i * labor i
    let G := ∑ i, v i * A i ^ (1 / (1 - b)) * k i ^ (a / (1 - b))
    let K := ∑ i, v i * k i
    let ZA := ∑ i, v i * A i ^ (1 / d)
    let Y := L ^ b * G ^ (1 - b)
    let Yeff := K ^ a * L ^ b * ZA ^ d
    let loss := a * Real.log K + d * Real.log ZA - (1 - b) * Real.log G
    (∀ i, labor i = L * (A i ^ (1 / (1 - b)) * k i ^ (a / (1 - b))) / G) →
    Y = L ^ b * G ^ (1 - b) ∧ Yeff = K ^ a * L ^ b * ZA ^ d ∧ 0 ≤ loss

/-- Proposition 4.4. -/
def oppositeBranchAllocationSpec : Prop :=
  ∃ (S : Type) (_ : Fintype S) (_ : DecidableEq S)
      (P : Primitives S) (I : InheritedState) (X0 XS XB : Allocation S),
    SameInheritedAndPrimitives P P I I ∧
    CompetitiveEquilibrium P I XS ∧ CompetitiveEquilibrium P I XB ∧
    DateZeroSlackBorrower P XS FirmType.L ∧ DateZeroBindingBorrower P XB FirmType.L ∧
    XS.loanRate 0 (rootHistory P.tree) < X0.loanRate 0 (rootHistory P.tree) ∧
    XB.loanRate 0 (rootHistory P.tree) < X0.loanRate 0 (rootHistory P.tree) ∧
    X0.loan FirmType.H 0 (rootHistory P.tree) < XS.loan FirmType.H 0 (rootHistory P.tree) ∧
    X0.loan FirmType.H 0 (rootHistory P.tree) < XB.loan FirmType.H 0 (rootHistory P.tree) ∧
    XS.capital FirmType.H 1 (childHistory (rootHistory P.tree) P.tree.initial) /
        XS.capital FirmType.L 1 (childHistory (rootHistory P.tree) P.tree.initial) >
      X0.capital FirmType.H 1 (childHistory (rootHistory P.tree) P.tree.initial) /
        X0.capital FirmType.L 1 (childHistory (rootHistory P.tree) P.tree.initial) ∧
    XB.capital FirmType.H 1 (childHistory (rootHistory P.tree) P.tree.initial) /
        XB.capital FirmType.L 1 (childHistory (rootHistory P.tree) P.tree.initial) <
      X0.capital FirmType.H 1 (childHistory (rootHistory P.tree) P.tree.initial) /
        X0.capital FirmType.L 1 (childHistory (rootHistory P.tree) P.tree.initial)

/-- Proposition 4.5.  The strict risk/intervention wedge and endogenous child
minimum are explicit. -/
def riskyBranchPersistenceSpec : Prop :=
  ∃ hStar cStar : ℝ, 0 < hStar ∧ 0 < cStar ∧
    ∀ h eta, -hStar < h → h < 0 → 0 < eta → eta < cStar * |h| →
    ∃ (S : Type) (_ : Fintype S) (_ : DecidableEq S)
        (P : Primitives S) (I : InheritedState) (XS XB : Allocation S),
      CompetitiveEquilibrium P I XS ∧ CompetitiveEquilibrium P I XB ∧ XS ≠ XB ∧
      DateZeroSlackBorrower P XS FirmType.L ∧
      DateZeroBindingBorrower P XB FirmType.L ∧
      DateZeroBindingBorrower P XB FirmType.H ∧
      RestrictedFromDate P XS FirmType.H 1 ∧ RestrictedFromDate P XS FirmType.L 1 ∧
      RestrictedFromDate P XB FirmType.H 1 ∧ RestrictedFromDate P XB FirmType.L 1 ∧
      (∀ X ∈ ({XS, XB} : Set (Allocation S)), ∀ t h,
        ∃ value, IsWorstChildValue (t := t)
          (fun s ↦ X.inflation (t + 1) (childHistory h s) *
            X.capitalPrice (t + 1) (childHistory h s)) value)

/-! ## Appendix results, in source order -/

def steadyStatePositiveSpec : Prop :=
  ∀ (u c wealth q theta depreciation loanRate : FirmType → ℝ),
    (∀ i, 0 < u i ∧ 0 < c i ∧ 0 < wealth i ∧ 0 ≤ theta i ∧ theta i < 1 ∧
      0 < loanRate i ∧ q i > theta i * depreciation i * q i / loanRate i)

def realClosureSpec : Prop :=
  ∀ chiW L0 C0 phi sigmaW alpha beta d : ℝ,
    0 < chiW → 0 < L0 → 0 < C0 → 0 < d →
    let pw := 1 + ((1 - alpha) * phi + beta * sigmaW) / d
    0 < pw →
    ∃! w : ℝ, 0 < w ∧ w = (chiW * L0 ^ phi * C0 ^ sigmaW) ^ (1 / pw)

def bankRetentionSpec : Prop :=
  ∀ betaW gB etaB,
    betaW * gB > 1 → betaW * (1 - etaB) * gB < 1 →
    let value := betaW * etaB * gB / (1 - betaW * (1 - etaB) * gB)
    value > 1 ∧ ∀ equity retained, 0 ≤ retained → retained ≤ equity →
      equity + (value - 1) * retained ≤ equity + (value - 1) * equity ∧
      (equity + (value - 1) * retained = equity + (value - 1) * equity ↔
        retained = equity) ∧ equity - equity = 0

def stationaryExistenceSpec : Prop :=
  ∃ (S : Type) (_ : Fintype S) (_ : DecidableEq S)
      (P : Primitives S) (I : InheritedState) (X : Allocation S),
    CompetitiveEquilibrium P I X ∧
    RestrictedFromDate P X FirmType.H 0 ∧ RestrictedFromDate P X FirmType.L 0 ∧
    (∀ t h, X.bankRetainedEquity t h = X.bankEquity t h ∧ X.bankDividend t h = 0) ∧
    UniformlyBounded (fun t ↦ P.tree.expectationAt t (X.bankEquity t))

def steadyStateEfficiencyFactorSpec : Prop :=
  ∀ (mass useCost : FirmType → ℝ) (alpha beta x y Y Yeff : ℝ),
    (∀ i, 0 < mass i ∧ 0 < useCost i) → 0 < Yeff →
    Y / Yeff =
      (∑ i, mass i * useCost i ^ (-y)) ^ (1 - beta) /
        (∑ i, mass i * useCost i ^ (-x)) ^ alpha →
    Y / Yeff ≤ 1 ∧
      (Y / Yeff = 1 ↔
        ∀ i j, 0 < mass i → 0 < mass j → useCost i = useCost j)

def negativeComparativeSpec : Prop :=
  ∀ (thetaH thetaL R0 R1 : ℝ)
      (capitalShareH laborShareH efficiency : ℝ → ℝ),
    thetaH < thetaL → R1 < R0 →
    capitalShareH R1 < capitalShareH R0 ∧ laborShareH R1 < laborShareH R0 ∧
      efficiency R1 < efficiency R0 ∧
      Real.log (1 / efficiency R0) < Real.log (1 / efficiency R1)

def pledgeOrderingEfficiencySpec : Prop :=
  ∀ (thetaH thetaL R0 R1 : ℝ) (efficiency : ℝ → ℝ),
    R1 < R0 →
    (thetaH ≠ thetaL → efficiency R1 < efficiency R0) ∧
    (thetaH = thetaL → ∀ R, efficiency R = 1)

def dynamicCreditSupplySpec : Prop :=
  ∀ (kappaD bankFace : ℝ) (equity reserves inflation loans : ℝ → ℝ) (x : ℝ),
    (∀ s, loans s = (1 + kappaD) * equity s - reserves s) →
    (∀ s, equity s = bankFace / inflation s) → inflation x ≠ 0 →
    DifferentiableAt ℝ equity x → DifferentiableAt ℝ reserves x →
    DifferentiableAt ℝ inflation x →
    HasDerivAt (fun m ↦ (1 + kappaD) * equity x - m) (-1) (reserves x) ∧
    deriv loans x = (1 + kappaD) * deriv equity x - deriv reserves x ∧
    deriv equity x = -equity x * deriv inflation x / inflation x

def finiteMinimumDirectionalDerivativeSpec : Prop :=
  ∀ {ι : Type*} [Fintype ι] [Nonempty ι] (f : ι → ℝ → ℝ) x v,
    (∀ i, DifferentiableAt ℝ (f i) x) →
    RightDirectionalDerivativeAt (finiteMinimum f) x v
      (finiteMinimum (fun i _ ↦ deriv (f i) x * v) 0) ∧
    (DifferentiableAt ℝ (finiteMinimum f) x ↔
      ∀ i j, ActiveAt f x i → ActiveAt f x j → deriv (f i) x = deriv (f j) x)

def slackCreditSupplySpec : Prop :=
  ∀ (equity reserves reserveRatio loans : ℝ → ℝ) (x : ℝ),
    0 < reserveRatio x → reserveRatio x < 1 →
    (∀ s, loans s = equity s + (1 / reserveRatio s - 1) * reserves s) →
    DifferentiableAt ℝ equity x → DifferentiableAt ℝ reserves x →
    DifferentiableAt ℝ reserveRatio x →
    HasDerivAt (fun m ↦ equity x + (1 / reserveRatio x - 1) * m)
      ((1 - reserveRatio x) / reserveRatio x) (reserves x) ∧
    deriv loans x = deriv equity x + (1 / reserveRatio x - 1) * deriv reserves x -
      reserves x / (reserveRatio x) ^ 2 * deriv reserveRatio x

def slackDepositPriceRegularitySpec : Prop :=
  ∀ rho xi zeta : ℝ,
    0 ≤ rho → rho < 1 → xi > rho → 0 < zeta →
    ∀ residual : ℝ → ℝ,
      (∀ theta, theta ∈ Set.Ioo (0 : ℝ) 1 → 0 < deriv residual theta) →
      (∀ x y, x ∈ Set.Ioo (0 : ℝ) 1 → y ∈ Set.Ioo (0 : ℝ) 1 →
        residual x = 0 → residual y = 0 → x = y) ∧
      ∀ theta, theta ∈ Set.Ioo (0 : ℝ) 1 → residual theta = 0 →
        HasDerivAt residual (deriv residual theta) theta

def statewiseCollateralSpec : Prop :=
  ∀ {J : Type*} [Fintype J] [Nonempty J]
      (loanRate loan capitalNext : ℝ) (liquidation : J → ℝ),
    0 ≤ capitalNext →
    (loanRate * loan ≤ finiteMinimum (fun j _ ↦ liquidation j) 0 * capitalNext ↔
      ∀ j, loanRate * loan ≤ liquidation j * capitalNext)

def stochasticPartialHSpec : Prop :=
  ∀ capitalDemand : ℝ → ℝ, ∀ loanRate,
    DifferentiableAt ℝ capitalDemand loanRate → deriv capitalDemand loanRate < 0 →
    ∀ lowerRate, lowerRate < loanRate → capitalDemand loanRate < capitalDemand lowerRate

def boundedBankContinuationSpec : Prop :=
  ∀ gamma etaB value : ℕ → ℝ,
    ∀ lower upper, 1 < lower → (∀ t, lower ≤ gamma t ∧ gamma t ≤ upper) →
    (1 - etaB 0) * upper < 1 →
    (∀ t, value t = etaB t * gamma t + (1 - etaB t) * gamma t * value (t + 1)) →
    UniformlyBounded value →
    (∀ t, 1 < value t) ∧
      (∀ t, etaB t * lower / (1 - (1 - etaB t) * lower) ≤ value t) ∧
      ∀ other, UniformlyBounded other →
        (∀ t, other t = etaB t * gamma t +
          (1 - etaB t) * gamma t * other (t + 1)) → other = value

def noPermanentSaverSpec : Prop :=
  ∀ betaE betaW Zc : ℕ → ℝ,
    0 < betaE 0 → betaE 0 < betaW 0 → betaW 0 < 1 →
    UniformlyBounded Zc →
    ¬ ((∀ t, 0 < Zc t) ∧
      (∀ t, Zc (t + 1) = Zc t / betaE t) ∧
      (∀ t, Zc (t + 1) = Zc t / betaW t))

def nominalFaceIdentitySpec : Prop :=
  ∀ (mass : FirmType → ℝ) (bankScale : ℝ)
      (workerFace governmentFace bankFace householdDeposits householdBonds
        depositRate bondRate bankLoans bankDeposits firmDeposits reservesPost
        facilityBorrowing reserveRate facilityRate loanRate : ℕ → ℝ)
      (firmFace : FirmType → ℕ → ℝ),
    bankScale ≠ 0 →
    workerFace 0 = (∑ i, mass i * firmFace i 0) + governmentFace 0 -
      bankFace 0 / bankScale →
    (∀ t, workerFace (t + 1) = depositRate t * householdDeposits t +
      bondRate t * householdBonds t) →
    (∀ t, (∑ i, mass i * firmFace i (t + 1)) =
      loanRate t * bankLoans t - depositRate t * firmDeposits t) →
    (∀ t, governmentFace (t + 1) = bondRate t * householdBonds t +
      reserveRate t * reservesPost t - facilityRate t * facilityBorrowing t) →
    (∀ t, bankFace (t + 1) / bankScale = loanRate t * bankLoans t +
      reserveRate t * reservesPost t - depositRate t * bankDeposits t -
      facilityRate t * facilityBorrowing t) →
    (∀ t, bankDeposits t = householdDeposits t + firmDeposits t) →
    ∀ t, workerFace t = (∑ i, mass i * firmFace i t) + governmentFace t -
      bankFace t / bankScale

def householdBudgetReconstructionSpec : Prop :=
  ∀ {S : Type*} [Fintype S] [DecidableEq S]
      (P : Primitives S) (I : InheritedState) (X : Allocation S),
    (∀ i, FirmFeasible P I X i (firmPlanOfAllocation X i)) →
    BankBalance P X → SettlementClears P X → CreditClears P X → DepositsClear P X →
    CapitalClears P I X → LaborClears P X → FiscalClosure P I X →
    AccountingIdentities P X →
    (ResourceClears P X ↔ HouseholdFeasible P I X (householdPlanOfAllocation X))

def commonPledgeStateSpec : Prop :=
  ∀ faceH faceL thetaH thetaL capitalH capitalL J,
    0 < thetaH → 0 < thetaL → 0 < capitalH → 0 < capitalL →
    faceH = thetaH * capitalH * J → faceL = thetaL * capitalL * J →
    faceH / (thetaH * capitalH) = J ∧ faceL / (thetaL * capitalL) = J

def stableProjectionSpec : Prop :=
  ∀ (stableSpace : Submodule ℝ (Fin 16 → ℝ))
      (stateProjection : (Fin 16 → ℝ) →ₗ[ℝ] (Fin 6 → ℝ)),
    ((∀ x, ∃! y : stableSpace, stateProjection y = x) ↔
      Module.finrank ℝ stableSpace = 6 ∧
      Module.finrank ℝ (LinearMap.range (stateProjection.domRestrict stableSpace)) = 6) ∧
    (6 < Module.finrank ℝ stableSpace →
      Module.finrank ℝ (LinearMap.range (stateProjection.domRestrict stableSpace)) = 6 →
      Module.finrank ℝ (LinearMap.ker (stateProjection.domRestrict stableSpace)) =
        Module.finrank ℝ stableSpace - 6) ∧
    (Module.finrank ℝ (LinearMap.range (stateProjection.domRestrict stableSpace)) < 6 →
      LinearMap.range (stateProjection.domRestrict stableSpace) ≠ ⊤)

def boundedBoundaryInverseSpec : Prop :=
  ∀ L : (ℕ → ℝ) → (ℕ → ℝ),
    SequenceOperatorHasBoundedInverse L

def nonlinearLocalPathSpec : Prop :=
  ∀ F : ℝ → ℝ → ℝ, ∀ forcing initial : ℕ → ℝ,
    F 0 0 = 0 →
    ∃ r delta : ℝ, 0 < r ∧ 0 < delta ∧
      (∀ e x0, UniformlyBounded e → |x0| < delta →
        ∃! y : ℕ → ℝ,
          UniformlyBounded y ∧ (∀ t, F (y t) (y (t + 1)) = e t) ∧ y 0 = x0) ∧
      ∀ nu : ℝ, 0 < nu → nu < 1 →
        ∃ C : ℝ, 0 ≤ C ∧ ∀ (x0 : ℝ) (y : ℕ → ℝ),
          (∀ t, F (y t) (y (t + 1)) = 0) → y 0 = x0 →
          ∀ t, |y t| ≤ C * nu ^ t * |x0|

def firmSufficiencyInfiniteSpec : Prop :=
  ∀ {S : Type*} [Fintype S] [DecidableEq S]
      (P : Primitives S) (I : InheritedState) (X : Allocation S) (i : FirmType),
    PositiveDomain P X →
    FirmFeasible P I X i (firmPlanOfAllocation X i) →
    FirmObjectiveWellDefined P (firmPlanOfAllocation X i) →
    FirmLaborOptimal P I X i → FirmOperatingProfitConcave P X i →
    FirmPositiveNetCapitalCost P X i → GeneralFirmFinancialKKT P X i →
    (FirmSourceTerminalCondition P X (firmPlanOfAllocation X i) →
      FirmOptimal P I X i) ∧
    (FirmValuedPortfolioBounds P X (firmPlanOfAllocation X i) →
      FirmSourceTerminalCondition P X (firmPlanOfAllocation X i))

def retailLocalSufficiencySpec : Prop :=
  ∀ {S : Type*} [Fintype S] [DecidableEq S]
      (P : Primitives S) (X : Allocation S),
    PositiveDomain P X → RetailObjectiveWellDefined P X (retailerPlanOfAllocation X) →
    X.retailerLogRelativePrice = (fun _ _ ↦ 0) → RetailOptimal P X

def affineRiskCandidateSpec : Prop :=
  ∀ linearPart impact riskMean candidate : ℕ → ℝ,
    (∀ t, candidate t = linearPart t + impact t - riskMean t) →
    UniformlyBounded linearPart → UniformlyBounded impact → UniformlyBounded riskMean →
    UniformlyBounded candidate ∧
      ∀ other, (∀ t, other t = linearPart t + impact t - riskMean t) → other = candidate

def treeComparisonBoundSpec : Prop :=
  ∀ B : (ℕ → ℝ) → (ℕ → ℝ), ∀ N : ℕ, ∀ qN : ℝ,
    (∀ v M, (∀ t, |v t| ≤ M) → ∀ t, |(B^[N]) v t| ≤ qN * M) →
    qN < 1 → SequenceOperatorHasBoundedInverse (fun v ↦ v - B v)

def stochasticSelectedInverseSpec : Prop :=
  ∀ L : (ℕ → ℝ) → (ℕ → ℝ),
    SequenceOperatorHasBoundedInverse L ∧
      ∀ b, BoundedSequence b → ∃! y, BoundedSequence y ∧ L y = b

def selectedNonlinearFamilySpec : Prop :=
  ∀ residual : (ℕ → ℝ) → ℝ → ℝ → (ℕ → ℝ),
    ∃ radius : ℝ, 0 < radius ∧
      ∀ x0 eta, |x0| < radius → |eta| < radius →
      ∃! y, BoundedSequence y ∧ y 0 = x0 ∧
        residual y x0 eta = (fun _ ↦ 0)

def globalStochasticPriceOptimalitySpec : Prop :=
  ∀ {S : Type*} [Fintype S] [DecidableEq S]
      (P : Primitives S) (X : Allocation S) (markupLower priceBand : ℝ),
    P.priceElasticity = 6 → 4 / 5 < markupLower →
    0 < 5 * markupLower - 4 - P.priceAdjustmentCost / 2 * priceBand ^ 2 →
    (∀ t h, markupLower ≤ X.inputPrice t h ∧
      |X.inflation t h - 1| ≤ priceBand) →
    UniformlyBounded (fun t ↦ P.tree.expectationAt t (X.output t)) →
    UniformlyPositive (fun t ↦ P.tree.expectationAt t (X.output t)) →
    UniformlyBounded (fun t ↦ P.tree.expectationAt t (X.workerConsumption t)) →
    UniformlyPositive (fun t ↦ P.tree.expectationAt t (X.workerConsumption t)) →
    X.retailerLogRelativePrice = (fun _ _ ↦ 0) →
    RetailObjectiveWellDefined P X (retailerPlanOfAllocation X) →
    RetailOptimal P X ∧
      ∀ p, RetailObjectiveWellDefined P X p →
        (∃ t h, 0 < P.tree.historyWeight t h ∧ p.logRelativePrice t h ≠ 0) →
        RetailPayoff P X p < RetailPayoff P X (retailerPlanOfAllocation X)

def validatedTreeInverseSpec : Prop :=
  ∀ principal error : (ℕ → ℝ) → (ℕ → ℝ), ∀ gammaError,
    SequenceOperatorHasBoundedInverse principal → gammaError < 1 →
    SequenceOperatorHasBoundedInverse (fun y ↦ principal y + error y)

def certifiedSmallRiskEquilibriumSpec : Prop :=
  ∀ eta, 0 < eta → eta ≤ (10 : ℝ) ^ (-31 : ℤ) →
    ∃ (S : Type) (_ : Fintype S) (_ : DecidableEq S)
        (P : Primitives S) (I : InheritedState) (X : Allocation S),
      CompetitiveEquilibrium P I X ∧
      UniformlyBounded (fun t ↦ P.tree.expectationAt t (X.output t)) ∧
      (∀ t h, ∃ value, IsWorstChildValue (t := t)
        (fun s ↦ X.inflation (t + 1) (childHistory h s) *
          X.capitalPrice (t + 1) (childHistory h s)) value) ∧
      FirmOptimal P I X FirmType.H ∧ FirmOptimal P I X FirmType.L ∧
      HouseholdOptimal P I X ∧ BankOptimal P I X ∧ RetailOptimal P X

def minimumUniformInverseSpec : Prop :=
  ∀ Lmin : (ℕ → ℝ) → (ℕ → ℝ),
    SequenceOperatorHasLipschitzInverse Lmin ((10 : ℝ) ^ 13) ∧
    ∀ forcing, BoundedSequence forcing →
      ∃! y, BoundedSequence y ∧ Lmin y = forcing

def certifiedEndogenousMinimumSpec : Prop :=
  ∀ eta, 0 < eta → eta ≤ (10 : ℝ) ^ (-23 : ℤ) →
    ∃ (S : Type) (_ : Fintype S) (_ : DecidableEq S)
        (P : Primitives S) (I : InheritedState) (X : Allocation S) (r : ℝ),
      0 < r ∧ CompetitiveEquilibrium P I X ∧
      DateZeroBindingBorrower P X FirmType.H ∧ DateZeroBindingBorrower P X FirmType.L ∧
      (∀ t h, ∃ value, IsWorstChildValue (t := t)
        (fun s ↦ X.inflation (t + 1) (childHistory h s) *
          X.capitalPrice (t + 1) (childHistory h s)) value) ∧
      ∀ Y, CompetitiveEquilibrium P I Y → AllocationNear r X Y → Y = X

def regimeTubeSpec : Prop :=
  ∀ betaE steadyLoanRate sigmaE r : ℝ,
    betaE * steadyLoanRate < 1 →
    r < Real.log (1 / (betaE * steadyLoanRate)) / (2 * sigmaE + 2) →
    ∀ loanRate collateral capital discount face dual : ℝ,
      0 < discount →
      |Real.log (loanRate / steadyLoanRate)| < r →
      0 ≤ collateral * capital - face → 0 ≤ dual →
      dual * (collateral * capital - face) = 0 →
      (∀ alternative, fundingCash loanRate loanRate alternative ≤
        fundingCash loanRate loanRate face + (discount + dual) * (alternative - face)) →
      face = collateral * capital ∧ 0 < face ∧ 0 < dual

def generalRegimeSufficiencySpec : Prop :=
  ∀ {S : Type*} [Fintype S] [DecidableEq S]
      (P : Primitives S) (I : InheritedState) (X : Allocation S) (i : FirmType),
    PositiveDomain P X →
    FirmFeasible P I X i (firmPlanOfAllocation X i) →
    FirmObjectiveWellDefined P (firmPlanOfAllocation X i) →
    FirmLaborOptimal P I X i → FirmOperatingProfitConcave P X i →
    GeneralFirmFinancialKKT P X i → FirmPositiveNetCapitalCost P X i →
    (FirmSourceTerminalCondition P X (firmPlanOfAllocation X i) →
      FirmOptimal P I X i) ∧
    (FirmValuedPortfolioBounds P X (firmPlanOfAllocation X i) →
      FirmSourceTerminalCondition P X (firmPlanOfAllocation X i))

def finitePrefixEquilibriumSpec : Prop :=
  ∀ {S : Type*} [Fintype S] [DecidableEq S]
      (P : Primitives S) (I : InheritedState) (X : Allocation S),
    PositiveDomain P X → (∀ i, FirmOptimal P I X i) → HouseholdOptimal P I X →
    BankOptimal P I X → RetailOptimal P X → CapitalProducerOptimal P X →
    BankBalance P X → SettlementClears P X → CreditClears P X → DepositsClear P X →
    CapitalClears P I X → LaborClears P X → ResourceClears P X →
    FiscalClosure P I X → AccountingIdentities P X → CompetitiveEquilibrium P I X

def finiteSlackSpellSpec : Prop :=
  ∀ lower upper a betaW betaE : ℝ, ∀ ratio dual : ℕ → ℝ,
    0 < lower → (∀ t, lower ≤ ratio t ∧ ratio t ≤ upper) →
    a > 1 → 0 < betaE →
    a ≤ betaW / betaE → dual 0 = 0 →
    (∀ t, dual t = 0 → a * ratio t ≤ ratio (t + 1)) →
    ∃ tau : ℕ, 0 < dual tau ∧ (∀ t, t < tau → dual t = 0) ∧
      (tau : ℝ) ≤ (upper - ratio 0) / ((a - 1) * lower)

def pledgeSelectionComparativeSpec : Prop :=
  ∀ nH nL q thetaH thetaL Q loanRate : ℝ,
    0 < loanRate → q > thetaH * Q / loanRate → q > thetaL * Q / loanRate →
    let wH := nH / (q - thetaH * Q / loanRate) ^ 2
    let wL := nL / (q - thetaL * Q / loanRate) ^ 2
    let dq := -Q / loanRate ^ 2 * (wH * thetaH + wL * thetaL) / (wH + wL)
    let dkH := -Q / loanRate ^ 2 * wH * wL * (thetaH - thetaL) / (wH + wL)
    dq = -Q / loanRate ^ 2 * (wH * thetaH + wL * thetaL) / (wH + wL) ∧
      dkH = -Q / loanRate ^ 2 * wH * wL * (thetaH - thetaL) / (wH + wL) ∧
      (dkH < 0 ↔ thetaH > thetaL)

def positiveMixedChannelSpec : Prop :=
  ∀ vH vL WH WL thetaH Q loanRate kH : ℝ,
    0 < vH → 0 < vL → 0 < WH → 0 < WL → 0 < thetaH → 0 < Q →
    0 < loanRate →
    let dq := -vH * WH * thetaH * Q /
      (loanRate ^ 2 * (vH * WH + vL * WL))
    let dkH := -WH * vL * WL * thetaH * Q /
      (loanRate ^ 2 * (vH * WH + vL * WL))
    let dbH := thetaH * Q * (dkH / loanRate - kH / loanRate ^ 2)
    dq < 0 ∧ dkH < 0 ∧ dbH < 0

def capitalCreationChannelSpec : Prop :=
  ∀ vH vL WH WL thetaH Q loanRate supplySlope : ℝ,
    0 < vH → 0 < vL → 0 < WH → 0 < WL → 0 < thetaH → 0 < Q →
    0 < loanRate → 0 < supplySlope →
    let dq := -vH * WH * thetaH * Q /
      (loanRate ^ 2 * (vH * WH + vL * WL + supplySlope))
    let dkH := -WH * thetaH * Q * (vL * WL + supplySlope) /
      (loanRate ^ 2 * (vH * WH + vL * WL + supplySlope))
    dq < 0 ∧ dkH < 0

def crraHDemandSpec : Prop :=
  ∀ capitalDemand : ℝ → ℝ, ∀ p,
    DifferentiableAt ℝ capitalDemand p → deriv capitalDemand p < 0 →
    StrictAntiOn capitalDemand (Set.Ioi (0 : ℝ))

def crraPositiveMixedSpec : Prop :=
  ∀ vH vL WHtilde WL thetaH Q loanRate : ℝ,
    0 < vH → 0 < vL → 0 < WHtilde → 0 < WL → 0 < thetaH → 0 < Q →
    0 < loanRate →
    let dq := -vH * WHtilde * thetaH * Q /
      (loanRate ^ 2 * (vH * WHtilde + vL * WL))
    let dkH := -WHtilde * vL * WL * thetaH * Q /
      (loanRate ^ 2 * (vH * WHtilde + vL * WL))
    dq < 0 ∧ dkH < 0

def twoRateImplementationSpec : Prop :=
  ∀ loanRate depositRate rho x matchingCost : ℝ,
    loanRate > depositRate → 0 < depositRate → 0 ≤ rho → rho < 1 →
    x > matchingCost → 0 < matchingCost →
    ∃! reserveRate : ℝ, 0 < reserveRate ∧ reserveRate < depositRate ∧
      loanRate - depositRate = (loanRate - reserveRate) / x *
        (rho * (x - matchingCost) + matchingCost * depositRate / reserveRate)

def closedTwoDateEquilibriumSpec : Prop :=
  ∃ (S : Type) (_ : Fintype S) (_ : DecidableEq S)
      (P : Primitives S) (I : InheritedState) (X : Allocation S),
    CompetitiveEquilibrium P I X ∧
    P.productivity FirmType.L < P.productivity FirmType.H ∧
    I.capital FirmType.H < I.capital FirmType.L ∧
    P.pledgeability FirmType.H < P.pledgeability FirmType.L ∧
    DateZeroBindingBorrower P X FirmType.H ∧
    (∀ h : History S 0, X.loan FirmType.L 0 h = 0 ∧
      0 < X.firmDeposit FirmType.L 0 h) ∧
    BankOptimal P I X ∧ HouseholdOptimal P I X ∧
    BankBalance P X ∧ CreditClears P X ∧ DepositsClear P X ∧
    CapitalClears P I X ∧ ResourceClears P X ∧ FiscalClosure P I X

end Ventura26LiquidityAllocation
