import Ventura26LiquidityAllocation.StationaryBankPortfolioCandidate
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Topology.Order.OrderClosed

/-!
# Comparacion de continuaciones y valor alcanzado: PROPUESTA SIN COMPILAR

Proyecto: alejandroventuraventurameza-tech/ai-project.
Rama: work/chat-continuity.
Commit: 16e24fe828a5a0002ef13bb82bae9e295f190f86.
Base AppliedModelingLib: 194edcc95df74806a39b961d10dedddc6e730cce.
Lean previsto: leanprover/lean4:v4.30.0-rc2.
Mathlib: 5450b53e5ddc75d46418fabb605edbf36bd0beb6.

ESTADO: PROPUESTA SIN COMPILAR. No hay Lean, Lake, Elan ni ejecutor
Lean remoto disponible en esta sesion. Las demostraciones matematicas y
la revision estatica de interfaces no acreditan elaboracion, compilacion,
revision del kernel ni auditoria transitiva de axiomas.
Los archivos fuente fijados no se modifican. G permanece simbolico y
se conservan ambas ramas macroeconomicas S y B. Estos modulos se refieren
al padre estacionario; no certifican una continuacion perturbada.

Destino propuesto: papers/Ventura26LiquidityAllocation/StationaryBankContinuationCandidate.lean.
SHA256 de StationaryBankPortfolioCandidate.lean utilizado:
0ae2ff9c7b9e36714cb52c0b7eeeee2a518878accf09eed0cf9ed093869a4d03

Argumento matematico previo al codigo:
1. Para toda continuacion factible, su patrimonio real en el hijo es
   el retorno detallado de su propia cartera. La inflacion del padre es
   uno. La recurrencia se usa solo en transiciones positivas; los otros
   terminos tienen peso cero.
2. La media inicial satisface E[e1]<=R*(e0-d0). Las colas conservan la
   factibilidad fuente. Induccion sobre el horizonte finito, usando
   vB>=1 y su identidad escalar, da pago_hasta_N<=vB*e0.
3. La sumabilidad exigida por la fuente permite pasar al limite. No se
   impone una condicion terminal adicional a las alternativas.
4. Para el candidato, se conserva la recursion individual aleatoria
   e_(n+1)=(e_n/E)*g_omega. Al sumar los pesos de todas las historias de
   pagos se obtiene E[e_n]=E*R^n, sin igualar cada e_n con esa media.
5. El termino terminal fuente es exactamente E*(beta*(1-eta)*R)^n.
   El dividendo es cero y el pago de salida de fecha n+1 es 1/9 del
   termino terminal de esa fecha. La serie geometrica vale vB*E.

ALCANCE: cota para toda politica fuente y valor alcanzado por la
continuacion concreta. La condicion terminal del candidato sigue
siendo la de patrimonio superviviente; no se sustituye por una de V.
La integracion final en BankOptimal se hace en el modulo siguiente.
-/

open scoped BigOperators
open Filter

namespace Ventura26LiquidityAllocation
namespace ProposedStationaryBankOptimality

open ProposedStationaryRealScale
open ProposedStationaryPrimitives
open ProposedStationaryInheritedState
open ProposedStationaryLiteralAccounts
open ProposedStationaryTerminalFoundation
open ProposedStationaryTerminal

noncomputable def bankInitialDividend (G : ℝ)
    (p : BankContinuationPolicy LocalBridgePhase (primitives G).paymentSupport) : ℝ :=
  p.dividend 0 (fun j ↦ Fin.elim0 j) (fun j ↦ Fin.elim0 j)

/-- Media literal de e_1 sobre el primer estado y pago, sin incorporar
salida ni la renovacion del balance agregado. -/
noncomputable def bankNextEquityMean (G : ℝ) (t : ℕ)
    (h : History LocalBridgePhase t)
    (p : BankContinuationPolicy LocalBridgePhase (primitives G).paymentSupport) : ℝ :=
  ∑ s, ∑ omega : (primitives G).paymentSupport,
    (primitives G).tree.transition (currentState h) s *
      (primitives G).paymentProbability omega *
      p.equity 1 (fun _ ↦ s) (fun _ ↦ omega)

noncomputable def bankFinitePayoff (G : ℝ) (t : ℕ)
    (h : History LocalBridgePhase t)
    (p : BankContinuationPolicy LocalBridgePhase (primitives G).paymentSupport)
    (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.range (N + 1),
    bankContinuationPayoffTermAt (primitives G) (parentAllocation G) t h p n

theorem parent_bankInitialDividend_bounds (G : ℝ) (t : ℕ)
    (h : History LocalBridgePhase t) (equity : ℝ)
    (p : BankContinuationPolicy LocalBridgePhase (primitives G).paymentSupport)
    (hp : BankContinuationFeasibleAt (primitives G) (parentAllocation G)
      t h equity p) :
    0 ≤ equity ∧ 0 ≤ bankInitialDividend G p ∧ bankInitialDividend G p ≤ equity := by
  let emptyS : Fin 0 → LocalBridgePhase := fun j ↦ Fin.elim0 j
  let emptyOmega : Fin 0 → (primitives G).paymentSupport := fun j ↦ Fin.elim0 j
  have hzero := hp.2 0 emptyS emptyOmega (by trivial)
  rcases hzero with ⟨he, hd, hr, _hl, _hm, _hD, _hzero, _hrpos,
    hretention, _hbalance, _hcapD, _hcapL, _hRR, _hsettlement⟩
  have hinitial : p.equity 0 emptyS emptyOmega = equity := hp.1
  refine ⟨?_, hd, ?_⟩
  · simpa only [hinitial] using he
  · change p.dividend 0 emptyS emptyOmega ≤ equity
    linarith

/-- El promedio de patrimonio de fecha uno es el retorno de la cartera
inicial. Solo se usa la recurrencia en hijos de probabilidad positiva. -/
theorem parent_bankNextEquityMean_eq_expectedDetailed
    (G : ℝ) (t : ℕ) (h : History LocalBridgePhase t) (equity : ℝ)
    (p : BankContinuationPolicy LocalBridgePhase (primitives G).paymentSupport)
    (hp : BankContinuationFeasibleAt (primitives G) (parentAllocation G)
      t h equity p) :
    bankNextEquityMean G t h p =
      finiteSupportExpectation (primitives G).paymentSupport
        (primitives G).paymentProbability (fun omega ↦
          bankDetailedPortfolioReturnAt (primitives G) (parentAllocation G) t h
            ((parentAllocation G).bankTightness t h)
            (p.loans 0 (fun j ↦ Fin.elim0 j) (fun j ↦ Fin.elim0 j))
            (p.reserves 0 (fun j ↦ Fin.elim0 j) (fun j ↦ Fin.elim0 j))
            (p.deposits 0 (fun j ↦ Fin.elim0 j) (fun j ↦ Fin.elim0 j)) omega) := by
  classical
  let emptyS : Fin 0 → LocalBridgePhase := fun j ↦ Fin.elim0 j
  let emptyOmega : Fin 0 → (primitives G).paymentSupport := fun j ↦ Fin.elim0 j
  let ret : BankPayment → ℝ := fun omega ↦
    bankDetailedPortfolioReturnAt (primitives G) (parentAllocation G) t h
      ((parentAllocation G).bankTightness t h)
      (p.loans 0 emptyS emptyOmega) (p.reserves 0 emptyS emptyOmega)
      (p.deposits 0 emptyS emptyOmega) omega
  have hzero := hp.2 0 emptyS emptyOmega (by trivial)
  rcases hzero with ⟨_he, _hd, _hr, _hl, _hm, _hD, _hzero, _hrpos,
    _hretention, _hbalance, _hcapD, _hcapL, _hRR, hsettlement⟩
  have hchild : ∀ s, 0 < (primitives G).tree.transition (currentState h) s →
      ∀ omega : (primitives G).paymentSupport,
        p.equity 1 (fun _ ↦ s) (fun _ ↦ omega) = ret omega := by
    intro s hs omega
    have hs' : 0 < (primitives G).tree.transition
        (currentState (continuationHistory h emptyS)) s := by
      simpa only [continuationHistory_zero] using hs
    have heq := (hsettlement omega).2.2 s hs'
    have hfuture : childFutureHistory emptyS s = (fun _ ↦ s) := by
      funext j
      exact Fin.eq_zero j ▸ rfl
    have hpayment : childPaymentHistory emptyOmega omega = (fun _ ↦ omega) := by
      funext j
      exact Fin.eq_zero j ▸ rfl
    rw [hfuture, hpayment] at heq
    simpa only [Nat.add_zero, continuationHistory_zero, parent_inflation,
      div_one, ret] using heq
  unfold bankNextEquityMean
  calc
    _ = ∑ s, ∑ omega : (primitives G).paymentSupport,
        (primitives G).tree.transition (currentState h) s *
          (primitives G).paymentProbability omega * ret omega := by
      apply Finset.sum_congr rfl
      intro s _
      apply Finset.sum_congr rfl
      intro omega _
      by_cases hs : (primitives G).tree.transition (currentState h) s = 0
      · simp only [hs, zero_mul]
      · have hspos : 0 < (primitives G).tree.transition (currentState h) s :=
          lt_of_le_of_ne ((primitives G).tree.transition_nonneg _ _) (Ne.symm hs)
        rw [hchild s hspos omega]
    _ = ∑ omega : (primitives G).paymentSupport,
        (primitives G).paymentProbability omega * ret omega := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro omega _
      calc
        _ = (∑ s, (primitives G).tree.transition (currentState h) s) *
            ((primitives G).paymentProbability omega * ret omega) := by
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro s _
          ring
        _ = _ := by rw [(primitives G).tree.transition_sum_one, one_mul]
    _ = _ := by
      unfold finiteSupportExpectation
      rw [Finset.sum_subtype (primitives G).paymentSupport (fun _ ↦ Iff.rfl)]

/-- Cota de la media de e_1 derivada del soporte global de cartera y de
la retencion literal e_0-d_0; no es una hipotesis de Bellman. -/
theorem parent_bankNextEquityMean_le (G : ℝ) (t : ℕ)
    (h : History LocalBridgePhase t) (equity : ℝ)
    (p : BankContinuationPolicy LocalBridgePhase (primitives G).paymentSupport)
    (hp : BankContinuationFeasibleAt (primitives G) (parentAllocation G)
      t h equity p) :
    bankNextEquityMean G t h p ≤
      ProposedStationaryBank.loanRate * (equity - bankInitialDividend G p) := by
  let emptyS : Fin 0 → LocalBridgePhase := fun j ↦ Fin.elim0 j
  let emptyOmega : Fin 0 → (primitives G).paymentSupport := fun j ↦ Fin.elim0 j
  have hzero := hp.2 0 emptyS emptyOmega (by trivial)
  rcases hzero with ⟨_he, _hd, _hr, _hl, _hm, _hD, _hzero, _hrpos,
    hretention, hbalance, _hcapD, _hcapL, _hRR, _hsettlement⟩
  have hinitial : p.equity 0 emptyS emptyOmega = equity := hp.1
  have hretained : p.retainedEquity 0 emptyS emptyOmega =
      equity - bankInitialDividend G p := by
    simpa only [hinitial, bankInitialDividend] using hretention
  rw [parent_bankNextEquityMean_eq_expectedDetailed G t h equity p hp]
  have hbound := parent_bankExpectedDetailed_le_retained G t h
    (p.retainedEquity 0 emptyS emptyOmega) (p.loans 0 emptyS emptyOmega)
    (p.reserves 0 emptyS emptyOmega) (p.deposits 0 emptyS emptyOmega) hbalance
  simpa only [hretained] using hbound

private theorem bank_sum_range_succ_shift (f : ℕ → ℝ) (N : ℕ) :
    (∑ n ∈ Finset.range (N + 1), f n) =
      f 0 + ∑ n ∈ Finset.range N, f (n + 1) := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_range_succ, ih]
      conv_rhs => rw [Finset.sum_range_succ]
      ring

private theorem bank_sum_range_first_exit (a b c : ℝ) (f : ℕ → ℝ) (N : ℕ) :
    (∑ n ∈ Finset.range (N + 1), a * (b * f n + if n = 0 then c else 0)) =
      a * (b * (∑ n ∈ Finset.range (N + 1), f n) + c) := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_range_succ, ih]
      conv_rhs => rw [Finset.sum_range_succ]
      simp only [Nat.succ_ne_zero, if_false, add_zero]
      ring

theorem parent_bankFinitePayoff_zero (G : ℝ) (t : ℕ)
    (h : History LocalBridgePhase t)
    (p : BankContinuationPolicy LocalBridgePhase (primitives G).paymentSupport) :
    bankFinitePayoff G t h p 0 = bankInitialDividend G p := by
  have hc : 0 < (parentAllocation G).workerConsumption t h := by
    rw [parent_workerConsumption]
    exact workerConsumption_pos
  simpa only [bankFinitePayoff, Nat.zero_add, Finset.sum_range_one,
    bankInitialDividend] using
      bankContinuationPayoffTermAt_zero (primitives G) (parentAllocation G) t h p hc

/-- Descomposicion finita literal: el pago de salida aparece una vez,
ademas de los dividendos presentes y los objetivos de las colas supervivientes. -/
theorem parent_bankFinitePayoff_succ (G : ℝ) (t : ℕ)
    (h : History LocalBridgePhase t)
    (p : BankContinuationPolicy LocalBridgePhase (primitives G).paymentSupport)
    (N : ℕ) :
    bankFinitePayoff G t h p (N + 1) = bankInitialDividend G p +
      ∑ s, ∑ omega : (primitives G).paymentSupport,
        (primitives G).tree.transition (currentState h) s *
          (primitives G).paymentProbability omega * (99 / 100 : ℝ) *
          ((9 / 10 : ℝ) * bankFinitePayoff G (t + 1) (childHistory h s)
              (tailBankContinuationPolicy p s omega) N +
            (1 / 10 : ℝ) * p.equity 1 (fun _ ↦ s) (fun _ ↦ omega)) := by
  classical
  have hc : 0 < (parentAllocation G).workerConsumption t h := by
    rw [parent_workerConsumption]
    exact workerConsumption_pos
  have hchild : ∀ s, 0 < (primitives G).tree.transition (currentState h) s →
      0 < (parentAllocation G).workerConsumption (t + 1) (childHistory h s) := by
    intro s _
    rw [parent_workerConsumption]
    exact workerConsumption_pos
  have hrec (n : ℕ) :
      bankContinuationPayoffTermAt (primitives G) (parentAllocation G) t h p (n + 1) =
        ∑ s, ∑ omega : (primitives G).paymentSupport,
          (primitives G).tree.transition (currentState h) s *
            (primitives G).paymentProbability omega * (99 / 100 : ℝ) *
            ((9 / 10 : ℝ) * bankContinuationPayoffTermAt (primitives G)
                (parentAllocation G) (t + 1) (childHistory h s)
                (tailBankContinuationPolicy p s omega) n +
              if n = 0 then (1 / 10 : ℝ) *
                p.equity 1 (fun _ ↦ s) (fun _ ↦ omega) else 0) := by
    simpa only [parent_bankStochasticDiscount_eq, bank_survivalFactor_eq] using
      bankContinuationPayoffTermAt_succ (primitives G) (parentAllocation G)
        t h p n hchild
  unfold bankFinitePayoff
  rw [bank_sum_range_succ_shift,
    bankContinuationPayoffTermAt_zero (primitives G) (parentAllocation G) t h p hc]
  simp_rw [hrec]
  apply congrArg (fun z : ℝ ↦ bankInitialDividend G p + z)
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro omega _
  exact bank_sum_range_first_exit
    ((primitives G).tree.transition (currentState h) s *
      (primitives G).paymentProbability omega * (99 / 100 : ℝ))
    (9 / 10 : ℝ) ((1 / 10 : ℝ) *
      p.equity 1 (fun _ ↦ s) (fun _ ↦ omega))
    (fun n ↦ bankContinuationPayoffTermAt (primitives G) (parentAllocation G)
      (t + 1) (childHistory h s) (tailBankContinuationPolicy p s omega) n) N

/-- Induccion sobre el objetivo FINITO de cualquier politica factible.
El valor escalar se caracteriza explicitamente, sin asumir dominancia. -/
theorem parent_bankFinitePayoff_le (G value : ℝ)
    (hvalueOne : 1 ≤ value)
    (hvalue : value = (99 / 100 : ℝ) *
      ((9 / 10 : ℝ) * value + (1 / 10 : ℝ)) * ProposedStationaryBank.loanRate)
    (N : ℕ) (t : ℕ) (h : History LocalBridgePhase t) (equity : ℝ)
    (p : BankContinuationPolicy LocalBridgePhase (primitives G).paymentSupport)
    (hp : BankContinuationFeasibleAt (primitives G) (parentAllocation G)
      t h equity p) :
    bankFinitePayoff G t h p N ≤ value * equity := by
  classical
  induction N generalizing t h equity p with
  | zero =>
      rw [parent_bankFinitePayoff_zero]
      have hb := parent_bankInitialDividend_bounds G t h equity p hp
      calc
        bankInitialDividend G p ≤ equity := hb.2.2
        _ = 1 * equity := by ring
        _ ≤ value * equity := mul_le_mul_of_nonneg_right hvalueOne hb.1
  | succ N ih =>
      have hd := (parent_bankInitialDividend_bounds G t h equity p hp).2.1
      have hcoefficient : 0 ≤ (99 / 100 : ℝ) *
          ((9 / 10 : ℝ) * value + (1 / 10 : ℝ)) := by
        have hv : 0 ≤ value := le_trans (by norm_num) hvalueOne
        positivity
      rw [parent_bankFinitePayoff_succ]
      calc
        _ ≤ bankInitialDividend G p +
            ∑ s, ∑ omega : (primitives G).paymentSupport,
              (primitives G).tree.transition (currentState h) s *
                (primitives G).paymentProbability omega * (99 / 100 : ℝ) *
                ((9 / 10 : ℝ) *
                    (value * p.equity 1 (fun _ ↦ s) (fun _ ↦ omega)) +
                  (1 / 10 : ℝ) * p.equity 1 (fun _ ↦ s) (fun _ ↦ omega)) := by
          apply add_le_add_right
          apply Finset.sum_le_sum
          intro s _
          apply Finset.sum_le_sum
          intro omega _
          by_cases hs : (primitives G).tree.transition (currentState h) s = 0
          · simp only [hs, zero_mul, le_refl]
          · have hspos : 0 < (primitives G).tree.transition (currentState h) s :=
              lt_of_le_of_ne ((primitives G).tree.transition_nonneg _ _) (Ne.symm hs)
            have htail := tailBankContinuationPolicy_feasible
              (primitives G) (parentAllocation G) t h equity p hp s hspos omega
            have htailBound := ih (t + 1) (childHistory h s)
              (p.equity 1 (fun _ ↦ s) (fun _ ↦ omega))
              (tailBankContinuationPolicy p s omega) htail
            have hw : 0 ≤ (primitives G).tree.transition (currentState h) s *
                (primitives G).paymentProbability omega * (99 / 100 : ℝ) :=
              mul_nonneg (mul_nonneg ((primitives G).tree.transition_nonneg _ _)
                ((primitives G).payment_probability_nonneg omega)) (by norm_num)
            exact mul_le_mul_of_nonneg_left
              (add_le_add_left
                (mul_le_mul_of_nonneg_left htailBound
                  (show (0 : ℝ) ≤ 9 / 10 by norm_num)) _) hw
        _ = bankInitialDividend G p + (99 / 100 : ℝ) *
            ((9 / 10 : ℝ) * value + (1 / 10 : ℝ)) * bankNextEquityMean G t h p := by
          apply congrArg (fun z : ℝ ↦ bankInitialDividend G p + z)
          unfold bankNextEquityMean
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro s _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro omega _
          ring
        _ ≤ bankInitialDividend G p + (99 / 100 : ℝ) *
            ((9 / 10 : ℝ) * value + (1 / 10 : ℝ)) *
              (ProposedStationaryBank.loanRate * (equity - bankInitialDividend G p)) :=
          add_le_add_right (mul_le_mul_of_nonneg_left
            (parent_bankNextEquityMean_le G t h equity p hp) hcoefficient) _
        _ = bankInitialDividend G p + value * (equity - bankInitialDividend G p) := by
          rw [← mul_assoc, ← hvalue]
        _ ≤ value * equity := by
          have hloss : 0 ≤ (value - 1) * bankInitialDividend G p :=
            mul_nonneg (sub_nonneg.mpr hvalueOne) hd
          nlinarith

/-- Paso al objetivo infinito usando exclusivamente la sumabilidad que
la definicion fuente exige al competidor. No se impone TVC alternativa. -/
theorem parent_bankContinuationPayoff_le (G value : ℝ)
    (hvalueOne : 1 ≤ value)
    (hvalue : value = (99 / 100 : ℝ) *
      ((9 / 10 : ℝ) * value + (1 / 10 : ℝ)) * ProposedStationaryBank.loanRate)
    (t : ℕ) (h : History LocalBridgePhase t) (equity : ℝ)
    (p : BankContinuationPolicy LocalBridgePhase (primitives G).paymentSupport)
    (hp : BankContinuationFeasibleAt (primitives G) (parentAllocation G)
      t h equity p)
    (hpDefined : BankContinuationObjectiveWellDefinedAt
      (primitives G) (parentAllocation G) t h p) :
    bankContinuationPayoffAt (primitives G) (parentAllocation G) t h p ≤
      value * equity := by
  have hsum : Summable
      (bankContinuationPayoffTermAt (primitives G) (parentAllocation G) t h p) :=
    hpDefined
  have hpartial : Tendsto (fun N : ℕ ↦ bankFinitePayoff G t h p N)
      atTop (nhds (bankContinuationPayoffAt (primitives G) (parentAllocation G) t h p)) := by
    simpa only [bankFinitePayoff, bankContinuationPayoffAt, Function.comp_def] using
      hsum.hasSum.tendsto_sum_nat.comp (Filter.tendsto_add_atTop_nat 1)
  exact le_of_tendsto_of_tendsto' hpartial tendsto_const_nhds
    (fun N ↦ parent_bankFinitePayoff_le G value hvalueOne hvalue N t h equity p hp)

open ProposedStationaryRealScale
open ProposedStationaryPrimitives
open ProposedStationaryInheritedState
open ProposedStationaryLiteralAccounts
open ProposedStationaryPrivateFeasibility
open ProposedStationaryTerminalFoundation
open ProposedStationaryTerminal

/-- Separar el pago mas reciente en la suma sobre todas las historias.
La equivalencia `Fin.consEquiv` se consulta en la revision fijada de Mathlib. -/
theorem bank_sum_pi_cons {A : Type*} [Fintype A] {n : ℕ}
    (f : (Fin (n + 1) → A) → ℝ) :
    (∑ q, f q) = ∑ a, ∑ q : Fin n → A, f (Fin.cons a q) := by
  rw [← (Fin.consEquiv (fun _ : Fin (n + 1) ↦ A)).sum_comp f,
    Fintype.sum_prod_type] <;> rfl

theorem bank_paymentWeight_cons (G : ℝ) {n : ℕ}
    (payments : Fin n → (primitives G).paymentSupport)
    (omega : (primitives G).paymentSupport) :
    continuationPaymentWeight (primitives G) (Fin.cons omega payments) =
      (primitives G).paymentProbability omega *
        continuationPaymentWeight (primitives G) payments := by
  unfold continuationPaymentWeight
  rw [Fin.prod_univ_succ] <;>
    simp only [Fin.cons_zero, Fin.cons_succ]

/-- Recursion individual literal con retorno nominal igual al real porque
la inflacion del padre es uno. No se introduce salida o renovacion aqui. -/
theorem parent_bankEquity_cons
    (G : ℝ) (t : ℕ) (h : History LocalBridgePhase t) (n : ℕ)
    (future : Fin (n + 1) → LocalBridgePhase)
    (payments : Fin n → (primitives G).paymentSupport)
    (omega : (primitives G).paymentSupport) :
    (parentBankContinuation G t h).equity (n + 1) future
        (Fin.cons omega payments) =
      ((parentBankContinuation G t h).equity n
          (fun j ↦ future j.succ) payments / bankEquity) *
        bankGrossReturn (primitives G) (parentAllocation G) (commonBankPlan G)
          omega (t + n) (continuationHistory h (fun j ↦ future j.succ)) := by
  let previousFuture : Fin n → LocalBridgePhase := fun j ↦ future j.succ
  let H : History LocalBridgePhase (t + n) := continuationHistory h previousFuture
  let e := (parentBankContinuation G t h).equity n previousFuture payments
  have he : 0 < e :=
    (parent_bankContinuation_equity_bounds G t h n previousFuture payments).1
  have hscale : 0 < e / bankEquity := div_pos he bank_scale_pos.1
  change bankDetailedPortfolioReturnAt (primitives G) (parentAllocation G)
      (t + n) H ((parentAllocation G).bankTightness (t + n) H)
      ((e / (parentAllocation G).bankEquity (t + n) H) *
        (parentAllocation G).bankLoans (t + n) H)
      ((e / (parentAllocation G).bankEquity (t + n) H) *
        (parentAllocation G).reservesPrePayment (t + n) H)
      ((e / (parentAllocation G).bankEquity (t + n) H) *
        (parentAllocation G).bankDeposits (t + n) H) omega /
      (parentAllocation G).inflation (t + n + 1)
        (childHistory H (future 0)) = _
  rw [parent_bankEquity, parent_inflation, div_one]
  rw [bankDetailedPortfolioReturnAt_scale (primitives G) (parentAllocation G)
    (t + n) H ((parentAllocation G).bankTightness (t + n) H)
    ((parentAllocation G).bankLoans (t + n) H)
    ((parentAllocation G).reservesPrePayment (t + n) H)
    ((parentAllocation G).bankDeposits (t + n) H)
    (e / bankEquity) hscale omega]
  rw [← fullRetentionCommonBankPlan_grossReturn_eq_detailed
    (primitives G) (parentAllocation G) (t + n) H omega omega.property]
  rfl

/-- Media sobre pagos soportados del retorno del plan comun. -/
theorem parent_bankGrossReturn_supported_mean
    (G : ℝ) (t : ℕ) (h : History LocalBridgePhase t) :
    (∑ omega : (primitives G).paymentSupport,
      (primitives G).paymentProbability omega *
        bankGrossReturn (primitives G) (parentAllocation G) (commonBankPlan G)
          omega t h) = ProposedStationaryBank.loanRate * bankEquity := by
  have hmean := commonBankPlan_expectedGrossReturn G t h
  change (∑ omega ∈ (primitives G).paymentSupport,
    (primitives G).paymentProbability omega *
      bankGrossReturn (primitives G) (parentAllocation G) (commonBankPlan G)
        omega t h) = _ at hmean
  rw [Finset.sum_subtype (primitives G).paymentSupport (fun x ↦ Iff.rfl)] at hmean
  exact hmean

/-- Para cada historia agregada, la media sobre historias de pagos es E*R^n.
No se afirma que cada banco tenga ese patrimonio. -/
theorem parent_bankPaymentMeanEquity
    (G : ℝ) (t : ℕ) (h : History LocalBridgePhase t) (n : ℕ)
    (future : Fin n → LocalBridgePhase) :
    (∑ payments : Fin n → (primitives G).paymentSupport,
      continuationPaymentWeight (primitives G) payments *
        (parentBankContinuation G t h).equity n future payments) =
      bankEquity * ProposedStationaryBank.loanRate ^ n := by
  classical
  induction n with
  | zero =>
      have he : ∀ payments : Fin 0 → (primitives G).paymentSupport,
          (parentBankContinuation G t h).equity 0 future payments = bankEquity := by
        intro payments
        change (parentAllocation G).bankEquity t h = bankEquity
        exact parent_bankEquity G t h
      simp only [he, pow_zero, mul_one, ← Finset.sum_mul]
      rw [continuationPaymentWeight_sum_one, one_mul]
  | succ n ih =>
      let previousFuture : Fin n → LocalBridgePhase := fun j ↦ future j.succ
      let H : History LocalBridgePhase (t + n) := continuationHistory h previousFuture
      let e := fun payments : Fin n → (primitives G).paymentSupport ↦
        (parentBankContinuation G t h).equity n previousFuture payments
      let g := fun omega : (primitives G).paymentSupport ↦
        bankGrossReturn (primitives G) (parentAllocation G) (commonBankPlan G)
          omega (t + n) H
      rw [bank_sum_pi_cons]
      simp_rw [bank_paymentWeight_cons, parent_bankEquity_cons]
      change (∑ omega : (primitives G).paymentSupport,
        ∑ payments : Fin n → (primitives G).paymentSupport,
          ((primitives G).paymentProbability omega *
            continuationPaymentWeight (primitives G) payments) *
              ((e payments / bankEquity) * g omega)) = _
      calc
        _ = ∑ payments : Fin n → (primitives G).paymentSupport,
            (continuationPaymentWeight (primitives G) payments * e payments /
              bankEquity) *
              (∑ omega : (primitives G).paymentSupport,
                (primitives G).paymentProbability omega * g omega) := by
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro payments _
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro omega _
            ring
        _ = ∑ payments : Fin n → (primitives G).paymentSupport,
            (continuationPaymentWeight (primitives G) payments * e payments) *
              ProposedStationaryBank.loanRate := by
            have hg : (∑ omega : (primitives G).paymentSupport,
                (primitives G).paymentProbability omega * g omega) =
                ProposedStationaryBank.loanRate * bankEquity :=
              parent_bankGrossReturn_supported_mean G (t + n) H
            rw [hg]
            apply Finset.sum_congr rfl
            intro payments _
            field_simp [ne_of_gt bank_scale_pos.1] <;> ring
        _ = (bankEquity * ProposedStationaryBank.loanRate ^ n) *
            ProposedStationaryBank.loanRate := by
            rw [← Finset.sum_mul]
            rw [show (∑ payments : Fin n → (primitives G).paymentSupport,
                continuationPaymentWeight (primitives G) payments * e payments) =
                bankEquity * ProposedStationaryBank.loanRate ^ n from
              ih previousFuture]
        _ = bankEquity * ProposedStationaryBank.loanRate ^ (n + 1) := by
            rw [pow_succ]
            ring

/-- Promedio conjunto con los pesos literales de la fuente. -/
theorem parent_bankJointMeanEquity
    (G : ℝ) (t : ℕ) (h : History LocalBridgePhase t) (n : ℕ) :
    (∑ future : Fin n → LocalBridgePhase,
      ∑ payments : Fin n → (primitives G).paymentSupport,
        continuationTransitionWeight (primitives G).tree (currentState h) n future *
          continuationPaymentWeight (primitives G) payments *
          (parentBankContinuation G t h).equity n future payments) =
      bankEquity * ProposedStationaryBank.loanRate ^ n := by
  classical
  calc
    _ = ∑ future : Fin n → LocalBridgePhase,
        continuationTransitionWeight (primitives G).tree (currentState h) n future *
          (∑ payments : Fin n → (primitives G).paymentSupport,
            continuationPaymentWeight (primitives G) payments *
              (parentBankContinuation G t h).equity n future payments) := by
        apply Finset.sum_congr rfl
        intro future _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro payments _
        ring
    _ = (∑ future : Fin n → LocalBridgePhase,
        continuationTransitionWeight (primitives G).tree (currentState h) n future) *
          (bankEquity * ProposedStationaryBank.loanRate ^ n) := by
        simp only [parent_bankPaymentMeanEquity, Finset.sum_mul]
    _ = bankEquity * ProposedStationaryBank.loanRate ^ n := by
        rw [continuationTransitionWeight_sum_one, one_mul]

/-- Termino terminal exacto del candidato, obtenido de la media y del SDF.
La cota geometrica anterior sigue siendo valida, pero aqui hay igualdad. -/
theorem parent_bankSurvivingValue_exact
    (G : ℝ) (t : ℕ) (h : History LocalBridgePhase t) (n : ℕ) :
    bankSurvivingValueTermAt (primitives G) (parentAllocation G) t h
        (parentBankContinuation G t h) n =
      bankEquity * ((99 / 100 : ℝ) * (9 / 10) *
        ProposedStationaryBank.loanRate) ^ n := by
  classical
  unfold bankSurvivingValueTermAt
  simp only [parent_bankCumulativeSDF, bank_survivalFactor_eq]
  calc
    _ = ((99 / 100 : ℝ) ^ n * (9 / 10 : ℝ) ^ n) *
        (∑ future : Fin n → LocalBridgePhase,
          ∑ payments : Fin n → (primitives G).paymentSupport,
            continuationTransitionWeight (primitives G).tree (currentState h) n future *
              continuationPaymentWeight (primitives G) payments *
              (parentBankContinuation G t h).equity n future payments) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro future _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro payments _
        ring
    _ = bankEquity * ((99 / 100 : ℝ) * (9 / 10) *
        ProposedStationaryBank.loanRate) ^ n := by
        rw [parent_bankJointMeanEquity, mul_pow, mul_pow]
        ring

/-- El objetivo literal del candidato alcanza la pendiente de valor.
Se suman pagos de salida, no dividendos ficticios ni transferencias de entrada. -/
theorem parent_bankContinuation_payoff_eq_value
    (G : ℝ) (t : ℕ) (h : History LocalBridgePhase t) :
    bankContinuationPayoffAt (primitives G) (parentAllocation G) t h
      (parentBankContinuation G t h) = bankValueSlope * bankEquity := by
  let a : ℝ := (99 / 100 : ℝ) * (9 / 10) * ProposedStationaryBank.loanRate
  have ha : 0 ≤ a ∧ a < 1 :=
    ⟨bank_discounted_survival_return_bounds.1.le,
      bank_discounted_survival_return_bounds.2⟩
  have hgeo : Summable (fun n : ℕ ↦ a ^ n) :=
    summable_geometric_of_lt_one ha.1 ha.2
  have hsum : Summable (bankContinuationPayoffTermAt (primitives G)
      (parentAllocation G) t h (parentBankContinuation G t h)) :=
    (parent_bankContinuation_objective_and_terminal G t h).1
  have hterm : (fun n : ℕ ↦ bankContinuationPayoffTermAt (primitives G)
        (parentAllocation G) t h (parentBankContinuation G t h) (n + 1)) =
      (fun n : ℕ ↦ ((1 / 9 : ℝ) * bankEquity * a) * a ^ n) := by
    funext n
    rw [parent_bankPayoffTerm_succ, parent_bankSurvivingValue_exact]
    change (1 / 9 : ℝ) * (bankEquity * a ^ (n + 1)) = _
    rw [pow_succ]
    ring
  unfold bankContinuationPayoffAt
  rw [hsum.tsum_eq_zero_add, parent_bankPayoffTerm_zero, zero_add, hterm,
    hgeo.tsum_mul_left, tsum_geometric_of_lt_one ha.1 ha.2]
  dsimp only [a, bankValueSlope]
  field_simp [ne_of_gt bankValueSlope_den_pos] <;> ring

end ProposedStationaryBankOptimality
end Ventura26LiquidityAllocation
