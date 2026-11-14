import Ventura26LiquidityAllocation.StationaryPrivateFeasibilityCandidate

/-!
# Expectativas y descuento estacionarios: PROPUESTA SIN COMPILAR

Proyecto: alejandroventuraventurameza-tech/ai-project.
Rama: work/chat-continuity.
Commit: 16e24fe828a5a0002ef13bb82bae9e295f190f86.
Base AppliedModelingLib: 194edcc95df74806a39b961d10dedddc6e730cce.
Lean previsto: leanprover/lean4:v4.30.0-rc2.
Mathlib: 5450b53e5ddc75d46418fabb605edbf36bd0beb6.
Destino propuesto: papers/Ventura26LiquidityAllocation/StationaryTerminalFoundationCandidate.lean.
SHA256 de StationaryPrivateFeasibilityCandidate.lean utilizado:
30e72a942fe565a21a5f058b1e162d603b619cfa64de028cc5f4561f9ede91d4

Este modulo reutiliza los lemas conservados de pesos de historias y
`summable_tendsto_zero_of_abs_le_geometric`. No se ha ejecutado Lean.
La revision matematica y de interfaces no acredita compilacion ni kernel.

Argumento previo al codigo:
1. Cada peso del calendario es no negativo. Si una historia distinta de la
   canonica tuviera peso positivo, `localBridgeTree_historyWeight_pos_iff`
   la identificaria con aquella. Su peso, por tanto, es cero.
2. La suma finita que define la expectativa conserva solamente la historia
   canonica; `localBridgeHistory_weight_one` da peso uno a ese termino.
3. Los pesos de continuacion agregados y de pagos son no negativos y
   suman uno, por las normalizaciones primitivas y la descomposicion
   cronologica conservada. Las cotas puntuales se transmiten a su media.
4. Para 0 <= beta < 1 y cualquier C real, la sucesion beta^t*C satisface
   |beta^t*C| = |C|*beta^t. El lema geometrico conservado demuestra tanto
   sumabilidad como limite cero. No se impone C >= 0.

ALCANCE: herramientas comunes para las identidades posteriores de utilidad
y riqueza terminal. Este archivo no afirma optimalidad, condiciones de
equilibrio ni estacionariedad de la distribucion bancaria individual.
G permanece simbolico; no necesita una restriccion de signo en estos lemas.
-/

open scoped BigOperators
open Filter

namespace Ventura26LiquidityAllocation
namespace ProposedStationaryTerminalFoundation

open ProposedStationaryPrimitives

/-- En el calendario determinista toda historia no canonica tiene peso cero.
Se deduce de los lemas conservados, sin introducir una hipotesis probabilistica. -/
theorem localBridgeTree_historyWeight_eq_zero_of_ne
    (t : ℕ) (h : History LocalBridgePhase t)
    (hne : h ≠ localBridgeHistory t) :
    localBridgeTree.historyWeight t h = 0 := by
  have hnot : ¬ 0 < localBridgeTree.historyWeight t h := by
    intro hpos
    exact hne ((localBridgeTree_historyWeight_pos_iff t h).mp hpos)
  exact le_antisymm (le_of_not_gt hnot)
    (localBridgeTree_historyWeight_nonneg t h)

/-- Evaluacion literal de cualquier integrando en la unica historia con peso.
No exige que el integrando sea constante fuera de la historia admisible. -/
theorem localBridgeTree_expectationAt_eq
    (t : ℕ) (x : History LocalBridgePhase t → ℝ) :
    localBridgeTree.expectationAt t x = x (localBridgeHistory t) := by
  classical
  unfold FiniteMarkovTree.expectationAt
  calc
    (∑ h, localBridgeTree.historyWeight t h * x h) =
        localBridgeTree.historyWeight t (localBridgeHistory t) *
          x (localBridgeHistory t) := by
      apply Finset.sum_eq_single (localBridgeHistory t)
      · intro h _ hne
        rw [localBridgeTree_historyWeight_eq_zero_of_ne t h hne, zero_mul]
      · intro hnot
        exact (hnot (Finset.mem_univ _)).elim
    _ = x (localBridgeHistory t) := by
      rw [localBridgeHistory_weight_one, one_mul]

@[simp] theorem localBridgeTree_expectationAt_const (t : ℕ) (C : ℝ) :
    localBridgeTree.expectationAt t (fun _ ↦ C) = C := by
  exact localBridgeTree_expectationAt_eq t (fun _ ↦ C)

/-- El campo `tree` de la instancia conserva exactamente el calendario local. -/
theorem primitives_expectationAt_eq
    (G : ℝ) (t : ℕ) (x : History LocalBridgePhase t → ℝ) :
    (primitives G).tree.expectationAt t x = x (localBridgeHistory t) := by
  rw [primitives_tree G]
  exact localBridgeTree_expectationAt_eq t x

@[simp] theorem primitives_expectationAt_const (G : ℝ) (t : ℕ) (C : ℝ) :
    (primitives G).tree.expectationAt t (fun _ ↦ C) = C := by
  exact primitives_expectationAt_eq G t (fun _ ↦ C)

/-- Descuento geometrico de un coeficiente real de cualquier signo, incluido
el caso beta = 0. Se reutiliza la envolvente absoluta de la fuente conservada. -/
theorem fixed_beta_geometric (beta C : ℝ)
    (hbeta0 : 0 ≤ beta) (hbeta1 : beta < 1) :
    Summable (fun t : ℕ ↦ beta ^ t * C) ∧
      Tendsto (fun t : ℕ ↦ beta ^ t * C) atTop (nhds 0) := by
  apply summable_tendsto_zero_of_abs_le_geometric
    (fun t : ℕ ↦ beta ^ t * C) |C| beta
    (abs_nonneg C) hbeta0 hbeta1
  intro t
  rw [abs_mul, abs_of_nonneg (pow_nonneg hbeta0 t)]
  exact le_of_eq (mul_comm _ _)

/-- Version que mantiene visible la expectativa finita usada por los
objetivos y los terminos terminales literales de empresas y hogar. -/
theorem fixed_beta_expectation_geometric (G beta C : ℝ)
    (hbeta0 : 0 ≤ beta) (hbeta1 : beta < 1) :
    Summable (fun t : ℕ ↦
      beta ^ t * (primitives G).tree.expectationAt t (fun _ ↦ C)) ∧
      Tendsto (fun t : ℕ ↦
        beta ^ t * (primitives G).tree.expectationAt t (fun _ ↦ C))
        atTop (nhds 0) := by
  simpa only [primitives_expectationAt_const] using
    fixed_beta_geometric beta C hbeta0 hbeta1

/-! ## Pesos de continuacion sobre todas las historias soportadas -/


/-- La suma sobre el subtipo del soporte coincide con la suma primitiva. -/
theorem supportedPaymentProbability_sum_one
    {S : Type*} [Fintype S] (P : Primitives S) :
    (∑ omega : P.paymentSupport, P.paymentProbability omega) = 1 := by
  classical
  have hsum := P.payment_probability_sum_one
  rw [Finset.sum_subtype P.paymentSupport (fun x ↦ Iff.rfl)] at hsum
  exact hsum

/-- No negatividad de cada probabilidad condicional de historia agregada. -/
theorem continuationTransitionWeight_nonneg
    {S : Type*} [Fintype S] (T : FiniteMarkovTree S)
    (start : S) (n : ℕ) (future : Fin n → S) :
    0 ≤ continuationTransitionWeight T start n future := by
  induction n with
  | zero => simp [continuationTransitionWeight]
  | succ n ih =>
      change 0 ≤ continuationTransitionWeight T start n
        (fun j ↦ future j.succ) * T.transition _ _
      exact mul_nonneg (ih (fun j ↦ future j.succ)) (T.transition_nonneg _ _)

/-- La distribucion condicional de historias agregadas tiene masa uno,
incluso si la historia actual no procede del estado inicial del arbol. -/
theorem continuationTransitionWeight_sum_one
    {S : Type*} [Fintype S] (T : FiniteMarkovTree S)
    (start : S) (n : ℕ) :
    (∑ future : Fin n → S,
      continuationTransitionWeight T start n future) = 1 := by
  classical
  induction n generalizing start with
  | zero => simp [continuationTransitionWeight]
  | succ n ih =>
      rw [sum_pi_snoc]
      simp_rw [continuationTransitionWeight_snoc]
      calc
        (∑ s, ∑ future : Fin n → S,
            T.transition start s * continuationTransitionWeight T s n future) =
            ∑ s, T.transition start s *
              (∑ future : Fin n → S, continuationTransitionWeight T s n future) := by
          simp only [Finset.mul_sum]
        _ = ∑ s, T.transition start s := by simp only [ih, mul_one]
        _ = 1 := T.transition_sum_one start

/-- Cada producto de probabilidades de pagos soportados es no negativo. -/
theorem continuationPaymentWeight_nonneg
    {S : Type*} [Fintype S] (P : Primitives S) {n : ℕ}
    (payments : Fin n → P.paymentSupport) :
    0 ≤ continuationPaymentWeight P payments := by
  classical
  unfold continuationPaymentWeight
  exact Finset.prod_nonneg (fun j _ ↦ P.payment_probability_nonneg (payments j))

/-- La distribucion sobre todas las historias de pagos soportados tiene masa uno. -/
theorem continuationPaymentWeight_sum_one
    {S : Type*} [Fintype S] (P : Primitives S) (n : ℕ) :
    (∑ payments : Fin n → P.paymentSupport,
      continuationPaymentWeight P payments) = 1 := by
  classical
  induction n with
  | zero => simp [continuationPaymentWeight]
  | succ n ih =>
      rw [sum_pi_snoc]
      simp_rw [continuationPaymentWeight_snoc]
      calc
        (∑ omega : P.paymentSupport, ∑ payments : Fin n → P.paymentSupport,
            P.paymentProbability omega * continuationPaymentWeight P payments) =
            ∑ omega : P.paymentSupport, P.paymentProbability omega *
              (∑ payments : Fin n → P.paymentSupport,
                continuationPaymentWeight P payments) := by
          simp only [Finset.mul_sum]
        _ = ∑ omega : P.paymentSupport, P.paymentProbability omega := by
          rw [ih]
          simp only [mul_one]
        _ = 1 := supportedPaymentProbability_sum_one P

/-- Expectativa de una constante sobre el producto literal de historias.
La igualdad no convierte la riqueza individual en una constante. -/
theorem continuationJointWeight_const
    {S : Type*} [Fintype S] (P : Primitives S)
    (start : S) (n : ℕ) (C : ℝ) :
    (∑ future : Fin n → S, ∑ payments : Fin n → P.paymentSupport,
      continuationTransitionWeight P.tree start n future *
        continuationPaymentWeight P payments * C) = C := by
  classical
  calc
    _ = ∑ future : Fin n → S,
        (continuationTransitionWeight P.tree start n future * C) *
          (∑ payments : Fin n → P.paymentSupport,
            continuationPaymentWeight P payments) := by
      apply Finset.sum_congr rfl
      intro future _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro payments _
      ring
    _ = (∑ future : Fin n → S,
        continuationTransitionWeight P.tree start n future) * C := by
      rw [continuationPaymentWeight_sum_one]
      simp only [mul_one, Finset.sum_mul]
    _ = C := by rw [continuationTransitionWeight_sum_one, one_mul]

/-- Una cota puntual se conserva bajo los pesos de probabilidad literales. -/
theorem continuationJointWeighted_bounds
    {S : Type*} [Fintype S] (P : Primitives S)
    (start : S) (n : ℕ)
    (x : (Fin n → S) → (Fin n → P.paymentSupport) → ℝ) (C : ℝ)
    (hx : ∀ future payments, 0 ≤ x future payments ∧ x future payments ≤ C) :
    0 ≤ (∑ future : Fin n → S, ∑ payments : Fin n → P.paymentSupport,
      continuationTransitionWeight P.tree start n future *
        continuationPaymentWeight P payments * x future payments) ∧
    (∑ future : Fin n → S, ∑ payments : Fin n → P.paymentSupport,
      continuationTransitionWeight P.tree start n future *
        continuationPaymentWeight P payments * x future payments) ≤ C := by
  classical
  constructor
  · apply Finset.sum_nonneg
    intro future _
    apply Finset.sum_nonneg
    intro payments _
    exact mul_nonneg
      (mul_nonneg (continuationTransitionWeight_nonneg P.tree start n future)
        (continuationPaymentWeight_nonneg P payments)) (hx future payments).1
  · calc
      _ ≤ ∑ future : Fin n → S, ∑ payments : Fin n → P.paymentSupport,
          continuationTransitionWeight P.tree start n future *
            continuationPaymentWeight P payments * C := by
        apply Finset.sum_le_sum
        intro future _
        apply Finset.sum_le_sum
        intro payments _
        exact mul_le_mul_of_nonneg_left (hx future payments).2
          (mul_nonneg (continuationTransitionWeight_nonneg P.tree start n future)
            (continuationPaymentWeight_nonneg P payments))
      _ = C := continuationJointWeight_const P start n C

end ProposedStationaryTerminalFoundation
end Ventura26LiquidityAllocation
