import Ventura26LiquidityAllocation.EconomicModel

/-!
# Auditoria de la unicidad de la continuacion: PROPUESTA SIN COMPILAR

Proyecto: alejandroventuraventurameza-tech/ai-project.
Rama: work/chat-continuity.
Commit: 16e24fe828a5a0002ef13bb82bae9e295f190f86.
Base AppliedModelingLib: 194edcc95df74806a39b961d10dedddc6e730cce.
Lean previsto: leanprover/lean4:v4.30.0-rc2.
Mathlib: 5450b53e5ddc75d46418fabb605edbf36bd0beb6.
EconomicModel.lean SHA256:
d5e9bb95aad09ff515cc1418778c241d1b91ca3095c02b31eb369f496ea38d86.

ESTADO: codigo candidato SIN COMPILAR. No se ejecuto Lean ni Lake. El
argumento matematico y la inspeccion textual no son validacion del kernel.
No se importa ProofInterface ni se invocan sus resultados admitidos.
No se modifica el contrato ni ningun archivo de la fuente conservada.

Argumento matematico previo al codigo:
1. CompetitiveEquilibrium no depende del campo collateralDual. Los
   presupuestos, objetivos, dominios, mercados y planes de desviacion solo
   usan las decisiones y precios. Cambiar ese campo preserva el predicado.
2. Para cualquier equilibrio X y radio r>0, reemplazar cada dual por su
   valor mas r/2 produce otro equilibrio Y. En AllocationFullNear todos
   los campos tienen distancia cero salvo el dual, cuya distancia es r/2.
   Y no es igual a X: basta evaluar el dual en la historia inicial.
3. LocalExactContinuationAround exige existencia y unicidad literal de
   toda Allocation en ese mismo entorno. Su estado central x0 esta en
   el entorno; aplicar el paso 2 al equilibrio de x0 contradice unicidad.
4. Propuesta separada: comparar campos primales en historias admisibles,
   borrando el dual antes de usar AllocationFullNear y exigiendo distancia
   menor que todo radio positivo. En los reales esto equivale a igualdad
   de todos esos campos en el soporte. No exige igualdad fuera del soporte.

ALCANCE: se exhibe una obstruccion del contrato literal de unicidad. No
se refuta existencia de equilibrio, unicidad de decisiones observables ni
el argumento economico de ramas S/B. La definicion alternativa de abajo
solo repara este defecto de formulacion; NO prueba existencia, suavidad,
unicidad primal, Jacobianos invertibles ni multiplicidad. Las condiciones
KKT y la identificacion de duales siguen siendo obligaciones separadas.

El mismo criterio de igualdad debe usarse al formular "exactamente dos"
ramas: contar estructuras Allocation con duales libres produciria copias
arbitrarias de las mismas decisiones. En PaperInterface.lean 473--475,
la igualdad literal X = Xs o X = Xb requiere esa correccion separada.
-/

namespace Ventura26LiquidityAllocation
namespace ProposedContinuationContractAudit

variable {S : Type*} [Fintype S] [DecidableEq S]

def replaceCollateralDual (X : Allocation S)
    (dual : FirmType → AdaptedProcess S) : Allocation S :=
  { X with collateralDual := dual }

noncomputable def shiftCollateralDual (X : Allocation S) (epsilon : ℝ) :
    Allocation S :=
  replaceCollateralDual X (fun i t h ↦ X.collateralDual i t h + epsilon)

/-- El predicado de equilibrio es definicionalmente independiente de
`collateralDual`. No se usa una caracterizacion KKT de FirmOptimal. -/
theorem competitiveEquilibrium_replaceCollateralDual_iff
    (P : Primitives S) (I : InheritedState) (X : Allocation S)
    (dual : FirmType → AdaptedProcess S) :
    CompetitiveEquilibrium P I (replaceCollateralDual X dual) ↔
      CompetitiveEquilibrium P I X := by
  rfl

theorem allocationFullNear_refl
    (P : Primitives S) (radius : ℝ) (X : Allocation S)
    (hradius : 0 < radius) : AllocationFullNear P radius X X := by
  simp [AllocationFullNear, hradius]

theorem allocationFullNear_shiftCollateralDual
    (P : Primitives S) (radius epsilon : ℝ) (X : Allocation S)
    (hradius : 0 < radius) (hepsilon : |epsilon| < radius) :
    AllocationFullNear P radius X (shiftCollateralDual X epsilon) := by
  refine ⟨hradius, ?_⟩
  intro t h _hadmissible
  simp [shiftCollateralDual, replaceCollateralDual, sub_add_eq_sub_sub,
    abs_neg, hepsilon, hradius]

theorem shiftCollateralDual_ne
    (P : Primitives S) (X : Allocation S) (epsilon : ℝ)
    (hepsilon : epsilon ≠ 0) : shiftCollateralDual X epsilon ≠ X := by
  intro heq
  have hvalue := congrArg
    (fun Z : Allocation S ↦
      Z.collateralDual .H 0 (fun _ ↦ P.tree.initial)) heq
  change X.collateralDual .H 0 (fun _ ↦ P.tree.initial) + epsilon =
    X.collateralDual .H 0 (fun _ ↦ P.tree.initial) at hvalue
  apply hepsilon
  linarith

/-- Todo equilibrio tiene estructuras de equilibrio distintas y
arbitrariamente cercanas si se compara tambien el dual libre. -/
theorem exists_near_distinct_competitiveEquilibrium
    (P : Primitives S) (I : InheritedState) (X : Allocation S)
    (hX : CompetitiveEquilibrium P I X)
    (radius : ℝ) (hradius : 0 < radius) :
    ∃ Y : Allocation S,
      CompetitiveEquilibrium P I Y ∧
      AllocationFullNear P radius X Y ∧ Y ≠ X := by
  have hhalf : 0 < radius / 2 := by linarith
  have habs : |radius / 2| < radius := by
    rw [abs_of_pos hhalf]
    linarith
  refine ⟨shiftCollateralDual X (radius / 2), ?_,
    allocationFullNear_shiftCollateralDual P radius (radius / 2) X
      hradius habs,
    shiftCollateralDual_ne P X (radius / 2) (ne_of_gt hhalf)⟩
  exact (competitiveEquilibrium_replaceCollateralDual_iff P I X
    (fun i t h ↦ X.collateralDual i t h + radius / 2)).2 hX

/-- El contrato fuente no puede cumplirse: su unicidad literal incluye
un campo que el propio equilibrio no determina. -/
theorem not_localExactContinuationAround
    (P : Primitives S) (recurrent : S) (x0 : LocalPrefixStateSix)
    (tail : LocalPrefixContinuationRule) :
    ¬ LocalExactContinuationAround P recurrent x0 tail := by
  intro hcontinuation
  rcases hcontinuation with
    ⟨hx0, _hcontrols, radius, hradius, _hdifferentiable,
      inherited, continuation, hfamily⟩
  have hnear : LocalPrefixStateSixNear radius x0 x0 := by
    simp [LocalPrefixStateSixNear, hradius]
  rcases hfamily x0 hnear hx0 with
    ⟨_hinherited, hequilibrium, _hrealized, hunique⟩
  obtain ⟨Y, hY, hYnear, hYne⟩ :=
    exists_near_distinct_competitiveEquilibrium
      (P.withInitialState recurrent) (inherited x0) (continuation x0)
      hequilibrium radius hradius
  exact hYne (hunique Y hY hYnear)

/-! ## Propuesta de un contrato de unicidad primal sobre el soporte -/

def eraseCollateralDual (X : Allocation S) : Allocation S :=
  replaceCollateralDual X (fun _ _ _ ↦ 0)

/-- Misma vecindad de la fuente para todos los campos primales, sin
atribuir contenido economico a un dual todavia no identificado por KKT. -/
def AllocationPrimalNear (P : Primitives S) (radius : ℝ)
    (X Y : Allocation S) : Prop :=
  AllocationFullNear P radius (eraseCollateralDual X) (eraseCollateralDual Y)

/-- En cada historia admisible, todos los campos primales coinciden.
Se expresa mediante todos los radios positivos para reutilizar la lista
completa de observables de AllocationFullNear sin omitir ningun campo. -/
def AllocationPrimalAgreementOnSupport (P : Primitives S)
    (X Y : Allocation S) : Prop :=
  ∀ radius : ℝ, 0 < radius → AllocationPrimalNear P radius X Y

theorem primalAgreement_replaceCollateralDual
    (P : Primitives S) (X : Allocation S)
    (dual : FirmType → AdaptedProcess S) :
    AllocationPrimalAgreementOnSupport P X (replaceCollateralDual X dual) := by
  intro radius hradius
  change AllocationFullNear P radius (eraseCollateralDual X)
    (eraseCollateralDual (replaceCollateralDual X dual))
  have herase : eraseCollateralDual (replaceCollateralDual X dual) =
      eraseCollateralDual X := by rfl
  rw [herase]
  exact allocationFullNear_refl P radius (eraseCollateralDual X) hradius

/-- PROPUESTA de sustitucion del contrato, sin modificar la fuente.
La existencia, los estados heredados, los controles y la diferenciabilidad
se mantienen; solo la cercania/unicidad usa campos primales en el soporte.
No se demuestra aqui que este nuevo contrato tenga un testigo.
La mera DifferentiableOn conservada tampoco suministra continuidad de la
derivada ni signos uniformes en un entorno; antes de una aplicacion de IFT
esas propiedades deben demostrarse con sus hipotesis analiticas propias. -/
def LocalExactContinuationAroundPrimal
    (P : Primitives S) (recurrent : S) (x0 : LocalPrefixStateSix)
    (tail : LocalPrefixContinuationRule) : Prop :=
  let Q := P.withInitialState recurrent
  let response := localContinuationLogResponse x0 tail
  LocalPrefixStateSixPositive x0 ∧
  (∀ j, 0 < localPrefixControlsTenVector (tail x0) j) ∧
  ∃ radius : ℝ, 0 < radius ∧
    DifferentiableOn ℝ response (Metric.ball (0 : Fin 6 → ℝ) radius) ∧
    ∃ inherited : LocalPrefixStateSix → InheritedState,
      ∃ continuation : LocalPrefixStateSix → Allocation S,
        ∀ x, LocalPrefixStateSixNear radius x0 x →
          LocalPrefixStateSixPositive x →
          LocalContinuationInheritedStateMatches Q x (inherited x) ∧
          CompetitiveEquilibrium Q (inherited x) (continuation x) ∧
          LocalContinuationInitialControlsRealized Q (continuation x) tail x ∧
          ∀ Y, CompetitiveEquilibrium Q (inherited x) Y →
            AllocationPrimalNear Q radius (continuation x) Y →
            AllocationPrimalAgreementOnSupport Q Y (continuation x)

end ProposedContinuationContractAudit
end Ventura26LiquidityAllocation
