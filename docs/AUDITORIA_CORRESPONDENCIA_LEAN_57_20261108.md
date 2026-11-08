# Matriz de correspondencia entre los 57 resultados y Lean

**Corte editorial:** 8 de noviembre de 2026. **Rama de investigación:**
`work/lean-ci-validation-otc-20261106`. **Fuente de verdad:**
`paper/result_ledger.json` y `paper/lean_crosswalk_57.json`.

## Actualización CI: cuatro declaraciones financieras comprobadas

La auditoría Lean
[42457259796](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/42457259796),
commit `c006e00c437243c3f6f44ec3c102df4286c545e0`,
**compiló y auditó `#print axioms` sin `sorryAx`** para
`exact_noSimultaneousSavingBorrowingSpec` (3.2),
`exact_financingCapacityComparativeSpec` (3.3),
`original_fundingSupergradientSpec_false` (contraejemplo a
la versión mal parentizada de 3.5) y
`corrected_fundingSupergradientSpec` (superdiferencial de
3.5 matemáticamente corregido). La especificación literal
3.5 no se declara probada: está refutada. El checkpoint
`PaperInterface.lean` permanece intacto.

El Lema 3.1 también quedó **DEMOSTRADO como especificación literal
Lean**: `PaperRepaymentExactCandidate.exact_repaymentSpec`
compiló y pasó `#print axioms` sin `sorryAx` en
[42458034938](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/42458034938),
commit `acc4263a2c60c6ec3a90c3331aef9cb522e4427a`.
Cubre por estado la cota de repago real, la desigualdad de
patrimonio, su no negatividad y su positividad si hay capital o
depósito positivo. No acredita suficiencia dinámica ni
solvencia bancaria en presencia de retiradas.

El Lema 4.3 cuenta ahora con **tres identidades auxiliares
formalmente verificadas** en
`PaperAllocationLossElasticityCandidate.lean`. Pasaron el kernel
y `#print axioms` sin `sorryAx` en
[Lean focalizado #42458449121](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/42458449121),
commit `1e797f886dea03a6fdea135338e6408a3e8ab91b`:
(1) álgebra del diferencial si se conocen las logderivadas agregadas,
(2) orden de participaciones y producto por capital positivo,
(3) signo negativo de la pérdida cuando se mueve capital relativo
hacia el tipo con mayor participación de producto que de capital.

El **Lema 4.3 integral sigue pendiente**: demostrar el reparto
laboral óptimo, la referencia eficiente y su superioridad productiva
desde los problemas originales, junto con las derivadas de
agregadores Cobb–Douglas. La versión de `allocationLossIdentitySpec`
tampoco contiene la ecuación diferencial completa del paper. Véase
`docs/LEMA_4_3_MECANISMO_ASIGNATIVO_20261108.md`.
La matriz registra run y commit para estos fragmentos sin cambiar
su relación a `same_statement_proved` del resultado académico.

La matriz `paper/lean_crosswalk_57.json` registra
la evidencia verde de estos cuatro objetos, pero
`paper_proof_equivalent_in_lean` conserva el valor
`not_established` en el registro: se certifican las
**proposiciones Lean exactas o corregidas**, no por ello
la totalidad de las obligaciones intertemporales del paper.

## 1. Veredicto general sin sobredeclaración

Se han inspeccionado de manera dirigida **24 de 57** afirmaciones:
se localizó al menos una declaración Lean con objeto relacionado, y
se describió explícitamente por qué no alcanza, todavía, a demostrar
el enunciado completo del paper. **33 resultados** siguen pendientes
de cotejo semántico individual. El identificador histórico de cada
resultado, su título y el hash de su enunciado son trazables en JSON.

El estatus de formalización integrada del registro fuente permanece
`not_run` en los **57/57 casos**; por tanto **ningún resultado
numerado se promociona a prueba formal de igual alcance**.
Eso no niega que existan teoremas Lean válidos; impide confundirlos
con enunciados que cambian cuantificadores, funciones, hipótesis,
dominios, calendarios o conclusiones.

El auditor `code/audit_lean_crosswalk.py`, agregado a
`editorial-qa.yml`, verifica uno por uno: cardinalidad, etiquetas,
títulos, hashes de enunciados, enlace a las declaraciones
Lean efectivamente existentes, existencia de las referencias
numéricas y ausencia de promoción espuria de cobertura.
Su salida `PASS_SYNTAX_AND_SCOPE_ONLY_NOT_EQUIVALENCE` solo
certifica **integridad del inventario y alcance declarado**;
no es una prueba Lean ni una certificación de correspondencia.
El módulo Lean especializado `LocalScalarStationaryPythonCalibrationCandidate`
y otras identidades sí pasaron sus propias auditorías de
compilación y axiomas en los runs registrados en la nota
`PUENTE_ESTACIONARIO_PYTHON_LEAN_20261108.md`.

## 2. Lectura precisa de la proposición central

La proposición `prop:local_macro_multiplicity` del paper considera
una función reducida `M(s,h)`, de clase `C¹` cerca de
`(0,0)`, con `M(0,0)=0`,
`b=∂_s M(0,0)<0` y `a_R=∂_h M(0,0)<0`.
Para `h<0` pequeño obtiene una solución en el borde `s=0`
y una raíz positiva `s(h)>0`; para `h>0` pequeño,
no hay solución complementaria cercana.

Las declaraciones Lean relacionadas **no son literalmente iguales**:

| Declaración Lean localizada | Qué afirma realmente | Qué falta para el paper |
|---|---|---|
| `ProposedScalarComplementarityMultiplicity.scalar_complementarity_exactly_two` | Cuenta dos soluciones dada antitonicidad en el semieje no negativo, una raíz positiva explícita y `M(0)>0` | Derivar raíz y signos para `h` desde `C¹`; antitonicidad aquí es global sobre el semieje |
| `ProposedLocalScalarPolicyBifurcation.negative_shock_creates_exactly_two_local_scalar_roots` | Produce la raíz en una cuña local si se tienen derivadas y continuidad/monotonía en dicha cuña | Identificar efectivamente esas premisas con el Schur complement fuente |
| `ProposedLocalScalarEconomicPolicyCertificate.source_economic_negative_remuneration_shock_two_roots` | Especializa al mapa económico de fuente, pero presupone `LocalScalarImplicitReduction`, dual nulo en el punto de base y regularidad local uniforme de cortes | Certificar las premisas en la instancia numérica fuente, no asumirlas a partir del Python heredado |
| `ProposedProposition42Audit.localMacroMultiplicitySpec_false` | Refuta el contrato original que pedía unicidad literal de la estructura `Allocation` con un campo `collateralDual` no restringido por el predicado de equilibrio | Reformular unicidad primal sobre soporte admisible, probar existencia de las dos ramas económicas y condiciones terminales |

**Conclusión responsable:** la prueba escrita de complementariedad
local es matemáticamente coherente bajo sus premisas,
pero las **premisas del modelo económico original**
aún no están plenamente verificadas para ambas ramas.
El contraejemplo de la especificación Lean original
no constituye una refutación de la multiplicidad
económica que compara variables primales.

## 3. Resultados principales y el tipo de brecha

Las numeraciones de la tabla son **identificadores históricos** del
ledger; el cuerpo compacto conserva una paginación nueva y
los números de PDF antiguos no deben usarse como localizadores.

| ID del ledger | Hallazgo del cotejo dirigido | Veredicto |
|---|---|---|
| 3.3 — efecto parcial de menor tasa | `rate_cut_raises_capacity_given_same_funds` y `firmFeasible_binding_capital_formula` son lemas algebraicos del mismo canal | Prueba auxiliar, no cálculo diferencial completo de equilibrio |
| 3.6 — KKT financiero | `source_scalar_complementarity_recovers_original_L_KKT` recupera la condición escalar de L | No cubre equivalencia total de KKT ni suficiencia |
| 3.8 — spread no negativo | `bank_margins_and_pricing` fija signos del testigo estacionario | No demuestra la proposición general de covarianza |
| 3.9 — consistencia de flujos | `parent_resourceClears`, `parent_bankBalance`, `parent_creditClears` cierran cuentas estacionarias | La prueba general por historias permanece abierta |
| 4.1 — equilibrio de frontera | `BoundaryFullPrefixCandidate` verifica filas del prefijo | No demuestra todas las premisas de equilibrio competitivo |
| 4.2 — multiplicidad local | Teoremas escalares y contraejemplo literal citados arriba | Correspondencia económica completa no establecida |
| 4.4 — asignación opuesta S/B | Existe una cuenta numérica reproducible y lemas de raíces escalares | No existe prueba Lean de los signos de capital, pérdida y soluciones de equilibrio |
| 4.5 — persistencia bajo riesgo | Todavía no se cotejó con declaración de mismo alcance | Revisión prioritaria pendiente |

Los **14 resultados numerados del cuerpo histórico** ya tienen cotejo
semántico dirigido. Esto no acredita cobertura integrada: para cada
resultado se han registrado las hipótesis y las brechas.

## 4. Cinco relaciones auxiliares del anexo

Se localizaron relaciones parciales relevantes para
`prop:stationaryexistence` (testigo estacionario
`parent_competitiveEquilibrium`),
`lem:statewise_collateral` (garantía de una trayectoria),
`lem:nominal_face_identity` (identidad de cara nominal),
`lem:common_pledge_state` (equivalencia de ceros de fila 21),
y `lem:CRRA_H_demand` (identidad de presupuesto y cobertura,
sin derivar utilidad CRRA). Ninguna ha sido promovida a
igualdad literal con el lema del anexo.

## 4 bis. Hallazgo del módulo fuente `FinancialCore.lean`

La segunda revisión reveló una omisión metodológica del primer inventario:
en `lean/checkpoint/modules/Ventura26LiquidityAllocation/FinancialCore.lean`
hay **tres teoremas fuente** mucho más cercanos al paper de lo
que sugerían los nombres de los módulos candidatos:

| Resultado | Prueba fuente ya declarada | Nuevo puente exacto candidato |
|---|---|---|
| Lema 3.2: no ahorrar y endeudarse simultáneamente | `no_simultaneous_saving_and_borrowing`: contradicción de KKT si `RL>RD>0` y ambos saldos positivos | `exact_noSimultaneousSavingBorrowingSpec` |
| Proposición 3.3: efecto parcial de la tasa | `financingCapacity_hasDerivAt_and_deriv_neg`: derivada exacta de capacidad con fondos, `q` y garantía fijos | `exact_financingCapacityComparativeSpec` |
| Lema 3.5: superdiferencial | `isFundingSupergradient_iff_cases`: equivalencia global para tres caras, incluyendo el intervalo en `f=0` | `original_fundingSupergradientSpec_false` + `corrected_fundingSupergradientSpec` |

Los puentes se declararon en
`lean/candidates/Ventura26LiquidityAllocation/PaperFinancialMainExactCandidate.lean`.
**Solo 3.2 y 3.3** tienen objetivo literal `PaperInterface.*Spec`.
Para 3.5, la primera compilación **FALLÓ** (Lean CI
[42456592968](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/42456592968)).
La inspección mostró que el `PaperInterface.fundingSupergradientSpec`
fue escrito formalmente como

```text
((0 < RD -> RD < RL -> IsFundingSupergradient RL RD face slope)
  <-> FundingSupergradientCases RL RD face slope)
```

y no como la especificación económica correcta

```text
(0 < RD -> RD < RL ->
  (IsFundingSupergradient RL RD face slope
   <-> FundingSupergradientCases RL RD face slope))
```

Es un error sustantivo de ámbito de `→` frente a `↔`, no
simplemente una táctica `intro` que no compiló. Contraejemplo:
`RL=RD=1`, `face=0`, `slope=2`. La premisa de spread
estricto es falsa y la implicación de la izquierda resulta
verdadera vacíamente, mientras que los casos de la derecha son
falsos (el intervalo admisible sería `[1,1]`).
Por tanto, el enunciado original **no puede demostrarse**
en lógica consistente. No se modifica el checkpoint;
se añade el teorema `original_fundingSupergradientSpec_false`
y una proposición independiente
`fundingSupergradientCorrectedSpec` con prueba
`corrected_fundingSupergradientSpec`.
La compilación y auditoría de axiomas de esas dos declaraciones
**siguen pendientes de CI** antes de elevar su estatus.
No modificar todavía `formalization_status` del ledger fuente.

El problema no invalida la fórmula económica del paper,
que ya contiene `R^L>R^D>0`; invalida la transcripción lógica
del objetivo fuente cuando las tasas están fuera de ese dominio.

Al cotejar **los siete últimos resultados principales**:
el Lema 3.1 dispone del predicado fuente `RobustCollateral`,
y ahora existe un candidato exacto para patrimonio futuro no negativo, aún bajo prueba Lean;
el Lema 3.4 tiene un teorema fuente de recuperación de cartera
`signedFundingEquivalence` que no eleva por sí solo óptimos
intertemporales; el Lema 3.7 tiene la cota de tasa interbancaria
`otcCorridorWeight_mem` pero no la monotonicidad global prometida
en `tightness`; y los resultados 4.3 y 4.5 siguen sin prueba
completa equivalente a su enunciado histórico.

**Brecha especialmente relevante para 4.3:** `allocationLossIdentitySpec`
en `PaperInterface.lean` enuncia parte del referente eficiente y
la no negatividad de la pérdida, pero **no** contiene la derivada
`d𝓛 = α(κ_H-ω_H)d log(k_H/k_L)` incluida en el paper.
Aun una prueba exitosa de ese `Spec` sería estrictamente más débil
que el lema académico completo.

**Brecha especialmente relevante para 4.5:** el `Spec` Lean original
requiere dos equilibrios competitivos estocásticos completos para
riesgos positivos pequeños, mientras que el paper vigente enuncia
solo persistencia de soluciones reducidas **suponiendo** que
la continuación es contractiva. No puede reutilizarse el resultado
reducido para afirmar verdadero el `Spec` más fuerte.

## 4 ter. Auditoría dirigida del núcleo de existencia y suficiencia en anexos

Se amplió el cotejo a cinco proposiciones de riesgo especialmente alto:
`prop:firm_sufficiency_infinite` (A.17.1),
`prop:general_regime_sufficiency` (A.32.1),
`prop:finite_prefix_equilibrium` (A.32.2),
`prop:certified_small_risk_equilibrium` (A.30.1)
y `prop:nonlinear_local_path` (A.15.2).
Las cinco tienen declaraciones Lean **relacionadas pero de
alcance insuficiente** para sus enunciados originales.

- `parent_firmOptimal` y `parent_firm_dominates` demuestran
  optimalidad de empresas en un **testigo estacionario concreto**;
  no la suficiencia intertemporal para todo árbol y régimen financiero.
- `firmOptimal_twoSidedVariation_derivative_zero` obtiene una
  condición **necesaria** de optimalidad por variación, no una
  suficiencia universal de sistemas KKT.
- `parent_competitiveEquilibrium` acredita un equilibrio
  estacionario literal condicionado a `reservesPre≤G`;
  no ensambla una continuación estocástica con un prefijo perturbado.
- `boundaryRoot_spec` exhibe una raíz del residual de
  recursos de frontera bajo paquetes de signo, no el equilibrio
  de todas las condiciones de empresas, hogar, bancos y precios.
- `source_economic_negative_remuneration_shock_two_roots`
  presupone una reducción implícita y signos locales;
  no certifica las contracciones uniformes ni la
  optimalidad del testigo con riesgo `0<η≤10^-31`.

Esta revisión eleva el número de resultados con cotejo
dirigido a **24/57**; los otros **33** siguen sin revisión
individual. No significa que estas cinco proposiciones hayan
quedado demostradas en Lean. Se conserva la marca
`paper_proof_equivalent_in_lean=not_established`.
El inventario exacto y las obligaciones individuales están en
`paper/lean_crosswalk_57.json`.

## 5. Obligaciones antes de promover cualquier resultado

1. Comparar **enunciado literal**, todos los cuantificadores y
   dominios. Un resultado para un testigo estacionario no cubre
   una afirmación general en un árbol estocástico.
2. Conciliar los datos numéricos y los vectores fuente:
   `Z`, `I`, el calendario del shock y `tail`. Las
   equivalencias de cero de ocho filas no demuestran por sí
   mismas identidad de todas las derivadas del operador de 34 filas.
3. Obtener evidencia de compilación y axiomas del **commit exacto**
   que contiene el módulo enlazado, sin `sorryAx` ni axiomas
   auxiliares especiales sin justificar.
4. Para elevar raíces del sistema reducido, demostrar
   factibilidad por historia, optimalidad individual,
   clearing, apoyo por precios, continuación y terminalidad;
   distinguir KKT necesarias de suficiente optimalidad.
5. Emitir veredicto por resultado: `same_statement_proved`,
   `strictly_weaker`, `conditional_different_statement`,
   `counterexample_to_original` o `still_unreviewed`;
   solo los casos `same_statement_proved` pasan a estado
   integral, y únicamente si las hipótesis están cotejadas.

## 6. Orden de cierre recomendado

**P0 (entrega):** revisar 4.2, 4.4, 4.5, 4.1 y las
identidades de capacidad empresarial; reescribir las
afirmaciones de alcance demasiado amplio en vez de
pretender que cada una ya está formalizada.

**P1 (reproducción):** contrastar integralmente operadores
fuente y Python de 34 filas y sus derivadas, con hashes
de escenario, radios y signos. No aplicar a una IRF de
`h=-10^{-5}` un certificado que cubre solo
`|h|≤10^{-15}`.

**P2 (manuscrito):** cerrar la comparación literal entre
proposición y Lean, añadir el cotejo realmente manuscrito
del autor y el veredicto crítico, revisar las fuentes
bibliográficas y pasar el control visual de PDFs. No
fusionar PR #2 antes del cierre de los checks.

No se hace afirmación de que todas estas tareas deban
completarse para disponer de un paper **condicional** y
honesto para el curso; sí son necesarias antes de
declarar cerrado el programa científico general.
