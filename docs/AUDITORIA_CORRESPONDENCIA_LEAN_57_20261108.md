# Matriz de correspondencia entre los 57 resultados y Lean

**Corte editorial:** 8 de noviembre de 2026. **Rama de investigación:**
`work/lean-ci-validation-otc-20261106`. **Fuente de verdad:**
`paper/result_ledger.json` y `paper/lean_crosswalk_57.json`.

## 1. Veredicto general sin sobredeclaración

Se han inspeccionado de manera dirigida **12 de 57** afirmaciones:
se localizó al menos una declaración Lean con objeto relacionado, y
se describió explícitamente por qué no alcanza, todavía, a demostrar
el enunciado completo del paper. **45 resultados** siguen pendientes
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

Los demás seis resultados principales de los catorce históricos se
mantienen `not_yet_semantically_reviewed` y no se interpretan
como falsos ni como demostrados.

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
