# Auditoría preliminar de correspondencia: proposiciones 4.1–4.5

Fecha: 8 de noviembre de 2026 (Lima). Rama: `work/lean-ci-validation-otc-20261106`.
Revisión de partida: `93cfb4dd6b5c0f212975621b22ddc1cec6331a6c`.

## Convención de evidencia

- **Coincidencia exacta:** declaración Lean cuya conclusión e hipótesis cubren literalmente el enunciado del paper, con SHA, corrida verde y sin `sorryAx`.
- **Puente parcial:** lema formal sobre un subproblema o bajo hipótesis más fuertes; NO certifica la proposición completa.
- **Solo numérico:** solución de sistema reducido o comprobación computacional reproducible, no teorema de equilibrio.
- **Abierto:** no se ha encontrado en esta auditoría un certificado del enunciado completo.

El archivo `paper/result_ledger.json` declara 57 resultados; en la inspección de esta revisión los 57 conservan `formalization_status=not_run`, y ninguno tiene `author_full_review=true`. Eso es **un déficit de trazabilidad del registro**, no una afirmación de que los 57 carecen de prueba. No actualizar esas etiquetas por parecido de nombres.

## Correspondencia examinada

| Paper | Título en el ledger | Evidencia específica examinada | Alcance verificado / obstáculo | Clasificación |
|---|---|---|---|---|
| 4.1 | Un equilibrio en la frontera de L | `BoundaryFullPrefixCandidate.lean`, `BoundaryResourceRootCandidate.lean`; `docs/PUENTE_REDUCIDO_EQUILIBRIO.md` | Prefijo y raíz de recursos no son por sí solos un testigo de `CompetitiveEquilibrium` infinito; se requieren condiciones laborales, extensiones y optimalidades | Puente parcial; existencia completa abierta |
| 4.2 | Dos soluciones locales de la complementariedad reducida | `LocalScalarComplementarityCandidate.local_scalar_complementarity_exactly_two_of_crossing`; `LocalScalarEconomicPolicyCertificate.source_economic_negative_remuneration_shock_two_roots`; `LocalScalarOriginalBoundaryBBranchCandidate`; `LocalScalarOriginalInteriorSBranchCandidate` | Lemas locales y puentes de filas/KKT condicionados; la especificación de unicidad literal de `Allocation` tiene un dual libre; hace falta equivalencia primal y construir soluciones completas | Formal condicional para subproblema, no multiplicidad de equilibrio |
| 4.3 | Referencia eficiente y derivada de reasignación | `PaperAllocationLossElasticityCandidate.allocation_loss_log_differential_algebra`; `PaperAllocationEfficiencySupportCandidate.normalized_two_type_output_le_benchmark`; `PaperAllocationSourceAlgebraBridgeCandidate.positive_aggregate_loss_log_formula` | Pruebas algebraicas y de eficiencia normalizada; el empalme con pérdida asignativa original, elección laboral y derivadas totales no se presume | Puente parcial |
| 4.4 | Condiciones de una mejora y un deterioro para el mismo instrumento | `code/irf/output/delivery_audit.json`; `docs/RESULTADOS_Y_ALCANCE.md` | Respuestas divergentes de pérdida asignativa condicional S/B reproducidas para parámetros ilustrativos; falta demostración de equilibrio global y que el instrumento produzca esas ramas | Solo numérico/reducido en este cotejo |
| 4.5 | Persistencia condicional de ramas reducidas bajo riesgo | `docs/PUENTE_REDUCIDO_EQUILIBRIO.md`; diagnósticos no lineales T=640 en `code/irf/DIAGNOSIS_STATUS.md` | Aproximaciones finitas y continuación local no equivalen a una cola infinita con factibilidad uniforme y selección de rama; reformulada con alcance condicional | Parcial / conclusión infinita abierta |

## Bloque OTC separado del capítulo 4

La ejecución CI **verde** para `93cfb4dd` demuestra teoremas condicionales en `PaperBankConditionalOTCTransitionIdentityCandidate.lean`, incluidos los puentes de masa/TVC y cotas de retorno bancario firmadas, pero no es una prueba exacta automática de las proposiciones 4.1–4.5. Incorporarlos a un futuro crosswalk solo donde sus hipótesis, cuantificadores, conclusión y objeto económico coincidan.

## Próximas acciones de cierre

1. Cotejar literalmente los entornos LaTeX y los cuantificadores de cada proposición con el `lean_declaration` candidato.
2. Registrar `exact_match / weaker_conditional / numerical_only / open` junto al SHA de la declaración y la corrida con `#print axioms`; no inferir identidad por nombre o temática.
3. Priorizar 4.1 (existencia), 4.2 (multiplicidad modulo duales libres) y 4.5 (cola infinita), por riesgo de sobreafirmación.
4. Rehacer la auditoría de los 57 resultados; separar la certificación de módulos del nivel de cobertura exacta del artículo.
5. No declarar crecimiento sostenido, optimalidad bancaria global ni equilibrio infinito mientras no existan los correspondientes certificados.

Esta auditoría es una primera clasificación sustentada en archivos del repositorio y diagnósticos existentes; NO constituye una revisión formal completa de los 57 enunciados.
