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


## Adenda técnica del 9 de noviembre de 2026: obligación 4.1 (frontera)

**Cambio de prioridad:** de cotas OTC auxiliares a la construcción del testigo de frontera. No se modifica la conclusión del manuscrito ni se afirma que `CompetitiveEquilibrium` esté demostrado. Base contrastada: commit `c15c413969db0598b9cb39b8c432689e9b2a5127` (CI *focused* verde para las declaraciones financieras; **no** acredita por sí solo los módulos `Boundary*`). Trabajo nuevo: commit `0a33f950f4c7c066dcb67a0ad8385eaa1ae0812b`, pendiente de compilación en el audit de candidatos.

### Estado de las piezas exactas del prefijo

1. **FOC laboral de fecha cero:** el módulo existente `BoundaryWorkerLaborCandidate.lean` contiene `boundary_workerLabor_row_zero`, `boundary_workerLabor_package` y `boundary_full_prefix_equations_from_root`. A diferencia de la descripción histórica del 7–8 de noviembre, **hay una prueba candidata explícita que intenta descargar `BoundaryWorkerLaborPackage`** mediante homogeneidad laboral, positividad y la raíz cúbica del salario. El estatus es *prueba fuente propuesta*, no *compilación confirmada por la CI focused*.
2. **Regularidad del residual:** `BoundaryAnalyticPackageCandidate.boundary_analyticPackage` construye `ContinuousOn` y `StrictMonoOn` del residual sobre `[41/40,129/125]` a partir de las funciones económicas; no toma la monotonía como hipótesis en su conclusión. Es una prueba candidata que requiere compuerta Lean de candidatos y axiomas.
3. **Signos de extremos:** `BoundaryEndpointBoxesCandidate.BoundaryComponentBoxes` contiene **diez desigualdades racionales** que implican signos estrictos de un residual normalizado. En `BoundaryNormalizationBridgeCandidate.endpointSigns_of_boxes_and_output_roots` permanecen además dos instancias `OutputRootIdentityAt` (una en cada extremo), que evitan asumir directamente `\Phi(a)<0<\Phi(b)`. Las diez cajas **no están descargadas** por ese teorema; sus valores requieren pruebas verificables y no solamente la salida de Python/Decimal.
4. **Quinta identidad de normalización:** las otras cuatro identidades (consumo del trabajador, ambos consumos empresariales y costo de capital) se derivan en `BoundaryNormalizationBridgeCandidate.scaleIdentities_of_output_root`. En `0a33f950` se añadió a `BoundaryAnalyticPackageCandidate` el lema candidato `output_ratio_fifteenth_power`:

   \[
   \left(\frac{Y_0(R)}{\bar Y}\right)^{15}
   =s(R)^8\,[0.99 R_0^D(R)]^5,
   \quad s(R)=\text{boundaryCapitalScale}(R)>0.
   \]

   Junto con \(Y_0/\bar Y>0\), debería permitir probar que \(Y_0/\bar Y\) coincide con la **raíz positiva decimoquinta** usada por `normalizedOutput`, y eliminar ambas hipótesis `OutputRootIdentityAt`. **Hasta una CI verde, sigue siendo un candidato, no un resultado certificado.**
5. **De 33 filas a equilibrio infinito:** aun cerrando el signo del bracket y la FOC laboral, `LocalReducedPrefixEquationsHold` no es `CompetitiveEquilibriumWithInitialIntervention`. Faltan testigos de trayectoria en el espacio de historias, factibilidad y limpieza de mercados, optimalidad global de hogares/firmas/bancos/minoristas, condiciones terminales y coherencia de las ramas.

### Criterio de aceptación de la proposición 4.1

Una afirmación *exact_match* requiere (i) prueba kernel de `boundary_full_prefix_equations_from_root` con sus hipótesis efectivamente descargadas y `#print axioms` libre de `sorryAx`; (ii) testigo de existencia de trayectoria y `CompetitiveEquilibriumWithInitialIntervention` bajo las primitivas exactas del paper; (iii) prueba de condición activa de L, préstamo positivo y dual nulo en fecha cero, y condiciones afirmadas a partir de fecha 1; (iv) análisis de optimalidad global, solvencia y transversalidad, sin identificar automáticamente raíces del sistema reducido con equilibrios completos. Un éxito de la CI *focused* del bloque OTC no satisface estos criterios.

**Decisión de auditoría:** la categoría de 4.1 sigue siendo **puente parcial / equilibrio completo abierto**. La descripción previa «FOC laboral todavía aislada» queda refinada a «FOC laboral con candidato de prueba explícito, a verificar en la CI de candidatos»; el cuello de botella inmediato pasa a las dos identidades de raíz de producción y las diez desigualdades de extremos.
