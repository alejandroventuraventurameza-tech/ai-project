# Del certificado escalar SOURCE a un testigo de equilibrio intertemporal

**Fecha:** 9 de noviembre de 2026. **Rama de trabajo:** `work/lean-ci-validation-otc-20261106`. **Regla:** no fusionar PR #2 mientras no exista el testigo completo.
**Base kernel certificada:** `3be17cc4acc545e823fc618164602e5835833e4e`, compuerta Lean `42707095089`, auditoría de candidatos certificada en `69fbc8b0` (ejecución `42706205583`), build y QA editorial verdes. Las pruebas de dominio, colateral y trabajo inicial de `69fbc8b0` están incorporadas y verificadas. **Nuevo puente SOURCE a PaperInterface:** las tres declaraciones que fijan el residual y lo vinculan condicionalmente con un testigo completo permanecen pendientes de CI en el commit que introduce este documento.

## 1. Teorema cerrado frente al objetivo científico abierto

El teorema `ProposedBoundaryNormalizationBridge.boundary_unique_reduced_prefix_rate_from_source` demuestra sin hipótesis de cajas la existencia y unicidad de una tasa `R` en `[41/40,129/125]` que anula `boundaryResourceResidual` y satisface `LocalReducedPrefixEquationsHold` para las dos ramas de prefijo y sus 33 ecuaciones. El objeto nombrado `boundarySourceRate` y `boundarySourceRate_spec` recuperan esa raíz en la compilación certificada `3be17cc4`. La auditoría de axiomas correspondiente debe excluir `sorryAx` en **esas declaraciones**, no solo en una dependencia adyacente.

**No se deduce** que exista una asignación `X : Allocation S` sobre todas las fechas e historias, ni `CompetitiveEquilibriumWithInitialIntervention P I v X`. La función reducida `Phi` tampoco constituye por sí misma una regla de selección dinámica entre ramas S/B.

La definición fuente `CompetitiveEquilibrium P I X` (en `EconomicModel.lean`, alrededor de la línea 10992 de la revisión fuente) exige literalmente:

| Familia | Predicados/obligaciones del contrato original | Evidencia de frontera disponible | Estado para un testigo completo |
|---|---|---|---|
| Política y dominio | `MonetaryPolicyPrimitiveDomain`, `PositiveDomain`, `MonetaryPolicyRules` | Ecuaciones de fecha cero/uno y cotas de variables seleccionadas | **ABIERTO:** todas las fechas/historias y dominio completo |
| Firmas | `∀ i, FirmOptimal P I X i`; `FirmBudgetFlows` | Euler financiera reducida, dual L nulo, dual H positivo, presupuesto local | **ABIERTO:** máximos globales y terminalidad para cada plan |
| Hogar | `HouseholdOptimal`; `HouseholdBudgetFlows` | Euler y FOC laboral del prefijo local | **ABIERTO:** desviaciones admisibles, objetivos y TVC |
| Bancos | `BankPopulationEquilibrium`, `BankBalance` | Signos, stocks y algunas filas de balance y precios | **ABIERTO:** población por tipos, Bellman, OTC, óptimo dinámico y terminalidad |
| Minoristas/productor de capital | `RetailOptimal`, `CapitalProducerOptimal`, `CapitalProducerAccounts` | Filas reducidas, bandas de precios y costo de instalación | **ABIERTO:** suficiencia global y cuentas para toda la trayectoria |
| Presupuestos y caras nominales | `InheritedNominalFaceConsistency`, `CurrentNominalFaceConsistency`, `AccountingIdentities` | Reconstrucción local de algunos campos heredados | **ABIERTO:** identidad completa en historias admisibles |
| Agregados y mercado | `AggregateProduction`, `FiscalClosure`, `CreditClears`, `DepositsClear`, `CapitalClears`, `LaborClears`, `ResourceClears` | Residuales reducidos y `Phi(R*)=0` | **ABIERTO:** equivalencia literal y validez global |

`LocalReducedPrefixEquationsHold` está tipado con `LocalPrefixCoordinates` y `LocalPrefixContinuationRule`; `LocalPrefixEquationsHold` está tipado con una `Allocation S` concreta. El puente entre ambos exige **realización de coordenadas y controles de continuación**, no solo igualdad de sus 33 residuales en vectores distintos.

## 2. Dos riesgos lógicos del contrato del paper

**(i) Portador de la raíz libre.** `PaperInterface.boundaryEquilibriumSpec` cuantifica `∃ Phi : ℝ → ℝ` y solicita `ExactRootOn Phi 1.025 1.032` junto con `BoundaryEquilibriumCandidate P I X`, pero no obliga a que `Phi = boundaryResourceResidual` ni que la raíz determina los campos de `X`. Una prueba de esa especificación, sin añadir el nexo de fuente, sería insuficiente para la afirmación de construcción exacta del manuscrito.

**(ii) Interfaz de suficiencia no cerrada.** `ProofInterface.finitePrefixEquilibrium : finitePrefixEquilibriumSpec := by sorry` es un *placeholder*, no una demostración utilizable como certificado sin `sorryAx`. Además, `finitePrefixEquilibriumSpec` enumera `BankOptimal` donde `CompetitiveEquilibrium` exige `BankPopulationEquilibrium`, y omite del antecedente explícito `MonetaryPolicyPrimitiveDomain`, `MonetaryPolicyRules`, `FirmBudgetFlows`, `HouseholdBudgetFlows`, las dos consistencias de promesas nominales, `AggregateProduction` y `CapitalProducerAccounts`. Antes de invocarla para el equilibrio global es imprescindible probar o incorporar cada premisa faltante, preferiblemente mediante un teorema puente nuevo, no promoviendo el placeholder.

Para la proposición 4.1 el contrato fuerte debe ligar **la misma** tasa y el mismo `X` al residual fuente y al equilibrio completo, y certificar el régimen de colateral para las historias de fecha cero y posteriores.

## 3. Secuencia de construcción y compuertas de calidad

1. **Carrier explícito.** Construir `P`, `I`, `v` y `X : Allocation S` para el calendario escogido. Identificar qué ramas e historias son admisibles; probar que sus campos reproducen `boundaryInitialState`, `boundaryCoordinates boundarySourceRate` y las 33 ecuaciones sin cambiar de primitivas a mitad de la prueba.
2. **Fecha cero y continuación inmediata.** Descargar dominios, Euler y balances empresariales, bancos, hogar, mercado y reglas monetarias sobre el `X` literal. Las nuevas pruebas sobre `boundarySourceRate` son lemas de fecha cero, **no** sustitutos de la realización global.
3. **Cola recurrente.** Construir una solución exacta para cada historia admitida, comprobar que satisface ecuaciones, restricciones y positividad, y enlazar estados en fechas 1 y 2. Una cola finita T=640 o una linealización no acredita el infinito.
4. **Optimalidad y terminalidad.** Probar `FirmOptimal`, `HouseholdOptimal`, `BankPopulationEquilibrium`, `RetailOptimal` y `CapitalProducerOptimal` por las definiciones originales: FOC/KKT necesarias no implican máximos globales. Descargar condiciones de transversalidad y convergencia de objetivos con hipótesis uniformes.
5. **Equilibrio exacto y corrección del enunciado.** Unir los veintidós componentes de `CompetitiveEquilibrium` para un único `X`; a continuación probar `CompetitiveEquilibriumWithInitialIntervention` para el instrumento correctamente etiquetado y construir `BoundaryEquilibriumCandidate` con el régimen requerido de H/L.
6. **Auditoría.** Registrar SHA, `#print axioms`, ausencia de `sorryAx`, tests reproducibles, trazabilidad del manuscrito y diferencia entre nivel de producto, transición y crecimiento sostenido.

`LocalExactContinuationAround` es una obligación adicional para la proposición 4.2: además de la trayectoria central requiere soluciones vecinas y unicidad adecuada; la libertad del dual de colateral vuelve inapropiada la unicidad literal de todos los campos de `Allocation` si no se fija una normalización/primalidad.

## 4. Tabla de evidencia para próximos commits

- **DEMOSTRADO (SHA `3be17cc4`):** raíz única SOURCE, residual nulo y prefijo reducido de 33 ecuaciones; test exacto de intervalos, positividad real y bancaria, régimen de colateral de H/L y condición laboral inicial, con Lean/axiomas, build y QA editorial verdes.
- **CANDIDATO (este commit, hasta CI verde):** contrato ExactRootOn con Phi fijado al residual fuente, unicidad explícita de la tasa nombrada y puente condicional hacia boundaryEquilibriumSpec dada una asignación completa de frontera.
- **PENDIENTE:** testigo global `X`, suficiencia individual, Bellman bancario, transversalidad y todos los mercados; en particular `boundaryEquilibriumSpec` como afirmación económica de la proposición 4.1.
- **NUMÉRICO:** IRF y pruebas de horizonte finito, no evidencia de equilibrio infinito ni de crecimiento tendencial permanente.

**Próxima tarea aceptable:** primer lema sobre un portador explícito y sus campos de fecha cero, con cuantificadores de historias visibles. No etiquetar este documento ni el manuscrito como «cierre definitivo» del equilibrio hasta descargar las obligaciones de las secciones 1–3.
