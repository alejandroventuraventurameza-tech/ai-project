# Del sistema reducido al equilibrio: trazabilidad del puente lógico

**Fecha de revisión:** 7 de noviembre de 2026. **Rama:** work/lean-ci-validation-otc-20261106. **Objeto:** distinguir el sistema de 33 ecuaciones, la complementariedad escalar, las condiciones óptimas de los agentes y el equilibrio competitivo infinito.

## 1. Teorema reducido frente a equilibrio completo

El código resuelve por separado \(F_r(Z,v_R)=0\), con 33 logincógnitas y \(r\in\{S,B\}\). Bajo un Jacobiano local invertible, la restricción de L se reduce a

\[
0\le s\ \perp\ \mathcal M(s,h)\ge0,\qquad h=v_R,\quad
\mathcal M(s,h)=a_Rh+bs+o(|s|+|h|),
\]

donde el caso auditado reporta \(a_R\simeq-3.219277533\) y \(b\in(-2.376742673,-2.376742670)\). Si, adicionalmente, la marginal reducida es continua, estrictamente decreciente en \(s\ge0\) y posee una raíz interior positiva para \(h<0\), las únicas soluciones escalares son B (\(s=0\)) y S (la raíz positiva). Para \(h>0\), si \(\mathcal M(0,h)<0\), no hay solución complementaria no negativa en el entorno decreciente.

El módulo nuevo **ScalarComplementarityMultiplicityCandidate.lean** formaliza precisamente la conclusión escalar bajo **premisas explícitas**: monotonía estricta, signo en cero y existencia previa de una raíz positiva. No deriva esas premisas del modelo económico, no prueba el IFT del prefijo y no certifica un equilibrio DSGE. Compilación **aprobada** en GitHub Actions, ejecución 42430587348, commit ab86ddfc0b9220ff7aa7f8fe8fa3856cfe4f182b, bajo Lean 4 v4.30.0-rc2 con dependencias fijadas. El registro específico de este módulo muestra para ambos teoremas únicamente los axiomas estándar `propext`, `Classical.choice` y `Quot.sound`; no aparece `sorryAx`. El teorema formal usa monotonía en todo el semieje `[0,∞)`, hipótesis **más fuerte** que la monotonía local del argumento escrito de la Proposición 4.2. Por ello el teorema compilado no constituye todavía una formalización exacta de toda la proposición del manuscrito.

## 2. Obstrucción lógica identificada en Lean

La interfaz fuente **PaperInterface.localMacroMultiplicitySpec** pide unicidad literal de una estructura Allocation. Pero **CompetitiveEquilibrium** no restringe el campo collateralDual: el teorema **competitiveEquilibrium_replaceCollateralDual_iff** muestra que puede cambiarse sin alterar el equilibrio. Consecuentemente, **ContinuationContractAuditCandidate.not_localExactContinuationAround** refuta la unicidad literal del carrier, y **Proposition42RefutationCandidate.localMacroMultiplicitySpec_false** demuestra que la especificación fuente de la Proposición 4.2 es inalcanzable.

La refutación concierne a la **especificación formal literal**, no demuestra que las dos ramas económicas S/B sean imposibles. **Proposition42PrimalRepairCandidate.localMacroMultiplicityPrimalSpec** propone comparar asignaciones tras borrar el dual libre, y **Proposition42PrimalSeparationCandidate.strict_slack_and_binding_primal_disjoint** distingue ambas ramas por holgura y cobertura activa en historias admitidas. La reparación está aún **sin testigo de existencia de ambos equilibrios**.

## 3. Matriz de obligaciones y evidencia

| Implicación requerida | Evidencia concreta | Estado autorizado |
|---|---|---|
| Construir estados y reglas monetarias del caso | finite_irf.py, finite_bridge_certificate.json | NUMÉRICO/ALGEBRAICO, parámetros ilustrativos |
| Resolver 33 relaciones con S y B por separado | audit_prefix_rows.py, finite_irf_validation.json | NUMÉRICO DEL REDUCIDO |
| Justificar \(\mathcal M\), sus signos y raíz positiva | Ecuaciones scalar_macro_complementarity y negative_schur; certificados del enlace | ESPECÍFICO/CONDICIONAL, sin reflexión Lean integral |
| Probar que la complementariedad escalar tiene dos soluciones | ScalarComplementarityMultiplicityCandidate, bajo monotonía y existencia de raíz | LEMA CONDICIONAL; kernel debe validarse en CI |
| Recuperar KKT de empresas y posiciones bancarias | audit_financial_blocks.py, DateZeroJointBindingSharedDualCandidate | CONDICIONAL/NUMÉRICO; no prueba suficiencia global |
| Construir el prefijo literal del modelo | BoundaryFullPrefixCandidate.boundary_full_prefix_equations | Condicionado a BoundaryWorkerLaborPackage, paquete analítico y signos de la raíz |
| Elevar prefijo a equilibrio competitivo infinito | finite_prefix_equilibrium, colas y condiciones terminales | PENDIENTE: suficiencia y puente de todas las ramas |
| Contar exactamente dos equilibrios | PrimalRepairCandidate y PrimalSeparationCandidate | PENDIENTE: no contar estructuras con duales libres |
| Probar crecimiento tendencial permanente | Acumulación y asignación condicional | PENDIENTE: falta un mecanismo probado de crecimiento sostenido |

El padre estacionario formalizado en StationaryEquilibriumCandidate **no es** por sí mismo la instancia de frontera ni una IRF ante shock. La continuidad no lineal reducida T=640 y la recursión de valor bancario tampoco prueban optimalidad dinámica para todas las políticas admisibles.

## 4. Correspondencia exacta con los enunciados del paper

**Proposición 4.1 — frontera:** la existencia de raíz de recursos no basta para elevar el prefijo a equilibrio; entre las premisas específicas está la FOC laboral en fecha cero, todavía aislada en BoundaryWorkerLaborPackage.

**Proposición 4.2 — multiplicidad:** debe distinguir las dos raíces de la complementariedad reducida de la proposición adicional de dos **equilibrios completos**. La segunda no está certificada y su contrato Lean de unicidad literal es contradictorio. La noción candidata correcta identifica clases de asignaciones **primales en el soporte**, no estructuras completas con duales libres.

**Proposición 4.5 — persistencia bajo riesgo:** exige una cola exacta, estimaciones uniformes y factibilidad global; no es la misma cosa que una IRF con prefijo Newton y cola lineal local, ni que una solución finita T=640.

**Proposición de enlace del apéndice:** es una implicación condicional válida solo después de establecer las premisas de todas las KKT originales, optimalidad de hogares/bancos/minoristas, dominio, precio global y condiciones terminales.

## 5. Compuertas para una afirmación más fuerte

1. **Semántica:** igualdad de variables primales sobre historias admisibles y dual canónico cuando la KKT lo determine.
2. **Álgebra:** las 33 ecuaciones deben reconstruir todos los presupuestos, contratos, restricciones y márgenes originales.
3. **Dinámica:** continuación no lineal exacta con condiciones terminales y optimalidad global por agente.
4. **Formalización:** testigos de CompetitiveEquilibriumWithInitialIntervention para S/B; separación primal y unicidad **modulo** duales libres, con axiomas auditados al commit exacto.
5. **Edición:** resumen, proposiciones, prueba escrita, slides y ledger de 57 resultados no pueden atribuir a las IRF un teorema de equilibrio infinito que permanece abierto.

**Decisión:** mantener PR en borrador y main intacta; la afirmación comprobable hoy son respuestas de dos soluciones numéricas locales del sistema reducido, no una multiplicidad de equilibrios completos certificados.
