# Resultados, evidencia y alcance de las proposiciones

**Primera compuerta científica — 7 de noviembre de 2026.** Revisión desde el checkpoint de 71 módulos candidatos Lean y del experimento reproducido en la rama de trabajo. Este documento es un inventario de afirmaciones, no una certificación global del equilibrio. La escala de evidencia se fija como **DEMOSTRADO** (enunciado formal exacto), **NUMÉRICO** (experimento reproducible con límites explícitos) y **PENDIENTE** (correspondencia/afirmación no acreditada).

## 1. Pregunta científica y hechos antes de las hipótesis

Queremos saber si los instrumentos de implementación monetaria pueden modificar la liquidez bancaria, abaratar el crédito y desplazar capital hacia empresas tecnológicamente más productivas que afrontan restricciones financieras. Sin embargo, ni la reducción del spread ni el aumento del volumen de crédito garantizan una mejora asignativa de equilibrio: también cambian los recursos propios, los precios de activos, el consumo y las expectativas. La rama B del experimento actual es un contraejemplo numérico al argumento favorable incondicional: el crédito de H aumenta, pero su inversión disminuye y su multiplicador normalizado se eleva.

El modelo describe remuneración de reservas, cantidad de reservas, corredor y encaje. **La única IRF de política completa disponible corresponde a la innovación negativa de remuneración**; la tasa interbancaria es endógena, y la etiqueta «tasa de política independiente» requeriría otra ecuación de implementación. La acumulación de capital permite estudiar transiciones dinámicas; no se ha demostrado todavía una tasa de crecimiento tendencial permanentemente mayor.

## 2. Resultados y fronteras de demostración

| Objeto y afirmación | Fuente literal | Evidencia de la revisión | Estatus permitido |
|---|---|---|---|
| Firmas heterogéneas: H más productiva, menos pignorable y de menor escala | paper/paper.tex, eq:production; finite_irf.py, steady_case() | Script audit_firm_scale.py: A_H=1.01>A_L=1; θ_H=.15<.4; k_H≈11.67383<19.39434; Y_H≈2.21218<3.25497 | **NUMÉRICO: solo ancla estacionaria ilustrativa.** La ordenación debe revisarse en la frontera perturbada. |
| Restricción crediticia permite una capacidad máxima, condicional en recursos y precios | eq:kmax y prop:v0m_original_6_3 | Derivada parcial escrita y verificable algebraicamente en paper | **ARGUMENTO ANALÍTICO CONDICIONAL.** No es derivada total del capital óptimo. |
| Matching OTC, corredor y condiciones de precios bancarios | eq:surplus, eq:IBclearing, eq:IBrate, eq:bankFOCL, eq:bankFOCD | Diagnósticos transmission_trace y financial_blocks_audit | **NUMÉRICO** a lo largo de las trayectorias; suficiencia de la política bancaria completa pendiente. |
| Dos soluciones cercanas con conjuntos activos S/B para una innovación negativa | eq:scalar_macro_complementarity y eq:negative_schur | Jacobianos, signos, márgenes y salidas de finite_irf_validation.json | **LOCAL/REDUCIDO CONDICIONAL.** No se identifica automáticamente con equilibrio competitivo infinito. |
| Literal de prop:local_macro_multiplicity: exactamente dos equilibrios completos | Paper, sección La complementariedad produce dos equilibrios locales | result_ledger.json: formalization_status=not_run; IRF: full_infinite_equilibrium_established=false | **PENDIENTE DE RECONCILIACIÓN.** Demostrar el puente dinámico o enunciar un teorema reducido más débil. |
| Capital y préstamo admiten un multiplicador común construido | DateZeroJointBindingSharedDualCandidate.lean, firmOptimal_sourceCalendar_binding_exists_shared_capitalLoanMultiplier | Compilación y auditoría de axiomas especializados de Lean | **DEMOSTRADO CONDICIONALMENTE** dado FirmOptimal, calendario determinista, capital interior, tasa positiva, unidad de garantía positiva e inflación futura no nula. No demuestra FirmOptimal para la IRF. |
| Existe una asignación primalmente equivalente con dual KKT normalizado | DateZeroBindingDualRepairCandidate.lean, firmOptimal_binding_exists_primalEquivalent_jointKKT_carrier | Lema compilado con hipótesis literales | **DEMOSTRADO CONDICIONALMENTE**. Para conservar dual estrictamente positivo hace falta brecha marginal estricta. |
| El campo dual almacenado no es identificado por FirmOptimal | DateZeroBindingDualFreedomCandidate.lean, not_all_bindingFirmOptimal_have_sourceCapitalEuler | Lema compilado y revisión de axiomas | **DEMOSTRADO CONDICIONALMENTE**, indicando que el dual originalmente almacenado puede variar preservando primales. |
| Shock de remuneración: crédito H ↑ en S/B; inversión H ↑ en S, ↓ en B | finite_irf.py, reproduce.py; paper/figures/irf_real_allocation.pdf | Newton del prefijo de 33 incógnitas, cola lineal local y contrastes no lineales finitos hasta T=640 | **NUMÉRICO DEL REDUCIDO**, sin estimación empírica ni selección de rama. |
| Producto inicial negativo | eq:nkpc, Euler, trabajo; DIAGNOSIS_STATUS.md | Persistencia de signos con T=640 y dos cierres terminales; reporte de transmisión | **NUMÉRICO + DESCOMPOSICIÓN CONTABLE**. No descomposición causal independiente. |
| Mejora permanente de crecimiento | Acumulación de capital y resultados de asignación condicional | No hay un motor demostrado de crecimiento endógeno sostenido | **PENDIENTE**, sujeto a extensión teórica o a reformular como trayectoria de nivel/transición. |

## 3. La empresa H sí es pequeña en un ejemplo específico

La función steady_case() genera, con parámetros ilustrativos, el siguiente ancla:

| Variable por firma | H | L |
|---|---:|---:|
| Productividad tecnológica | 1.01000 | 1.00000 |
| Pignorabilidad | 0.15000 | 0.40000 |
| Capital instalado | 11.67383 | 19.39434 |
| Producción por firma | 2.21218 | 3.25497 |
| Principal de préstamo | 1.70806 | 7.56717 |

De aquí se obtiene \(k_H/k_L\simeq0.60192\). El resultado responde a la preocupación sobre tamaño: H es más productiva y tiene menos capital **en esta construcción**. No se deduce de \(A_H>A_L\) por sí solo, ni basta para atribuir causalmente toda la diferencia a θ. El contraste de frontera y las series perturbadas quedan como pruebas independientes.

La identidad empresarial relevante, cuando la garantía está activa, los depósitos empresariales son nulos y el denominador es positivo, es:

\[
 k'_{i,t}=\frac{N_{i,t}-c_{i,t}}{q_t-H_{i,t}/R_t^L}.
\]

Por consiguiente, un aumento de crédito y una reducción de tasas pueden coexistir con menor inversión cuando cae suficientemente \(N-c\) u otros precios alteran el denominador. Este resultado se prueba a partir de presupuesto y colateral, no por una flecha decorativa.

## 4. Un cuidado indispensable con el spread

La condición interior de la empresa bancaria, **con dual de límite de préstamos**, es

\[
R_t^L-R_t^R=\mathbb E[\chi'_t(s_t^B)]+\nu_{L,t}.
\]

Por tanto, la igualdad abreviada \(R^L=R^R+\overline{\chi}\) exige declarar \(\nu_L=0\); no es una identidad válida para toda esquina. Distinguimos el rendimiento interbancario \(R^F\), la remuneración \(R^R\) y la tasa bancaria \(R^L\), que son objetos distintos.

## 5. Decisiones de cierre científico

Primero, formalizar un teorema **del sistema reducido** con sus supuestos precisos y no llamarlo equilibrio global por similitud del nombre. Segundo, completar la comparación de los 57 resultados del registro con las 71 unidades Lean candidatas sin inferir cobertura uno a uno. Tercero, validar los diagramas contra el catálogo de ecuaciones y cronología del paper. Cuarto, distinguir la pregunta de crecimiento sostenido —todavía abierta— de las transiciones y de la pérdida asignativa condicional.

**No se fusiona a main ni se publica como resultado final de equilibrio completo mientras haya una contradicción entre alcance escrito y evidencia disponible.**
