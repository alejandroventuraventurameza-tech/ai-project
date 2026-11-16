# IE project — cierre de avance para la exposición del 18 de noviembre de 2026

**Corte editorial:** domingo 15 de noviembre de 2026 (Lima). **Tipo de entrega:** avance de investigación, no paper final ni certificado de equilibrio dinámico completo. **Decisión:** congelar el alcance científico y detener la apertura de nuevas campañas de Lean antes de la exposición. **Rama:** work/lean-ci-validation-source-33-row-20261114. **PR #2:** borrador; no fusionar main.

## Mensaje científico que sí podemos defender

Estudiamos un modelo monetario con bancos, pagos idiosincráticos, negociación interbancaria, rigidez nominal y dos firmas heterogéneas. H tiene productividad ilustrativa 1.01 y pignorabilidad 0.15; L, 1.00 y 0.40. La pregunta no es si todo estímulo mejora la asignación, sino en qué régimen financiero puede hacerlo y en cuál puede empeorarla.

Existe una definición económica formal del equilibrio dinámico y un sistema de prefijo de 33 ecuaciones / 33 coordenadas positivas (7+10+6+10) con continuación recurrente local. Se dispone de resultados numéricos para las ramas S (L inicialmente holgada; H vinculante) y B (ambas vinculantes). **No se ha demostrado existencia de un equilibrio competitivo completo de horizonte infinito para esas ramas**. La continuación finita/local y la optimalidad necesaria no sustituyen esa demostración.

## Inventario conservado — no rehacer

| Pieza existente | Ruta | Evidencia y alcance |
|---|---|---|
| Modelo completo y definiciones | lean/checkpoint/modules/Ventura26LiquidityAllocation/EconomicModel.lean | Definiciones de hogares, firmas, bancos, OTC, política y equilibrio |
| Primitivas estacionarias SOURCE | lean/candidates/Ventura26LiquidityAllocation/StationaryPrimitivesCandidate.lean | Testigo de primitivas y admisibilidad verificado; no es un equilibrio dinámico completo |
| Sistema reducido de 33 filas | code/irf/finite_irf.py; code/irf/README.md | Prefijo local, dos ramas financieras y continuación |
| IRF S/B y tablas | code/irf/output/main; paper/figures; paper/irf_impact_table.tex | Experimento de remuneración de reservas, reproducible, parámetros ilustrativos |
| Robustez dinámica finita | code/irf/output/nonlinear_tail_comparison/REPORT.md | Soluciones conjuntas no lineales hasta T=640 y cierres terminales distintos |
| Bloques financieros y KKT necesarias | code/irf/output/financial_blocks_audit/REPORT.md | Condiciones financieras en trayectorias, no suficiencia competitiva global |
| Transmisión y NKPC/Euler | code/irf/output/transmission_trace/REPORT.md | Descomposición contable sobre solución conjunta, no efecto causal aislado |
| Auditorías Lean recientes | GitHub Actions 43775107518 | Transformaciones de filas y preservación condicional de inyectividad |
| Diagnóstico numérico jacobiano 33x33 | GitHub Actions 43789774665 | Inversión de matriz de diferencias finitas, no inversa intervalar del Jacobiano SOURCE |
| Paper y presentación preexistentes | paper/paper.tex; paper/paper.pdf; slides/final.tex; slides/final.pdf | Borradores utilizables como anexos técnicos, no entrega final |

## Resultado numérico central de la exposición

Experimento identificado: innovación inicial v_R,0 = -0.00001 en la regla de remuneración de reservas (aproximadamente -0.1 punto básico). Encaje fijo rho=0.10; no nuevos shocks posteriores. Parámetros ilustrativos, no estimaciones para Perú. Las dos ramas se comparan condicionalmente, sin regla endógena de selección.

| Respuesta de impacto | S | B |
|---|---:|---:|
| Tasa de crédito (pb) | -0.06363175 | -0.09090760 |
| Crédito de la firma H (log %) | +0.00109518 | +0.00084065 |
| Capital elegido por H para t+1 (log %) | +0.00016409 | -0.00107264 |
| Producción corriente (log %) | -0.00003580 | -0.00414255 |
| Pérdida asignativa condicional (100 Delta log) | -0.00000248 | +0.00000852 |

Lectura: el crédito H sube en ambas ramas, pero su capital elegido sube solamente en S. Esto muestra que crédito, inversión y relajación del multiplicador de colateral no son equivalentes. Los resultados se refieren al sistema reducido y al escenario especificado, no a una política óptima o a un resultado causal general.

La robustez con ecuaciones interiores no lineales hasta T=640 reproduce la caída inicial del producto y sus diferencias por rama. Con cierre terminal de gráfica estable, producción inicial T=640: S -0.00003559159239 log %, B -0.004142220876 log %. Cierres distintos muestran mayor sensibilidad a horizontes cortos.

## Qué verificó Lean y qué no

**DEMOSTRADO condicionalmente en Lean:** cronología y estructuras SOURCE, admisibilidad de primitivas estacionarias, identidades financieras, derivaciones relevantes de colateral/Euler, equivalencias de ceros y transformaciones invertibles bajo sus hipótesis, preservación de inyectividad del operador jacobiano bajo transformaciones de filas. Referencia última: run 43775107518 éxito.

**NUMÉRICO reproducible:** dos soluciones del sistema reducido por conjunto activo, IRF S/B, residuos de prefijo, pruebas no lineales T<=640, auditoría conjunta 33x33 de filas normalizadas (1,089 entradas; diferencia máxima ≈2.31e-10), diagnóstico de la inversa de la matriz de diferencias finitas (condición infinito ≈22,781.60; residuos de producto inverso ≲4.2e-13).

**PENDIENTE fundamental:** equivalencia funcional exacta SOURCE–Python sobre una misma historia, mismo punto base y regla terminal; existencia de raíz SOURCE validada; invertibilidad del Jacobiano matemático original mediante cotas certificadas; optimalidad dinámica competitiva de bancos y firmas, factibilidad y cierre fiscal completo, transversalidad, determinación/selección S/B y extensión de horizonte infinito. La raíz de frontera aumentada obtenida para un valor h positivo no certifica automáticamente IRF cuyo shock anunciado fue negativo; no combinar raíces de bases distintas.

## Alcance de los instrumentos

SOURCE contempla variaciones iniciales de remuneración de reservas, cantidad de reservas prepagos, coeficiente de encaje y amplitud del corredor. **La IRF principal ya publicada corresponde a remuneración de reservas**, no a cuatro IRF equivalentes. No se ha agregado una tasa de referencia headline independiente ni una regla de compras de activos del banco central con balance de stocks/flujos. Ver docs/INSTRUMENTOS_MONETARIOS_ALCANCE_EXTENSION.md.

## Crecimiento: afirmación que debemos evitar

El núcleo tiene productividad de firmas dada, sin ley de innovación endógena financiada con crédito. Una mejora de asignación puede elevar el producto transitorio o su nivel de largo plazo, pero **no prueba un aumento de la tasa de crecimiento tendencial de largo plazo**. Ver docs/CRECIMIENTO_VERSUS_NIVEL_CONDICIONAL.md.

## Plan de exposición recomendado

1. Problema e intuición económica (productividad vs colateral).
2. Agentes, tiempos y cuatro instrumentos en la arquitectura; identificar el único shock de las IRF.
3. Restricción de colateral y Euler; ramas S/B.
4. Sistema reducido 33x33 y procedimiento numérico.
5. Resultados S/B (tasas, crédito, capital y pérdida asignativa).
6. Mecanismo: crédito no equivale a inversión; recursos propios y precio efectivo.
7. Dinámica, robustez T=20..640 y transmisión Euler–Phillips.
8. Evidencia Lean y auditorías, con jerarquía DEMOSTRADO / NUMÉRICO / PENDIENTE.
9. Brecha hacia equilibrio competitivo dinámico completo.
10. Próximas tres tareas delimitadas: (i) correspondencia semántica SOURCE–Python sobre una base única; (ii) certificado de raíz/derivada y suficiencia económica; (iii) IRF estructurales y extensión de crecimiento como fase posterior.

## Compromiso de cierre del día

No modificar ecuaciones ni parámetros, no reabrir campañas de prueba nuevas, no fusionar la PR borrador, no recalificar resultados. Preservar los archivos ya generados y presentar el trabajo actual como **avance avanzado de modelo, verificación formal parcial y soluciones dinámicas reducidas reproducibles**. El objetivo del miércoles es discutir resultados y recibir observaciones, no afirmar un teorema de equilibrio infinito que aún no existe.
