# IE Project 18 — nueve factores nivel/log en raiz congelada y ledger 8+16+9 (12-XI-2026)

## Estado verificado de 24 filas

El workflow `build` del commit `57bdfc6db41d0a6ba2d2c4faf12551f91c9b45c6` concluyó `success` ([run 43267006602](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/43267006602)). Su registro documenta en ambas ramas los errores máximos de las 16 filas no empresariales: `1.6588293239028218e-16` en niveles transcritos y `1.280171524342677e-10` en derivadas direccionales de diferencias finitas. Con las ocho filas de firmas ya verificadas, hay **24 filas SOURCE-shaped candidatas**, todas evaluadas en el mismo estado fijo `frozen_stationary_seed(steady_case())`.

## Nuevo auditor para los nueve residuos de escala

Se incorporó `code/irf/audit_frozen_nine_scalar_source_shapes.py`. Recalcula directamente los residuos en niveles del SOURCE transcrito sobre la misma base congelada y misma regla `P0`, con filas `4,5,6,9,10,21,22,25,26`:

- Regímenes de las firmas H/L en fecha cero (pignoración en niveles, o condición de holgura L).
- Transición nominal de la cara bancaria, ecuación de oferta laboral y Euler del hogar en ambas fechas.
- Condición común de pignoración nominal en fecha uno.

Para cada ratio positivo `r = actual/predicho` con `g = log(r)`, la identidad **fuera de la raíz** es `actual-predicho = predicho*expm1(g)`. Para el residuo Euler `1-r`, es `1-r=-expm1(g)`. Este cálculo es esencial: un factor `1/predicho` constituye el transporte **lineal en una raíz común**, pero no reemplaza la identidad no lineal fuera de la raíz.

En la rama `slack` de fecha cero, el residuo de la firma L se expresa como `r-1`, con `r=loanRate*entrepreneurSDF/inflationNext`. En fecha uno se impone la rama `binding` a ambas firmas.

El auditor compara las nueve filas con los residuos logarítmicos originales del motor Python en tres coordenadas de prueba, dos ramas y 33 direcciones centrales alrededor de un punto no trivial. Exige errores inferiores a `2e-10` en los niveles y `5e-7` en las derivadas; conserva hashes de SOURCE, Python y `P0`.

**Estado:** PENDIENTE de observar `build=success` del commit `e5713f8...` o posteriores.

## Ledger de cobertura candidata 8+16+9

Se añadió `code/irf/audit_frozen_33_candidate_partition.py`, integrado en `code/verify.py`. Este módulo coteja los tres JSON generados, sus hashes SOURCE/Python/P0, su base y ramas, y exige una **partición disjunta exacta de las 33 filas SOURCE**. La salida es `frozen_33_source_shaped_candidate_partition.json`, archivada por GitHub Actions. Si el último CI pasa, podrá reportarse `33/33 SOURCE-shaped candidate rows tested at a common frozen base`, **nunca** equivalencia económica SOURCE–Python.

La misma fuente `EconomicModel.lean` no se evalúa en Python y las transcripciones se construyen utilizando expresiones compartidas del motor Python. Esto produce evidencia de consistencia interna de las fórmulas candidatas y no una verificación externa independiente de los originales en Lean.

## Diferencia con los otros resultados Lean

Los resultados fiscales Lean que comparan `P(G),I(G)` y `P(H),I(H)` son teoremas sobre el verdadero operador SOURCE reducido de 33 filas. **No** certifican que la carta Python, la continuación lineal `P0`, la normalización de filas ni las matrices numéricas correspondan exactamente al mismo operador SOURCE. Tampoco demuestran soluciones en la rama holgada ni equilibrio completo.

## Obligaciones tras la cobertura candidata

1. Especificar y demostrar una identidad funcional abierta `F_py(z)=T(z)F_source(psi(z))` con el mismo estado, ramas, anuncios y continuación. La derivada de `T(z)` produce un término adicional que se anula solo en una raíz común.
2. Construir la matriz SOURCE económica del mismo punto; verificar la norma de una inversa mediante errores de aritmética certificados o pruebas formales.
3. Cerrar el modelo completo (KKT, restricciones agregadas y fiscales, terminalidad, existencia del equilibrio de horizonte infinito) y, separadamente, demostrar los efectos de política monetaria y crecimiento de largo plazo.

PR #2 permanece draft, sin fusionar `main`.
