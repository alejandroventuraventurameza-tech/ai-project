# SOURCE–Python: puente bancario realizado/objetivo (obligación de prueba)

Estado: **identidad algebraica de trabajo; NO certificado Lean para el mapa económico completo**.
Fecha de trabajo: 2026-11-14 (America/Lima). No se afirma existencia de raíz SOURCE, regularidad de 33x33 ni validez de IRF.

## 1. Variables y alcance

Sea `x` el vector de los demás argumentos económicos compartidos entre formulaciones. Denótese:
- `R > 0`: tasa de reservas realizada SOURCE; `T(x) > 0`: objetivo de la regla de tasa.
- `M > 0`: reservas realizadas SOURCE; `N(x) > 0`: objetivo de la regla de cantidad.
- `u = log(R/T)`, `v = log(M/N)`: residuos de las respectivas reglas de política.
- `k(x,r) = 1 / reserveDepositRatio(x,r) - 1`, cuando el cociente esté bien definido.
- `C(x)`: todos los términos comunes de oferta de préstamos menos deuda bancaria real; comprobar esta hipótesis con los códigos completos antes de identificar la fila Python.

Si la fila SOURCE es `B_s = C(x) - k(x,R) M` y la fila objetivo es `B_t = C(x) - k(x,T) N`, entonces, para todo estado de sus dominios:

`B_t - B_s = k(x,R) (M-N) + [k(x,R)-k(x,T)] N`.

Utilizando las reglas monetarias SOURCE:

`B_t - B_s = k(x,R) N (exp(v)-1) + [k(x,R)-k(x,T)] N`.

Esta es una **descomposición exacta fuera de la raíz**, no una aproximación, pero NO certifica que la fila Python completa tenga exactamente la estructura hipotética `B_t`.

## 2. Jacobiano en una raíz común

Si `u=v=0`, `R=T`, `M=N`, `k` es diferenciable respecto de `r` y todos los argumentos `x` son idénticos en ambas evaluaciones, entonces la diferencial respecto del vector conjunto de coordenadas `z` satisface:

`D(B_t-B_s) = k(x,R) N Dv + N (partial_r k)(x,R) R Du`.

Las derivadas de `x` que ingresan simétricamente en `k(x,R)` y `k(x,T)` se cancelan al evaluar la raíz común. En particular, la diferencia de jacobianos es una combinación lineal de **dos filas de política monetaria**. No es, en general, una transformación diagonal constante de filas.

Para usar esta igualdad en una prueba de rango:
1. Identificar los índices exactos de las reglas `u,v` en el vector SOURCE de 33 residuos.
2. Verificar las escalas/normalizaciones de las filas bancarias originales (niveles frente a log-ratios).
3. Demostrar que la corrección de fila equivale a operaciones elementales invertibles en el punto; los factores y dominios deben ser explícitos.
4. Obtener un puente análogo para precio de depósitos, precio de préstamos y pendientes OTC; no reutilizar el resultado parcial como puente completo.
5. Después demostrar el bloque `A` invertible, la transversalidad Schur y una raíz SOURCE rigurosa, antes de aplicar el teorema de función implícita.

## 3. Ledger de evidencia

- **DEMOSTRADO en módulos Lean previos, bajo hipótesis declaradas:** identidades parciales de sustitución realizado/objetivo; equivalencia del conjunto de ceros bajo seis normalizaciones no lineales sobre el mismo vector SOURCE. Véanse `SourceReserveRuleTargetSubstitutionCandidate.lean` y `SourceSixNonlinearLogRowRootTransportCandidate.lean`.
- **DERIVACIÓN MATEMÁTICA NO FORMALIZADA AQUÍ:** identidad abstracta `B_t-B_s` y diferencial condicionado arriba.
- **PENDIENTE:** verificar correspondencia fila por fila con el auxiliar Python original y formalizar el nuevo puente en Lean; cotas rigurosas para raíz, jacobiano, condición Schur e IRF.
- **PROHIBIDO INFERIR:** que la normalización de seis filas prueba la equivalencia de las otras 27, que Python objetivo = SOURCE realizado fuera de raíz, o que CI verde implica equilibrio.

## 4. Criterio de cierre

No marcar el puente SOURCE–Python como resuelto hasta que el código certifique la transformación completa de las 33 filas, con las seis filas bancarias afectadas por sustituciones de objetivos explicitadas y la diferenciabilidad de sus coeficientes validada. Una raíz ilustrativa Python con residuo pequeño no sustituye una raíz SOURCE con cotas rigurosas.
