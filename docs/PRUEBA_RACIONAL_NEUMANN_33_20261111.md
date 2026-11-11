# IE Project 18: compuerta racional exacta de perturbación matricial (11-XI-2026)

## Objetivo

Evitar la inferencia errónea de que un Jacobiano económico está certificado solo porque se construye una matriz candidata invertible en punto flotante. La proposición condicional relevante es:

Sea `M` cuadrada invertible y `E` una perturbación. Si `q=||M^{-1}E||_∞<1`, entonces `M+E=M(I+M^{-1}E)` es invertible por la serie de Neumann y

`||(M+E)^{-1}||_∞ <= ||M^{-1}||_∞/(1-q)`.

El mismo razonamiento se aplica en dimensión 33 y en otras dimensiones. La condición es **suficiente, no necesaria**: si `q>=1`, no sabemos si `M+E` es singular sin información adicional.

## Prueba agregada a CI

`code/irf/test_exact_neumann_33.py` usa únicamente `fractions.Fraction` de la biblioteca estándar. Construye exactamente `M=(I+K)D`, donde `D` tiene 33 factores racionales no nulos y `K` es un shear con dos filas empresariales y una columna de garantía. Comprueba `K²=0`, `M M^{-1}=I`, `M^{-1}M=I` y evalúa la cota de Neumann sin redondeo binario.

Incluye dos controles negativos: una perturbación grande con `q>=1` y matriz resultante invertible por dominancia diagonal estricta; y la perturbación `E=-M`, que produce una matriz singular. Así se comprueba que el test no trata erróneamente `q>=1` como sinónimo de singularidad.

El workflow `editorial-qa.yml` ejecuta ahora la prueba. Debe comprobarse el run y SHA exacto antes de registrarlo como ejecutado satisfactoriamente.

## Frontera epistemológica

**DEMOSTRABLE EN MATEMÁTICAS:** proposición general de la serie de Neumann y sus hipótesis.

**PRUEBA DE CÓDIGO:** aritmética racional de una matriz sintética; no usa los residuos SOURCE ni el Jacobiano de Python.

**PENDIENTE EN EL MODELO:** identificar un `M` riguroso procedente del verdadero `DF` o `DG`, demostrar su inversa con cotas certificadas, construir `E=DR` sobre la misma carta y demostrar `q<1` con intervalos dirigidos. Nada de esto se obtiene de `test_exact_neumann_33.py`.

También siguen pendientes el cierre KKT de 34 relaciones, suficiencia de las condiciones, estado heredado común, terminalidad, equilibrio infinito y consecuencias de crecimiento.

No confundir los resultados de frontera común `make_boundary` con dos equilibrios dinámicos distintos. Mantener PR #2 como borrador; no fusionar `main`.
