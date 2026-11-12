# IE Project 18 — ocho filas de firmas evaluadas en la misma base congelada (12-XI-2026)

## Cambio de diseño de la auditoría

Los diagnósticos anteriores estudiaban dos problemas numéricos no intercambiables: (a) el puente condicional SOURCE–Python de ocho filas de firmas para la frontera `make_boundary(s)`, y (b) el Jacobiano de 33 filas calculado en `frozen_stationary_seed(steady_case())`. La barrera de procedencia `audit_jacobian_cross_baseline_firewall.py` impide combinarlos para declarar una inversa económica inexistente.

Este incremento **repite únicamente las ocho filas de firmas** de la transcripción condicional SOURCE en la MISMA base `frozen_stationary_seed(steady_case())` y el mismo `P0` 16×6 que emplea `audit_frozen_python_jacobian_float_diagnostic.py`.

La nueva auditoría `code/irf/audit_frozen_firm_row_same_base_candidates.py` evalúa las ramas `binding` y `slack`, los puntos `z=0` y dos perturbaciones vectoriales pequeñas, y las 33 derivadas direccionales coordenadas por diferencias centrales sobre un punto no trivial, junto con la transcripción de las filas de firmas y las dos cizallas Euler. Verifica el residuo común de pignoración en la coordenada Python 21 y coteja la identidad residual SOURCE-transcrita = Python + cizalla condicional.

Los criterios numéricos son, respectivamente, error de fila y de cizalla menor a `2e-10`, error direccional menor a `5e-7` y coincidencia del residuo común dentro de `2e-11`. El informe incluye hashes de `EconomicModel.lean`, `finite_irf.py`, `rational_preconditioners.json` y el código de transcripción.

## Alcance probatorio exacto

Se trata de una auditoría de **transcripción Python guiada por expresiones del SOURCE**, sin ejecutar el operador económico Lean en el mismo punto. El auditor **no** demuestra igualdad funcional del SOURCE original ni identidad de sus derivadas con las de Python, **no** comprueba los otros 25 residuos en esa misma base y **no** construye una inversa certificada del Jacobiano SOURCE.

No aplicar aquí shocks monetarios directos, ya que el transcriptor de firmas invocado no recibe la tupla de cuatro intervenciones. Las comparaciones se limitan expresamente a anuncios nulos y a una base fija, con dos ramas numéricas.

El módulo se ejecuta desde `code/verify.py` y el workflow `build.yml` archiva el reporte `frozen-same-base-firm-row-candidates`. **Hasta que la ejecución del SHA de integración concluya, el resultado nuevo está PENDIENTE DE CI.**

## Próximas obligaciones

1. Replicar y auditar los 25 residuos restantes en el mismo estado heredado fijo, con idéntico calendario y misma continuación.
2. Sustituir las transcripciones Python por una vinculación formal de funciones del SOURCE en la carta positiva, incluida la derivada completa de las dos cizallas Euler dependientes del estado.
3. Solo tras demostrar una igualdad en una vecindad abierta, construir el Jacobiano económico SOURCE e intentar una cota de inversa con errores matemáticamente controlados.

Ni esta auditoría ni un posterior éxito de CI bastarían para declarar KKT, equilibrio infinito o efecto de crecimiento permanente.

PR #2 permanece en borrador; no fusionar `main`.
