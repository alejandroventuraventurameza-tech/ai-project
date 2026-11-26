# IE Project 18 — diagnóstico flotante del Jacobiano congelado (12-XI-2026)

## Resultado formal comprobado antes de este commit

En el SHA `8d477e8f50a4397bd4bf766f024f176e168a2a22`, los ocho workflows principales terminaron correctamente, incluido el [workflow Lean #43241475013](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/43241475013). Quedaron comprobadas las equivalencias de operadores SOURCE estacionarios entre `G,H`, su igualdad de derivadas de Fréchet, transporte del predicado **condicional** de inversa acotada y equivalencia del lugar de ceros de las 33 ecuaciones reducidas con la misma carta, rama y continuación.

**Eso no constituye una prueba de que el Jacobiano económico SOURCE esté invertido:** el teorema transporta el valor lógico de un predicado, no crea un testigo `Jinv`.

## Nuevo cálculo reproducible, con alcance delimitado

Se añadió `code/irf/audit_frozen_python_jacobian_float_diagnostic.py`, integrado en `code/verify.py` y archivado por el workflow `build.yml`. El código construye exactamente la instancia que ya usa `frozen_stationary_prefix_audit.py`:

- `s=steady_case()`, `base=frozen_stationary_seed(s)` y el `P0` 16×6 existente;
- rama `binding`; cuatro anuncios de política iguales a cero y coordenadas logarítmicas cero;
- operador `F_py(z)=finite_irf.prefix_residual(base,P0,"binding",(0,0,0,0),z)`.

Calcula los 33 residuos `F_py(0)`; aproxima tres Jacobianos centrales a pasos relativos `2e-5`, `2e-6`, `2e-7`; construye una inversa aproximada de la matriz del paso medio mediante 33 sistemas pivoteados; evalúa las discrepancias `||A A_approx_inv-I||_max` y `||A_approx_inv A-I||_max`, la norma infinito del inverso flotante y el desplazamiento máximo de entradas al cambiar el paso.

**Compuerta numérica:** base `||F_py(0)||∞<10^-9`, pivotes positivos por encima de `10^-15` y productos de inversa con error absoluto por entrada menor a `10^-5`; se exige finitud a todos los valores calculados. Esos umbrales son diagnósticos de regresión, **no** un encierro dirigido ni garantía de error global.

El nuevo informe JSON identifica hashes del SOURCE, `finite_irf.py` y `rational_preconditioners.json`, y declara explícitamente `source_jacobian_equality_proved=false`, `interval_inverse_enclosure_proved=false` e `infinite_horizon_equilibrium_or_growth_proved=false`.

## Distinción formal necesaria

El predicado SOURCE original `LocalReducedPrefixLogJacobianCertifiedAt` requiere continuidad/diferenciabilidad en una bola logarítmica y una inversa lineal continua del **fderiv real** del operador SOURCE, con dos identidades exactas de inversa y cota estricta `||Jinv||<B`.

Ni la matriz flotante de diferencias centrales ni su inversa obtenida por Gauss-Jordan cumplen automáticamente esos requisitos. Tampoco se ha establecido la identidad funcional `F_py=T F_source∘psi` en una vecindad, ni el transporte de los índices y del `tail` bajo esa igualdad. Por tanto, la nueva tabla de diagnóstico se reportará como **NUMERICO**, no DEMOSTRADO.

## Obligación siguiente

Formalizar la transcripción de las 33 filas SOURCE, la conjugación de las cartas positiva/logarítmica, las diferencias de nivel/log en los residuos (incluyendo las cizallas Euler del régimen) y el mapeo exacto de `tail`. Luego obtener cotas intervalares estrictas del Jacobiano SOURCE en una vecindad, evitando elevar una condición numérica de rango a un teorema IFT.

El nuevo cálculo se ejecutará mediante CI del SHA con el script; no declarar éxito hasta observar `build=success` y el artefacto JSON.

PR #2 sigue borrador. Sin fusión de `main`.
