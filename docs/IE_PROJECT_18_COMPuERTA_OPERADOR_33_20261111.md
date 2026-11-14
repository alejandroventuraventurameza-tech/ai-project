# IE Project 18 — compuerta de equivalencia del operador de 33 filas (11-XI-2026)

## Estado comprobado en el árbol de trabajo

- El testigo estacionario de `Primitives LocalBridgePhase` ya existe en `StationaryPrimitivesCandidate.lean`: 37 campos y 22 obligaciones; no reconstruirlo.
- `StationaryInterventionSourceBridgeCandidate.lean` contiene pruebas candidatas sobre ley binaria, momento absoluto, renovación bancaria, funciones OTC para `tau <= 1`, estado heredado, proyección de cuatro instrumentos y sensibilidad directa del encaje. **El archivo y su sintaxis fueron inspeccionados, pero esta entrada NO certifica una ejecución verde del SHA actual**; usar la ejecución focalizada y revisar `#print axioms`.
- `audit_source_full_transform_candidate.py` construye `T=(I+K)D`, inversa `D^{-1}(I-K)` y determinant no nulo en dos trayectorias de la **misma frontera** `make_boundary`. Esto es una identidad de matrices **candidatas**, no un teorema sobre derivadas económicas de SOURCE.
- La auditoría publicada registra coeficientes `a_H=0.004160283832841957`, `a_L=0.011094090220911887`, error máximo de inversión `8.673617379884035e-19`. Los dos conjuntos de coeficientes iguales proceden de la frontera común; no usar como evidencia de dos raíces distintas S/B.

## Proposición matemática condicional que falta conectar al SOURCE

Sean `F: U -> R^33` (residuos SOURCE), `G: V -> R^33` (residuos Python), una carta diferenciable `psi: V -> U`, una permutación `P` y una transformación de filas diferenciable `T(z)`. **Si se demuestra la identidad funcional en un entorno abierto**

`G(z) = P T(z) F(psi(z))`,

y `F(psi(z_*))=0`, entonces por regla del producto:

`DG(z_*)=P T(z_*) DF(psi(z_*)) Dpsi(z_*)`.

Por tanto, si `P`, `T(z_*)` y `Dpsi(z_*)` son invertibles, `DG(z_*)` es invertible **si y solo si** `DF(psi(z_*))` lo es. Este argumento **no prueba ninguna de las dos invertibilidades por sí solo**.

Una versión más general permite `G(z)=P T(z) F(psi(z)) + R(z)` únicamente cuando se han demostrado simultáneamente `R(z_*)=0` y `DR(z_*)=0`. Controlar solo `R(z_*)` o comparar cifras redondeadas no basta.

**Atención:** el programa existente construye una matriz constante `T` evaluada en la raíz de una frontera común, pero no certifica la identidad funcional de arriba para la totalidad de los residuos ni el jacobiano exacto; no reetiquetar ese chequeo como demostración.

## Cota algebraica explotable sin confundir su objeto

Para `D=diag(lambda_i)` con factores no nulos y `K[19,21]=-a_H`, `K[20,21]=-a_L`, `K^2=0`:

`T^{-1}=D^{-1}(I-K)`.

Por tanto la norma infinito (suma máxima de valores absolutos de cada fila) de la inversa candidata es exactamente

`||T^{-1}||_inf = max( max_{i notin {19,20}} 1/|lambda_i|, (1+|a_H|)/|lambda_19|, (1+|a_L|)/|lambda_20| )`

cuando los índices 19, 20 y 21 son distintos, como aquí. La cota es **sobre T candidata**. No es una cota de `DF^{-1}` y no autoriza un radio de Newton-Kantorovich para el SOURCE.

## Siguiente ciclo verificable

1. Recuperar el estado y los logs de `lean-stationary-policy-payment-bridge.yml` para el SHA exacto que cambió el módulo; distinguir `kernel OK`, `sorryAx` y `no run`.
2. Construir un test que compare **los 33 valores de residuos en una misma carta y los 33 x 33 elementos de las derivadas**, perturbando cada coordenada en un dominio positivo y controlando las ramas OTC. En lugar de copiar coeficientes, medir `G(z)-PT(z)F(psi(z))` y su derivada residual para instancias separadas S/B con el **mismo predecessor heredado**.
3. Conectar cada una de las 33 filas al constructor SOURCE `LocalPrefixDateData`, comenzando por las dos filas Euler que incorporan el shear de colateral; verificar la cronología de instrumentos en fecha cero y dato heredado.
4. Solo después estudiar invertibilidad de `DF`, 34 condiciones KKT, optimalidad global/dinámica, terminalidad, equilibrio infinito y crecimiento. No declarar estos objetivos demostrados por un CI algebraico verde.

## Restricciones de publicación

No modificar `main`; PR #2 en borrador. Conservar distinción `DEMOSTRADO` / `NUMÉRICO` / `PENDIENTE`. Referencias: `docs/PUENTE_MATRIZ_CANDIDATA_33_RAMAS_SB_20261110.md`, `docs/MAPA_PRIMITIVAS_SOURCE_PYTHON_37_22_20261110.md`, `lean/candidates/Ventura26LiquidityAllocation/StationaryInterventionSourceBridgeCandidate.lean`.
