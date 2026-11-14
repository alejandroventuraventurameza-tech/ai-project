# IE Project 18 — ledger ejecutable de las 33 filas candidatas (11-XI-2026)

## Diagnóstico

Los auditores independientes ya produjeron nueve factores escalares en raíces, dieciséis filas adicionales transcritas y ocho filas empresariales (seis identidades directas y dos Euler con shear de colateral). Esa suma **9+16+8=33** es exhaustiva como **inventario** de posiciones, no una demostración de igualdad de operadores.

El problema que resuelve esta iteración es la posible inferencia editorial falsa «33 posiciones cubiertas = 33 ecuaciones SOURCE formalmente equivalentes a Python». El script `code/irf/audit_source_33_claim_readiness.py` convierte esa distinción en una compuerta verificable.

## Auditoría nueva

El script, ejecutado inmediatamente después de `audit_source_full_transform_candidate.py`, comprueba:

1. Los conjuntos de nueve, dieciséis y ocho índices SOURCE son disjuntos, de los tamaños previstos y su unión es exactamente `{0,...,32}`.
2. La permutación `SOURCE→Python` es una biyección y coincide con el informe de matriz candidata.
3. Los hashes del archivo literal Lean `EconomicModel.lean`, `finite_irf.py` y `rational_preconditioners.json` son iguales a los hashes anotados por los auditores de filas, de la carta y de las identidades; no se aceptan reportes obsoletos.
4. La carta del benchmark es positiva, ambos informes de la matriz candidata conservan explicitamente la procedencia de la frontera común y los factores de inversa candidatos son finitos.
5. Las banderas del alcance formal permanecen explícitamente en `False` mientras no exista un teorema de igualdad funcional en el SOURCE, certificado del Jacobiano o equivalencia económica del estado heredado.

El resultado esperado tiene la categoría:

`ALL_33_CANDIDATE_ROWS_PRESENT_FULL_SOURCE_OPERATOR_NOT_CERTIFIED`.

Por construcción la salida **no** dice `certified`. El JSON se genera durante `code/verify.py` y se archiva como artifact `source-33-row-claim-readiness` en el workflow `build.yml`. La ejecución nueva debe cotejarse por commit y job.

## Qué no hace

No recompila Lean, no ejecuta el operador `EconomicModel.lean` dentro de Python, no verifica un entorno abierto de 33 residuos, no construye una matriz de discrepancias `DR` y no prueba `||M^{-1}DR||_∞<1`. La aritmética racional sintética de Neumann no sustituye esas tareas.

En particular, no es válido declarar una cota de perturbación del Jacobiano SOURCE usando como `M` la inversa ya conocida de la transformación de filas `T`. Se requiere una cota **independiente** de invertibilidad de un Jacobiano económico.

## Próximo compromiso científico

Construir el transporte semántico de datos: una función SOURCE y una función Python que consuman el mismo prefijo de historia, shock, estado heredado, planes de bancos y firmas, y terminalidad. Luego cotejar los 33 valores residuales y sus derivadas en una carta abierta, documentando las hipótesis de rama. Solo después activar una cota rigurosa de error y el criterio de Neumann. Mantener PR #2 en borrador, no fusionar `main`.
