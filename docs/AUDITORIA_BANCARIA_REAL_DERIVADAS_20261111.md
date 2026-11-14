# IE Project 18 — compuerta bancaria real, no prueba sintética (11-XI-2026)

## Corrección de inventario

La prueba real sobre las funciones Python ya existía: `code/irf/audit_source_bank_renewal_face_bridge.py` decodifica las 33 coordenadas mediante `finite_irf.decode_prefix` y evalúa `finite_irf.prefix_residual` para la fila 6 (banco en fecha 0) y la fila 22 (banco en fecha 1). Sus expresiones SOURCE se cotejan con patrones literales en `EconomicModel.lean`, pero **Lean no se ejecuta dentro del script**. El test sintético independiente agregado en el ciclo anterior constituye una regresión algebraica suplementaria, no sustituye este auditor real.

## Cambio de esta iteración

Se reforzó el auditor real para contar las 132 comprobaciones de gradiente en raíz (2 ramas × 2 filas × 33 direcciones) y las 132 comprobaciones fuera de raíz; rechaza una ejecución que no complete esa cobertura. Ahora también registra `max_offroot_error_if_root_only_formula_misused` y exige un testigo no nulo para la fórmula inválida `dF=D dG` fuera de raíz. El gradiente correcto sigue siendo

`dF=(exp(G)-1)dD + D exp(G)dG`.

Por construcción, las dos ramas comparten `make_boundary(s)` en esta auditoría. **No** se está afirmando que se trata de dos raíces distintas del mismo predecessor heredado. Los `33` gradientes son derivadas de las dos filas bancarias, **no** las 33 filas de SOURCE.

## Estado epistemológico

- **ANALÍTICO:** equivalencia de nivel y logaritmo sobre el dominio positivo, bajo identificación de numerador y denominador.
- **CÓDIGO MODIFICADO, CI POR CONFIRMAR:** detección de término fuera de raíz y conteo de derivadas.
- **NUMÉRICO HISTÓRICO:** auditoría bancaria Python documentada en `docs/PUENTE_RENOVACION_BANCARIA_SOURCE_PYTHON_20261110.md`.
- **PENDIENTE:** ejecución y cotejo línea a línea del original Lean en la misma carta; equivalencia completa de residuos/Jacobiano; existencia y optimalidad de solución SOURCE, 34 condiciones KKT, equilibrio infinito y crecimiento.

La siguiente compuerta matemática debe utilizar el mismo `LocalPrefixDateData` original y los mismos controles en ambos lenguajes, con fechas cero y uno. No promocionar una prueba por anotaciones de código, hashes o CI verde de la parte Python.

La rama es `work/lean-ci-validation-otc-20261106`; `main` permanece intacta y PR #2 continúa en borrador.
