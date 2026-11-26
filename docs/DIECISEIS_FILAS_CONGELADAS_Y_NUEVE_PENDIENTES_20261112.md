# IE Project 18 — 16 filas adicionales en base congelada (12-XI-2026)

## Verificación completada de las ocho filas de firmas

El workflow `build` del SHA `1afd20ab13bcb953ff4fc464c29441125adb9be7` terminó `success` en la ejecución [#43265930445](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/43265930445). El registro del job `Run code/verify.py` documentó para las ramas vinculante y holgada: error de filas directas `3.552713678800501e-15`, error de identidad de cizalla Euler `2.29951472199193e-16` y error direccional condicional `8.881784197001252e-10`. Se comprobaron ocho filas y 33 direcciones, siempre en una transcripción Python y no sobre el operador económico Lean.

## Nuevo incremento de 16 filas

Se añadió `code/irf/audit_frozen_16_remaining_row_candidates.py`, ejecutado desde `code/verify.py` y archivado en `build.yml`. Utiliza **el mismo `frozen_stationary_seed(steady_case())`**, `P0` racional previamente anclado y `finite_irf.prefix_residual` que el auditor del Jacobiano Python congelado.

Se reutiliza la función de transcripción SOURCE-shaped `transcribed_prefix_rows` de `audit_source_identity_row_candidates.py`, con verificación por índices sobre las dieciséis filas: oferta de capital, recursos, Phillips NK, regla de remuneración de reservas, regla de cantidad de reservas, precio de préstamos, precio de depósitos y balance bancario (fechas 0 y 1).

El diagnóstico toma dos ramas (vinculante y holgada), cinco intervenciones exógenas de cuatro instrumentos (ninguna y cuatro choques individuales), tres puntos en la carta logarítmica y diferencias centrales en las 33 direcciones. Exige errores de niveles inferiores a `2e-10` y errores direccionales inferiores a `5e-7` y conserva hashes de SOURCE, Python, `P0` y transcripción.

**Estado:** pendiente de que concluya el workflow `build` del commit que incorporó la auditoría `dbdb3329...`. No elevar la prueba a NUMERICO VERIFICADO antes de observar `success` y sus valores.

## Qué queda exactamente

Los informes 8+16 suman **24 posiciones de filas SOURCE distintas** examinadas sobre la misma base congelada, si el último test pasa. Quedan **nueve filas SOURCE** con transformaciones escalares de niveles frente a logaritmos: índices `4,5,6,9,10,21,22,25,26`. El auditor `audit_partial_jacobian_row_scales.py` ya propone factores para ellas, pero evalúa trayectorias de la **frontera switching `make_boundary(s)`**, no la raíz congelada.

No es legítimo trasladar esos nueve factores a la raíz congelada sin recomputarlos allí. Además, un test de igualdad de un transcriptor SOURCE-shaped con las fórmulas Python, aun con todas las 33 posiciones cubiertas, **no demostraría que la función Lean SOURCE sea igual**. Es necesario un transporte formal del registro `Primitives`, el calendario, las funciones auxiliares de ambas fechas, las cizallas Euler fuera de la raíz, la carta `psi` y `tail`.

## Alcance científico

- **Demostrado en Lean:** igualdad de los operadores SOURCE reducidos y de sus Jacobianos a través de parámetros fiscales estacionarios (no equilibrio completo).
- **Numérico verificado:** Jacobiano Python estacionario congelado y las ocho filas de firmas transcritas.
- **Pendiente de CI:** las dieciséis filas nuevas en esa misma base.
- **Pendiente:** nueve factores escalares recomputados en raíz congelada, igualdad SOURCE–Python genuina, inversa intervalar del Jacobiano económico y equilibrio infinito.

PR #2 continúa en borrador; `main` no se fusiona.
