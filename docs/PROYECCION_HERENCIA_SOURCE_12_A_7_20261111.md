# IE Project 18 — proyección condicional del estado heredado SOURCE al prefijo Python (11-XI-2026)

## Planteamiento

SOURCE define un registro `InheritedState` con doce **campos estructurales**, dos de los cuales son funciones de `FirmType` y contienen un par H/L cada uno. En Python, el prefijo estacionario congelado tiene el vector de siete coordenadas

`X0=(k_H,k_L,F_H,F_L,E,R_R,M_pre)`.

La función candidata que conecta las representaciones es una **proyección, no una biyección**:

`Phi_I(I)=(I.capital(H),I.capital(L),I.firmFace(H),I.firmFace(L),I.bankFace,I.reserveRateLag,I.reservesPreLag)`.

En particular, no sustituir `I.reservesPreLag` por `I.reservesLag`: este último incorpora el préstamo de facilidad OTC `W>0`.

Bajo la identificación de primitivas estacionarias SOURCE con los parámetros ilustrativos Python:
`F_i=theta_i (1-delta) q k_i`, `E=equity`, `R_R=reserve rate`, `M_pre=reserves before facility`, se propone
`Phi_I(inheritedState(G))=frozen_stationary_seed(s).X0`.
Esta igualdad es **condicional** a la traducción de las funciones SOURCE, y no se presenta como teorema Lean.

## Información perdida por la proyección

Se omiten siete campos estructurales: depósitos de hogares, bonos de hogares, tasas de depósito y bonos del gobierno heredadas, reservas posteriores al préstamo OTC, tasa de facilidad y cantidad tomada de la facilidad. Son siete campos adicionales porque los campos `capital` y `firmFace` del registro se expanden a dos coordenadas cada uno. No es correcto afirmar una biyección entre `InheritedState` y `X0`.

El saldo de bonos depende del nivel de deuda pública `G`:
`householdBonds=G-M_pre`.
El balance contable `householdBonds+M_pre=G` requiere `G≥M_pre` para bonos no negativos y `G>M_pre` para interioridad estricta. El préstamo OTC responde a
`W=(RD/RR-rho)D/30>0`,
de modo que `reservesPost=M_pre+W`. El valor de `G` no altera `Phi_I` en esta construcción, aunque sí altera bonos y debe incluirse en una futura identificación de cierre fiscal.

## Prueba implementada

`code/irf/audit_inherited_12_to_7_projection.py` comprueba patrones literales de `StationaryInheritedStateCandidate.lean` y `finite_irf.py`, reconstruye las catorce entradas escalares equivalentes a los doce campos SOURCE con la instancia numérica ilustrativa, y compara las siete coordenadas proyectadas contra `frozen_stationary_seed(s).X0`. Contrasta además tres valores admisibles de `G`, mantiene la identidad fiscal `bonos+reservasPre=G`, distingue reservas pre/post OTC y demuestra numéricamente la pérdida de inyectividad a lo largo de `G`.

El script se incorpora a `code/verify.py`; `build.yml` conserva el JSON `source-inherited-12-to-7-projection`. La ejecución del SHA nuevo requiere confirmación de GitHub Actions.

## Obligaciones aún pendientes

1. Obtener la identificación formal de todos los campos SOURCE con las funciones de Python, no únicamente una proyección numérica creada de sus fórmulas.
2. Incorporar depósitos, bonos, tasas heredadas, facilidad OTC y cierre fiscal al espacio de datos que consumen los operadores; demostrar cuándo se pueden eliminar sin alterar las 33 ecuaciones.
3. Vincular `tail Z.stateTwo` a la solución recurrente del operador fuente, no solo al grafo lineal `P0`.
4. Demostrar equivalencia funcional en una misma carta y la regularidad del Jacobiano; después resolver KKT, terminalidad y equilibrio infinito.

**Veredicto:** proyección candidata con auditoría de procedencia; no identidad SOURCE–Python formal, ni prueba de unicidad o crecimiento. PR #2 sigue draft; no modificar `main`.
