# IE Project 18 — la brecha entre predecessor fijo y frontera común (11-XI-2026)

## Hallazgo de procedencia

Las auditorías de filas `audit_source_identity_row_candidates.py`, `audit_source_firm_budget_euler_shear.py`, `audit_source_bank_renewal_face_bridge.py` y `audit_source_full_transform_candidate.py` utilizan `make_boundary(s)`. Este constructor modifica el estado heredado `X0` y contiene innovaciones compensatorias de fecha uno `e1` distintas de cero.

En cambio, el experimento económico `frozen_same_predecessor_branch_audit.py` usa `frozen_stationary_seed(s)`, que fija `X0=[k_H,k_L,F_H,F_L,E,R_R,M]` e impone `e0=e1=(0,0)`. El archivo de origen `frozen_stationary_prefix_audit.py` ya advertía que la frontera `make_boundary` debe emplearse como comparación adversarial, nunca como la misma herencia estacionaria.

Por tanto, cualquier cota o permutación calculada sobre `make_boundary` es **condicional a esa frontera** y no certifica la misma transformación sobre la raíz del problema de herencia fija. El objetivo de identificar ambas familias es matemáticamente distinto.

## Estado SOURCE

La instancia construida en `StationaryInheritedStateCandidate.lean` define 12 posiciones heredadas:
`capital`, `firmFace`, `bankFace`, `householdDeposits`, `householdBonds`, `depositRateLag`, `governmentBondRateLag`, `reserveRateLag`, `reservesPreLag`, `reservesLag`, `facilityRateLag`, `facilityBorrowingLag`.

Es relevante que `householdBonds=G-reservesPre`, `reservesLag=reservesPost` y `reservesPreLag=reservesPre`. No se pueden identificar reservas antes y después de liquidación bancaria por conveniencia, ni fijar silenciosamente `G=0` o `G=2M`. No basta observar que Python `X0` tiene siete entradas: los doce campos financieros y fiscales deben identificarse mediante las funciones y contratos fuente, no por el número de coordenadas.

## Nueva compuerta automática

`code/irf/audit_source_predecessor_provenance.py` inspecciona literalmente los doce campos del constructor Lean; comprueba la convención de `frozen_stationary_seed` y de `make_boundary`; evalúa sus siete coordenadas heredadas y sus innovaciones de fecha uno y exige una diferencia no trivial. Genera un JSON con hashes de código, coordenadas y banderas explícitas de no certificación.

El script se integra a `code/verify.py`; `build.yml` conserva el artefacto `source-inherited-predecessor-provenance`. La integración debe superar el run del SHA actualizado. El informe es una comprobación de **procedencia numérica y sintaxis SOURCE**, no una prueba Lean de la igualdad de ambas estructuras.

## Siguiente compuerta económica

Definir una traducción explícita
`Phi_I: InheritedState(P) → PythonFrozenPredecessor`
con las unidades de cada cara nominal, reservas pre/post, depósitos, bonos y facilidad OTC. Demostrar que `Phi_I(inheritedState(G))=frozen_stationary_seed(s).X0` bajo hipótesis identificadas, especificando qué componentes quedan fuera de las siete coordenadas y cómo se reconstruyen desde parámetros y contratos.

Solo después trasladar al caso de herencia fija las transformaciones de las 33 filas, verificar `G=P T F psi`, el Jacobiano y, en caso de resto, `||M^{-1}DR||<1`. Toda afirmación de un equilibrio S distinto exige una raíz factible y KKT verificadas, no solo una solución algorítmica tentativa.

**No fusionar PR #2; main intacta.**
