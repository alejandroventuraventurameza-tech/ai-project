# IE project — dividendos, retencion y existencia del maximo bancario

**Fecha:** 2026-11-08. **Rama:** `work/lean-ci-validation-otc-20261106`.
**Alcance:** argumento matematico condicional y auditoria de especificacion economica. **NO** prueba Lean ni `BankOptimal`.

## Fuente exacta y punto de fragilidad

`lean/checkpoint/modules/Ventura26LiquidityAllocation/EconomicModel.lean` define `BankContinuationFeasibleAt`, donde se exige en cada historia soportada:

- `0 <= equity`, `0 <= dividend`, `0 <= retainedEquity`;
- `retainedEquity = equity - dividend`;
- si `0 < equity`, entonces `0 < retainedEquity`.

En particular, para `e>0` se tiene `0<=d<e` y `r=e-d>0`. Estas restricciones no implican que **todas** las elecciones en ese intervalo sean factibles: balances, solvencia, caps, tasa de reserva positiva y transiciones pueden imponer otras limitaciones. La version positiva de patrimonio retenido excluye repartir todo el patrimonio en una fecha con `e>0`.

## Lema algebraico condicional de dividendos (sin Lean kernel)

Supongamos, **ademas**, que una cartera factible optimizada bajo precios dados genera un valor de continuacion lineal respecto del patrimonio retenido, `G_t(r)=k_t r`, con `k_t` un coeficiente independiente de la decision marginal de dividendos para el banco individual. Esta forma debe deducirse de homogeneidad mas factibilidad/alcanzabilidad; no se deduce solo de la desigualdad KKT para un `r` fijo.

Entonces, dado `e=d+r`, el objetivo de un paso es

`F_t(d,r) = d + k_t r = k_t e - (k_t-1)*d = e + (k_t-1)*r`.

**Caso k_t>1.** Para toda eleccion `d>=0` que respeta `d+r=e`,

`F_t(d,r) <= k_t e`,

con igualdad solamente si `d=0`. Por tanto, si la opcion de retencion total (d=0, r=e) satisface las restricciones fuente, es optima en este problema unidimensional. La factibilidad de esa cartera no debe darse por supuesta.

**Caso k_t=1.** El valor `F_t=e` es constante para toda decision de reparto factible. La candidata `d=0` es un maximo solo si es factible, y no es unica.

**Caso k_t<1.** El valor aumenta cuando `r` disminuye. Si `e>0`, el contrato fuente exige `r>0`; si para todo `r\in(0,e]` existiera una cartera factible, el supremo `e` se aproxima al hacer `r\downarrow0`, pero no se alcanza. No se debe proclamar inexistencia real del maximo del banco **sin demostrar** que esas carteras arbitrariamente pequenas son factibles. Si otras restricciones fuerzan `r>=r_min>0` y la cartera minima se alcanza, el maximo sera en ese `r_min`.

## Por que importa para la prueba `BankOptimal`

La prueba KKT del proyecto establece suficiencia global **dado el patrimonio retenido**, con cinco multiplicadores (incluye esquinas de préstamos, reservas, depósitos y caps). El resultado no compara opciones distintas de dividendos y retencion. Una comparacion Bellman entre futuros valores `V<=W` para la misma cartera tampoco optimiza `d`. Hay que separar:

1. Maximizacion de cartera `(b,m,d_{dep})` condicional en `r`.
2. Maximizacion de dividendos `D` y retencion `r=e-D` sobre el conjunto de retenciones efectivamente factibles.
3. Construccion y validacion del valor de continuacion infinito, con igualdad Bellman candidata y límite terminal.

No confundir dividendos `D` con depósitos bancarios `d_{dep}`; en el codigo fuente ambos aparecen en problemas distintos.

## Compromisos para una siguiente declaracion Lean

- Primero formular un lema **puramente algebraico** de dominancia cuando `k_t>=1` y `D>=0`, dejando explicitos `e=D+r`, homogeneidad, y factibilidad de la candidata de retencion total.
- Probar que el factor `k_t` usado es el factor marginal verdadero de la funcion `bankBellmanContinuationAt` bajo un conjunto de carteras escalado, no sustituirlo por una tasa numerica exógena.
- Comprobar las restricciones `0<r` sobre historias soportadas y el caso `e=0`. Si `k_t<1`, exigir un argumento separado de existencia/compacidad del conjunto factible, o reconocer no alcanzabilidad.
- Conservar el estatus `CANDIDATO` hasta compilacion focalizada y `#print axioms` sin `sorryAx`.
- No inferir `BankOptimal`, un equilibrio S/B general ni crecimiento sostenido de este lema unidimensional.

## Estado de CI en el momento de redactar

La ejecucion focalizada de los primeros módulos nuevos fue fallida por un orden de suma en una prueba Lean. El error se corrigio en `4cb60960` y en el analogo finito `3c487e21`; los módulos de cota de primer paso y Bellman literal se ajustaron preventivamente en `a8990d3e` y `1f5d57bd`. **El kernel del head que contiene estas correcciones aun no se ha confirmado verde.**

**No fusionar PR #2 a main** antes de cerrar las compuertas correspondientes.
