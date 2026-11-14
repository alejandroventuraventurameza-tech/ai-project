# Puente escalar estacionario Python–Lean — 8 de noviembre de 2026

**Estado de la evidencia:** contraste escalar numerico APROBADO para
`steady()`, y demostracion exacta en Lean CANDIDATA hasta el run
correspondiente de `LocalScalarStationaryPythonCalibrationCandidate.lean`.
**No es una certificacion de las 34 ecuaciones ni de equilibrio general.**

## Objetos, no identificaciones por nombre

- Productor numerico: `code/v0m/cotas_2026_10_15/verified_linear_operator.py::steady`;
  digest SHA-256 `1369e9c04ed9774297d957ea27d8dad893f99fc17fb08c9819fa9a378ca6400b`.
- Primitivas economicas: `StationaryPrimitivesCandidate.lean::primitives G`.
- Funciones estacionarias: `InterbankCancellationCandidate.lean` y
  `StationaryReducedSystemCandidate.lean`.
- Lema exacto candidato: `LocalScalarStationaryPythonCalibrationCandidate.lean`.
- Comprobador con intervalos dirigidos:
  `code/v0m/certified_ift/audit_stationary_scalar_bridge.py`.
- Prueba numerica exitosa en trabajo CI
  [42454567930](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/42454567930),
  job `Python syntax` (no confundirlo con el build LaTeX).

## Cadena algebraica reconstruida

Con los parametros ilustrativos exactos
`Delta=1/50`, `aa=1/2`, `tight=1/2`, `rho=1/10`,
`zeta=1/5`, `RD=100/99`, definir
`v=1/(1+sqrt(3/2))`. Las pendientes originales de Python son

```text
cm   = Delta*(1-aa+aa*v) = (1+v)/100
cp   = Delta*tight*aa*v = v/200
mean = (cm+cp)/2        = (2+3*v)/400
gap  = cm-cp            = (2+v)/200
A    = RD -(9/10)*mean - gap/100
RR   = (A + sqrt(A^2+(2/5)*RD*gap))/2
RL   = RR + mean
```

Las funciones estacionarias fuente usan exactamente las expresiones
`mean`, `gap`, `A`, `RR` y `RL` a nivel de los numeros reales
matematicos. No se introdujo una tasa numerica sustitutiva.

La fuente fija
`P.bankExit = 1/10` y
`P.bankSeedShare = 10/RL-9`.
Por consiguiente,

```text
bankRenewalFactor(P)
  = 1 - P.bankExit + P.bankExit*P.bankSeedShare
  = 9/10 + (1/10)*(10/RL-9)
  = 1/RL.
```

Esta identidad elimina la hipotesis de compatibilidad del factor
bancario **para la instancia fuente estacionaria especifica**
`primitives G`, al identificar `RL` con la funcion cerrada de las
tasas. El Python ilustrativo usa `s.aB=1/s.rate`.
No implica automaticamente que los vectores de estado/parametros del
verificador Banach sean el mismo objeto formal de Lean.

La instancia estacionaria declara adicionalmente

```text
reserveRatePersistence     = 1/2
reserveQuantityPersistence = 1/2
inflationResponse          = 3/2
outputResponse             = 1/8
reserveRateSteady          = RR
reserveQuantitySteady      = reservesPre
outputReference            = aggregateOutput
entrepreneurRiskAversion   = 1.
```

Las reglas monetarias y el dual quedan expresados en la fuente en
terminos coherentes con estas referencias, no mediante una igualdad de
arreglos ilustrativos asumida.

## Puerta numerica y limites

El verificador independiente reutiliza `steady()` y vuelve a calcular
las siete magnitudes escalares por una ruta separada, con aritmetica
decimal intervalar dirigida. Exige interseccion de intervalos y una
cota de discrepancia estrictamente menor que `1e-60`.
La mayor diferencia observada fue de orden `1e-79`; se guardan las
cotas en salida reproducible con `--output ruta.json`.
Se comprobo `0 < seedShare < 1` para el testigo estacionario inferido.

**Esta comparacion NO demuestra igualdad de numeros reales a partir
de punto flotante**: la identidad matematica exacta se formula
independientemente en Lean; el script solo contrasta enclosures del
productor real.

| Componente | Evidencia actual | Aun falta |
|---|---|---|
| Pendientes OTC, RR, RL | Coincidencia escalar numerica dirigida; teoremas Lean candidatos | cotejo automatizado de todas las referencias de estado |
| `aB = 1/RL` | Source estacionario con `bankSeedShare=10/RL-9`; contraste intervalar | enlace con trayectoria efectiva `finite_bridge.py` fuera del padre |
| Filas 6 y 22 | equivalencia log/nivel condicionada verificada en CI 42453702554 | igualar valores heredados, calendario y caja de derivadas |
| Filas 12/13/28/29 | identidades completas de residuos bajo premisas verificadas en CI 42453702554 | premisas concretas para cada fecha y vector de shocks |
| Fila 21 | equivalencia de ceros con positividad verificada en CI 42453702554 | transicion t=2 real y derivadas |
| Fila 33 | dual CRRA sigma=1, bajo positividad, verificado en CI 42453702554 | confirmar mapeo de consumos, prestamo e inflacion Python |

**Conexiones abiertas:** faltan 26 filas del operador aumentado;
las 8 filas identificadas arriba no son aun una prueba de
`SourceAugmented34ZeroSetAgreement` para el evaluador Python.
Las envolventes de derivadas Banach se construyeron para un sustituto
Python, y no se heredan automaticamente al operador fuente Lean.
Tampoco se probo una solucion de `CompetitiveEquilibrium`, duplicidad
real de equilibrios, optimalidad dinamica, condiciones terminales
infinitas ni un efecto positivo de crecimiento.

**Escala que no debe confundirse:** la caja de politica del certificado
local tiene radio `r_h=1e-15`; la IRF ilustrativa usa `v_R=-1e-5`.
La comparacion escalar estacionaria no autoriza aplicar el certificado
local a esa IRF.
