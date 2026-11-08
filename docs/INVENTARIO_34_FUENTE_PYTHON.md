# Inventario de las 34 ecuaciones: fuente Lean y evaluador Python

**Estado:** inventario de auditoria, NO certificacion de identidad
Python-Lean. **Rama:** `work/lean-ci-validation-otc-20261106`.

La enumeracion a continuacion viene de `localPrefixEquationOfIndex`
en `lean/checkpoint/modules/Ventura26LiquidityAllocation/EconomicModel.lean`.
El orden Python se transforma mediante `source_to_legacy_row_permutation`
en `finite_bridge.py`. La columna de prueba se refiere a lemas
**de la fuente Lean**; no certifica el volcado numerico ni los
parametros concretos de Python.

| Fila | Ecuacion literal del prefijo Lean | Ruta de correspondencia | Estado |
|---:|---|---|---|
| 0 | Presupuesto empresarial H, t=0 | Comparar patrimonio, faces, capital y precios | Pendiente |
| 1 | Presupuesto empresarial L, t=0 | Comparar patrimonio, faces, capital y precios | Pendiente |
| 2 | Euler de capital H, t=0 | Comparar SDF, producto marginal y garantias | Pendiente |
| 3 | Euler de capital L, t=0 | Comparar SDF, producto marginal y garantias | Pendiente |
| 4 | Colateral H, t=0 | Residuos en niveles, fila reescrita por Python | Pendiente |
| 5 | Holgura normalizada L, t=0 | Fuente exige `1-F_L/(theta*J*K_L)-s`; fila reescrita | Pendiente |
| 6 | Renovacion nominal bancaria, t=0 | Equivalencia log/niveles con factor fuente y positividad | Lemas fuente y compatibilidad algebraica verificados; instancia de `aB` pendiente |
| 7 | Precio de oferta de capital, t=0 | Definiciones de capital agregado y ajuste | Pendiente |
| 8 | Recursos agregados, t=0 | Identidades de cantidades, masa, costos y output | Pendiente |
| 9 | Oferta de trabajo, t=0 | Equivalencia log/niveles; `sigmaW=phi=1` | Lema Lean verificado; instancia y dominio pendientes |
| 10 | Euler de depositos del hogar, t=0 | Equivalencia log/niveles; `sigmaW=1` | Lema Lean verificado; instancia y dominio pendientes |
| 11 | Phillips Rotemberg, t=0 | Descuento del hogar, `phiP`, inflacion y output | Pendiente |
| 12 | Regla de tasa de reservas, t=0 | Logaritmos, persistencias, metas e innovacion | Objetivo exp fuente verificado; puente con `auxiliary` candidato |
| 13 | Regla de cantidad de reservas, t=0 | Logaritmos, persistencias, metas e innovacion | Objetivo exp fuente verificado; puente con `auxiliary` candidato |
| 14 | Precio del prestamo, t=0 | Formula OTC y media de pendientes | Pendiente |
| 15 | Precio del deposito, t=0 | Formula OTC, cantidad y shocks de pagos | Pendiente |
| 16 | Balance bancario, t=0 | Ratio reservas/depositos, faces e inflacion | Pendiente |
| 17 | Presupuesto empresarial H, t=1 | Mismo cotejo de fuente, datos fecha 1 | Pendiente |
| 18 | Presupuesto empresarial L, t=1 | Mismo cotejo de fuente, datos fecha 1 | Pendiente |
| 19 | Euler de capital H, t=1 | Producto marginal y continuation t=2 | Pendiente |
| 20 | Euler de capital L, t=1 | Producto marginal y continuation t=2 | Pendiente |
| 21 | Garantia comun de capital t=1 | Residuos en niveles, fila reescrita por Python | Pendiente |
| 22 | Renovacion nominal bancaria, t=1 | Lema generico log/niveles para fuente `d1` | Lemas fuente y compatibilidad algebraica verificados; datos `d1` pendientes |
| 23 | Oferta de capital, t=1 | Datos t=1 y continuation t=2 | Pendiente |
| 24 | Recursos, t=1 | Datos t=1 y continuation t=2 | Pendiente |
| 25 | Oferta de trabajo, t=1 | Lema generico log/niveles para fuente `d1` | Lema Lean verificado; instancia `d1` pendiente |
| 26 | Euler del hogar, t=1 | Lema generico log/niveles para fuente `d1` | Lema Lean verificado; instancia `d1` pendiente |
| 27 | Phillips, t=1 | Datos t=1, indexacion y continuation | Pendiente |
| 28 | Regla tasa reservas, t=1 | Calendario, persistencia e innovaciones t=1 | Objetivo exp fuente verificado; calendario e instanciacion pendientes |
| 29 | Regla cantidad reservas, t=1 | Calendario, persistencia e innovaciones t=1 | Objetivo exp fuente verificado; calendario e instanciacion pendientes |
| 30 | Precio prestamos, t=1 | OTC y estado heredado t=1 | Pendiente |
| 31 | Precio depositos, t=1 | OTC y estado heredado t=1 | Pendiente |
| 32 | Balance bancario, t=1 | Ratio reservas/depositos y faces t=1 | Pendiente |
| 33 | Dual financiero normalizado L | CRRA `sigmaE=1` y consumos positivos | Formula fuente verificada; primitivas no cotejadas |

Las filas **4, 5 y 21** se reescriben en niveles en el
exportador Python; no se infiere que todas las otras filas se
conviertan automaticamente en definiciones identicas de Lean.

## Lecciones de los residuos transformados

Sean `N(x)>0`, `D(x)>0`, `F(x)=N(x)-D(x)` y
`G(x)=log(N(x)/D(x))`. Suponiendo funciones diferenciables,
en todo punto donde `F(x)=0` se cumple

```text
G(x)=0 <-> F(x)=0,
DG(x) = DF(x)/N(x)  (solo en el cero comun N=D).
```

Para Euler del hogar, si `Q(x)>0`, `F(x)=1-Q(x)`
y `G(x)=log Q(x)`, entonces en `Q(x)=1`

```text
G(x)=0 <-> F(x)=0,
DG(x) = -DF(x).
```

Estas identidades evidencian por que el jacobiano de las expresiones
logaritmicas certificadas numericamente NO puede adjudicarse
sin transformacion al operador literal de Lean. La equivalencia de
ceros puede ser suficiente para transferir una raiz, pero requiere
cotejar numeros, unidades, estados y dominio en cada fila.

## Reglas de prueba y completitud

- **Certificado original:** `audit_augmented_34.py` conserva su
  significado: cota racional de un operador Python en una caja.
  Las banderas de identidad semantica siguen en falso.
- **Correspondencia exacta condicionada:** el modulo
  `LocalScalarAugmented34SemanticBridgeCandidate.lean` define
  `SourceAugmented34ZeroSetAgreement`. Aun falta demostrar
  sus 34 obligaciones para el operador concreto, no solo definirlas.
- **Faltante estructural principal:** `aB=1/s.rate` en el caso
  ilustrativo Python; en fuente Lean el factor es
  `1-bankExit+bankExit*bankSeedShare`. La igualdad seria una
  condicion de parametros que debe verificarse realmente, no
  una simplificacion textual o un default.
- **Escala:** `r_h=1e-15` en la caja Banach y
  `v_R=-1e-5` en la IRF principal: NO inferir resultados
  sobre la IRF a partir de la caja local.
- **Economia completa:** incluso 34 identidades cerradas y un cero
  formal no prueban por si mismas KKT suficiente de todos los
  agentes, clearing de todos los mercados ni terminalidad
  infinita. La multiplicidad de equilibrios sigue pendiente.

## Condicion necesaria y suficiente del factor de renovacion bancaria

El ejemplo Python fija `aB=1/s.rate`. En la fuente Lean
`bankRenewalFactor(P)=1-P.bankExit+P.bankExit*P.bankSeedShare`.
La identificacion de la fila bancaria exige por tanto la
compatibilidad cuantitativa **exacta**:

```text
P.bankExit*(1-P.bankSeedShare) = 1 - 1/s.rate.
```

Esta equivalencia se deduce algebraicamente de las definiciones;
no demuestra que los datos ilustrativos satisfagan dicha condicion.
Se requiere una instancia concreta de `P` y cotejar los valores
de `s.rate`, `P.bankExit` y `P.bankSeedShare` antes de marcar
las filas 6 y 22 como numericamente compatibles.

### Rango economicamente admisible (argumento algebraico)

Si la tasa de referencia bruta satisface `R>1`, definir
`kappa=1-1/R` implica `0<kappa<1`. Bajo
`0<=bankExit<=1` y `0<=bankSeedShare<=1`, las soluciones
admisibles de `bankExit*(1-bankSeedShare)=kappa` son

```text
0 <= bankSeedShare <= 1/R,
bankExit = kappa/(1-bankSeedShare).
```

Este es un conjunto de pares de parametros, NO la identificacion
de los parametros elegidos en la fuente economica. Evaluando
aproximadamente la formula de `steady()` de
`code/v0m/cotas_2026_10_15/verified_linear_operator.py`
se obtiene `R~1.01204824`, `kappa~0.01190480`.
Si, solo como ejemplo, se eligiera `bankSeedShare=0.5`,
entonces `bankExit~0.02380961`. Estas cifras usan redondeo
ordinario y NO sustituyen la verificacion de parametros ni
las cajas intervalares originales.

Se anadio el candidato Lean
`LocalScalarBankRenewalCalibrationBridgeCandidate.lean`
para demostrar el `iff` del factor de renovacion y la
equivalencia de ceros bancaria con positividad; no promoverlo
a verificado antes del resultado CI de su revision.

**Evidencia de CI por tipo de prueba:** la campaña Lean
[42450897067](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/42450897067)
verifico las equivalencias de cero de trabajo y Euler
del hogar y el contrato condicional de 34 filas.
[42451359174](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/42451359174)
verifico la compatibilidad algebraica del factor bancario,
NO su instancia numerica.
[42451438040](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/42451438040)
verifico los objetivos exponenciales de la fuente monetaria,
NO su identidad con el codigo Python.
Los puentes de residual logaritmico y objetivos de
`auxiliary()` se mantienen CANDIDATOS hasta aprobar
sus propias campañas Lean; no se alteraron las 34
banderas de procedencia numerica.

**Regla de actualizacion:** un candidato solo pasa a
"verificado" si el run especifico del commit lo compila y
`#print axioms` no presenta `sorryAx`; este inventario
no sustituye esos registros.


## Puente de reglas monetarias: mapeo a los instrumentos originales

El generador Python `finite_bridge.py:auxiliary` calcula, con
`e_R` y `e_M` como innovaciones de la regla nominal:

```text
RR_target = rr_ref * exp(
  1/2 * log(RR_lag / rr_ref)
  + 1/2 * (3/2 * log(Pi) + 1/8 * log(Y / Y_ref))
  + e_R
)
M_target = M_ref * exp(1/2 * log(M_lag/M_ref) + e_M)
```

Las filas `remaining(...)[6]` y `remaining(...)[7]` son
`log(RR_realized/RR_target)` y `log(M_realized/M_target)`.

Por otro lado, `EconomicModel.lean:localReducedRemainingResidual`,
filas de once `6` y `7`, contiene los residuos de niveles
logaritmicos de las dos reglas economicas originales. La identificacion
de coeficientes y referencias necesaria es:

| Primitiva Lean | Fuente Python | Restriccion de fuente |
|---|---|---|
| `P.reserveRatePersistence` | mitad de la persistencia en `auxiliary` | `=1/2` |
| `P.reserveQuantityPersistence` | mitad de la persistencia en `auxiliary` | `=1/2` |
| `P.inflationResponse` | `1.5` | `=3/2` |
| `P.outputResponse` | `0.125` | `=1/8` |
| `P.reserveRateSteady` | `s.rr` | identidad comprobada con la instancia |
| `P.reserveQuantitySteady` | `s.M` | identidad comprobada con la instancia |
| `P.outputReference` | `s.Y` | identidad comprobada con la instancia |
| `d.lagReserveRate` | `X[5]` | mismo estado heredado/fecha |
| `d.lagReservesPre` | `X[6]` | mismo estado heredado/fecha |
| `d.currentReserveRate` | `Xnext[5]` | misma variable bruta/fecha |
| `d.currentReservesPre` | `Xnext[6]` | misma variable nominal/fecha |
| `d.reserveRateInnovation` | `e[0]` | misma innovacion y calendario |
| `d.reserveQuantityInnovation` | `e[1]` | misma innovacion y calendario |

La prueba fuente `LocalScalarPolicyRuleTargetsCandidate.lean`
compilo con auditoria de axiomas en
[GitHub Actions 42451438040](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/42451438040).
El modulo `LocalScalarPythonMonetaryRuleBridgeCandidate.lean`
**verifico en Lean** las igualdades de *residuos logaritmicos expandidos*
bajo las hipotesis de coeficientes y positividad en
[CI 42451697663](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/42451697663),
incluido el control de axiomas sin `sorryAx`. El codigo Python calcula
los objetivos con exponenciales, por lo que aun resta demostrar
o cotejar la identidad `log(RR_target)` con el log objetivo
especializado bajo positividad, y conectar de forma literal
las columnas del vector fuente con las de Python en ambas fechas.

**Diferencia conceptual:** `e_R` altera la regla de remuneracion
de reservas y `e_M` su regla de cantidad. El experimento con
`v_R` no puede identificarse con cambios en `reserveRequirementPath`
ni `corridorWidthPath` sin nueva prueba.

