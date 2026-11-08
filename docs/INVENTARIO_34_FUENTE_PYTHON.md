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
| 6 | Renovacion nominal bancaria, t=0 | Equivalencia log/niveles con factor fuente y positividad | Lema fuente verificado; identificacion de `aB` pendiente |
| 7 | Precio de oferta de capital, t=0 | Definiciones de capital agregado y ajuste | Pendiente |
| 8 | Recursos agregados, t=0 | Identidades de cantidades, masa, costos y output | Pendiente |
| 9 | Oferta de trabajo, t=0 | Equivalencia log/niveles; `sigmaW=phi=1` | Lema Lean candidato |
| 10 | Euler de depositos del hogar, t=0 | Equivalencia log/niveles; `sigmaW=1` | Lema Lean candidato |
| 11 | Phillips Rotemberg, t=0 | Descuento del hogar, `phiP`, inflacion y output | Pendiente |
| 12 | Regla de tasa de reservas, t=0 | Logaritmos, persistencias, metas e innovacion | Pendiente |
| 13 | Regla de cantidad de reservas, t=0 | Logaritmos, persistencias, metas e innovacion | Pendiente |
| 14 | Precio del prestamo, t=0 | Formula OTC y media de pendientes | Pendiente |
| 15 | Precio del deposito, t=0 | Formula OTC, cantidad y shocks de pagos | Pendiente |
| 16 | Balance bancario, t=0 | Ratio reservas/depositos, faces e inflacion | Pendiente |
| 17 | Presupuesto empresarial H, t=1 | Mismo cotejo de fuente, datos fecha 1 | Pendiente |
| 18 | Presupuesto empresarial L, t=1 | Mismo cotejo de fuente, datos fecha 1 | Pendiente |
| 19 | Euler de capital H, t=1 | Producto marginal y continuation t=2 | Pendiente |
| 20 | Euler de capital L, t=1 | Producto marginal y continuation t=2 | Pendiente |
| 21 | Garantia comun de capital t=1 | Residuos en niveles, fila reescrita por Python | Pendiente |
| 22 | Renovacion nominal bancaria, t=1 | Lema generico log/niveles para fuente `d1` | Lema fuente verificado; identificacion de datos pendiente |
| 23 | Oferta de capital, t=1 | Datos t=1 y continuation t=2 | Pendiente |
| 24 | Recursos, t=1 | Datos t=1 y continuation t=2 | Pendiente |
| 25 | Oferta de trabajo, t=1 | Lema generico log/niveles para fuente `d1` | Lema Lean candidato |
| 26 | Euler del hogar, t=1 | Lema generico log/niveles para fuente `d1` | Lema Lean candidato |
| 27 | Phillips, t=1 | Datos t=1, indexacion y continuation | Pendiente |
| 28 | Regla tasa reservas, t=1 | Calendario, persistencia e innovaciones t=1 | Pendiente |
| 29 | Regla cantidad reservas, t=1 | Calendario, persistencia e innovaciones t=1 | Pendiente |
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

**Regla de actualizacion:** un candidato solo pasa a
"verificado" si el run especifico del commit lo compila y
`#print axioms` no presenta `sorryAx`; este inventario
no sustituye esos registros.
