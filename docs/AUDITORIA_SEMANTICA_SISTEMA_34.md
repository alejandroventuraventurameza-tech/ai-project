# Auditoria de correspondencia semantica: 34 ecuaciones Python y Lean

**Estado:** brecha cientifica ABIERTA. La aritmetica racional de la
puerta Banach de 34 dimensiones esta comprobada para el evaluador
Python; esto NO constituye una envolvente automaticamente valida
de las 34 funciones LITERALES de `EconomicModel.lean`.
**Rama:** `work/lean-ci-validation-otc-20261106`.

## 1. Objetos que NO deben identificarse automaticamente

- Fuente Lean: `localBindingResidualWithSlack`, 33 filas, mas
  `localNormalizedCollateralDualL`, una fila adicional.
- Productor numerico: `code/v0m/cierre_interno_2026_10_17/finite_bridge.py`,
  funcion `evaluate_bridge` y `remaining`.
- Verificador racional: `code/v0m/certified_ift/audit_augmented_34.py`.
- Condicion Banach numerica: `q < 1`, `eta + q < 1`,
  con radios `r_z=1e-10`, `r_h=1e-15`.
- Las banderas `source_Lean_semantic_identity_proved` y
  `uniform_box_contains_Lean_actual_derivatives_proved`
  siguen en `false` por razones sustantivas, no administrativas.

El productor ya transforma expresamente las filas de indices de fuente
`4`, `5` y `21` a formulas en niveles, y permuta el orden de filas
con `[0,3,1,4,2,5,6,...,16,17,19,18,20,21,...,32]`.
Esto es necesario pero NO suficiente para identidad semantica completa.

## 2. Discrepancias concretas que requieren un lema o nuevo evaluador

### Fila 6: transicion de patrimonio bancario, fecha cero

Python `remaining(...)[0]` produce, en notacion simplificada,
`G_6 = log(Bnext / (aB * RL * Bcur / Pi))`.
Lean `localReducedRemainingResidual P d 0` produce
`F_6 = Bnext - bankRenewalFactor(P) * RL * Bcur / Pi`.

Son residuos DISTINTOS. Si
`aB=bankRenewalFactor(P)`, `Bnext>0` y el denominador es
estrictamente positivo, entonces `G_6=0` si y solo si `F_6=0`.
En una raiz comun,
`D G_6 = (D F_6)/Bnext`, no `D G_6=D F_6`.
La identificacion `aB=bankRenewalFactor(P)` NO se deriva del
codigo fuente: el Python ilustrativo usa `s.aB = 1/s.rate`,
mientras que Lean define
`bankRenewalFactor(P)=1-P.bankExit+P.bankExit*P.bankSeedShare`.
Se requiere una condicion de parametros explicitamente comprobada.

### Fila 9: oferta laboral, fecha cero

Python `remaining(...)[3]` evalua
`G_9 = log(w / (chiW * L * CW))`.
Lean `localReducedRemainingResidual P d 3` evalua
`F_9 = w - P.laborScale * CW^(P.workerRiskAversion) *
L^(P.laborCurvature)`.

Para igualdad de conjuntos de ceros se necesitan, entre otras,
las especializaciones `sigmaW=1`, `varphi=1`,
`chiW=P.laborScale` y positividad del salario, el consumo y
el trabajo agregado. Los jacobianos son diferentes aun cuando
estas hipotesis se satisfagan.

### Fila 10: Euler del hogar, fecha cero

Python `remaining(...)[4]` evalua
`G_10=log(RD * (betaW * CW/CWnext) / Pinext)`.
Lean `localReducedRemainingResidual P d 4` evalua
`F_10=1 - (betaW * u'(CWnext)/u'(CW)) * RD/Pinext`.

Bajo `workerRiskAversion=1`, consumos positivos y parametros
identificados, escribir el cociente positivo como `Q` da
`G_10=log(Q)` y `F_10=1-Q`.
Ceros equivalentes, PERO `D G_10=-D F_10` en `Q=1`.
Por ello una cota de `D G` no es por defecto una cota de `D F`.

### Filas 12 y 13: reglas de reservas

El evaluador Python usa log-cocientes del valor realizado contra el
objetivo calculado por `auxiliary`, mientras que Lean escribe
directamente el log del valor realizado menos la regla de Taylor
y la regla de cantidad heredadas de `Primitives`.
La coincidencia requiere demostrar igualdad de tasas de referencia,
persistencias, coeficientes, innovaciones y unidades; una similitud
formal de logaritmos no basta.

### Fila 33 (adicional): marginal financiera de L

Lean usa `crraMarginal sigma c = c^(-sigma)`.
Python usa `betaE * C0L / C1L`.
La especializacion `sigmaE=1` y consumos positivos permite
la igualdad algebraica del termino de descuento, pero aun se
deben identificar los niveles, el prestamo bruto y la inflacion.
`LocalScalarDualSigmaOneBridgeCandidate.lean` es un candidato
enviado a compilacion para este sublema exacto.

Las otras filas no quedan declaradas iguales ni equivalentes por
omision. Deben someterse a pruebas independientes, en particular
Euler, operadores OTC, produccion, costos de ajuste y regla de cola.

## 3. Dos rutas correctas para cerrar la brecha

**Ruta A (equivalencia de ceros):** formalizar en Lean los
residuos transformados de Python y probar para cada fila `i`,
dentro de una caja economica positiva, `G_i(z,h)=0 iff
F_i(z,h)=0`. Entonces una raiz exacta obtenida con Banach para
`G` implica una raiz para el operador fuente `F`; las
cotas del Jacobiano de `G` no se adjudican falsamente a `F`.
Tambien deben comprobarse las constantes del modelo, los
valores heredados y la politica.

**Ruta B (evaluacion literal):** sustituir el residual numerico
por las 33 definiciones de fuente en niveles y el dual CRRA,
exportar nuevas cajas de derivadas con aritmetica dirigida,
construir un nuevo precondicionador y volver a ejecutar la
puerta Banach 34x34. Es una ruta mas directa a identidad
de operadores, pero exige revalidar cuidadosamente el
experimento y sus cotas.

Ambas rutas requieren demostrar regularidad C1 y la
correspondencia de la representacion de fuente (incluido el
sistema de Markov, masas, distribucion de pagos, tail).
No cabe declarar una raiz Lean sin completar ese puente.

## 4. Impacto en las afirmaciones

El certificado numerico anterior no debe eliminarse: sigue
certificando aritmeticamente un candidato bien definido.
Tampoco deben modificarse a mano sus hashes, cifras o
thresholds. Pero los teoremas Lean que recuperan las 33 filas
S y las 33 B asumen una raiz de la funcion LITERAL `H`,
cuya existencia no es aun consecuencia demostrada del
certificado de Python.

La IRF de remuneracion usa un shock `v_R=-1e-5`,
mayor que el radio `r_h=1e-15` del certificado local.
No inferir alcance de la IRF ni efectos de crecimiento de
largo plazo de estos resultados.

**Proxima compuerta:** exhibir una fila representativa con
prueba exacta de equivalencia de ceros en Lean (por ejemplo,
la fila bancaria 6) y establecer la condicion de parametros
del factor de renovacion; despues automatizar el inventario
de las 34 filas con testigos de equivalencia.
