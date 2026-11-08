# Del sistema reducido al equilibrio: trazabilidad del puente lógico

**Fecha de revisión:** 7 de noviembre de 2026. **Rama:** work/lean-ci-validation-otc-20261106. **Objeto:** distinguir el sistema de 33 ecuaciones, la complementariedad escalar, las condiciones óptimas de los agentes y el equilibrio competitivo infinito.

## 1. Teorema reducido frente a equilibrio completo

El código resuelve por separado \(F_r(Z,v_R)=0\), con 33 logincógnitas y \(r\in\{S,B\}\). Bajo un Jacobiano local invertible, la restricción de L se reduce a

\[
0\le s\ \perp\ \mathcal M(s,h)\ge0,\qquad h=v_R,\quad
\mathcal M(s,h)=a_Rh+bs+o(|s|+|h|),
\]

donde el caso auditado reporta \(a_R\simeq-3.219277533\) y \(b\in(-2.376742673,-2.376742670)\). Si, adicionalmente, la marginal reducida es continua, estrictamente decreciente en \(s\ge0\) y posee una raíz interior positiva para \(h<0\), las únicas soluciones escalares son B (\(s=0\)) y S (la raíz positiva). Para \(h>0\), si \(\mathcal M(0,h)<0\), no hay solución complementaria no negativa en el entorno decreciente.

El módulo nuevo **ScalarComplementarityMultiplicityCandidate.lean** formaliza precisamente la conclusión escalar bajo **premisas explícitas**: monotonía estricta, signo en cero y existencia previa de una raíz positiva. No deriva esas premisas del modelo económico, no prueba el IFT del prefijo y no certifica un equilibrio DSGE. Compilación **aprobada** en GitHub Actions, ejecución 42430587348, commit ab86ddfc0b9220ff7aa7f8fe8fa3856cfe4f182b, bajo Lean 4 v4.30.0-rc2 con dependencias fijadas. El registro específico de este módulo muestra para ambos teoremas únicamente los axiomas estándar `propext`, `Classical.choice` y `Quot.sound`; no aparece `sorryAx`. El teorema formal usa monotonía en todo el semieje `[0,∞)`, hipótesis **más fuerte** que la monotonía local del argumento escrito de la Proposición 4.2. Por ello el teorema compilado no constituye todavía una formalización exacta de toda la proposición del manuscrito.

## 2. Obstrucción lógica identificada en Lean

La interfaz fuente **PaperInterface.localMacroMultiplicitySpec** pide unicidad literal de una estructura Allocation. Pero **CompetitiveEquilibrium** no restringe el campo collateralDual: el teorema **competitiveEquilibrium_replaceCollateralDual_iff** muestra que puede cambiarse sin alterar el equilibrio. Consecuentemente, **ContinuationContractAuditCandidate.not_localExactContinuationAround** refuta la unicidad literal del carrier, y **Proposition42RefutationCandidate.localMacroMultiplicitySpec_false** demuestra que la especificación fuente de la Proposición 4.2 es inalcanzable.

La refutación concierne a la **especificación formal literal**, no demuestra que las dos ramas económicas S/B sean imposibles. **Proposition42PrimalRepairCandidate.localMacroMultiplicityPrimalSpec** propone comparar asignaciones tras borrar el dual libre, y **Proposition42PrimalSeparationCandidate.strict_slack_and_binding_primal_disjoint** distingue ambas ramas por holgura y cobertura activa en historias admitidas. La reparación está aún **sin testigo de existencia de ambos equilibrios**.

## 3. Matriz de obligaciones y evidencia

| Implicación requerida | Evidencia concreta | Estado autorizado |
|---|---|---|
| Construir estados y reglas monetarias del caso | finite_irf.py, finite_bridge_certificate.json | NUMÉRICO/ALGEBRAICO, parámetros ilustrativos |
| Resolver 33 relaciones con S y B por separado | audit_prefix_rows.py, finite_irf_validation.json | NUMÉRICO DEL REDUCIDO |
| Justificar \(\mathcal M\), sus signos y raíz positiva | Ecuaciones scalar_macro_complementarity y negative_schur; certificados del enlace | ESPECÍFICO/CONDICIONAL, sin reflexión Lean integral |
| Probar que la complementariedad escalar tiene dos soluciones | ScalarComplementarityMultiplicityCandidate, bajo monotonía y existencia de raíz | LEMA CONDICIONAL; kernel debe validarse en CI |
| Recuperar KKT de empresas y posiciones bancarias | audit_financial_blocks.py, DateZeroJointBindingSharedDualCandidate | CONDICIONAL/NUMÉRICO; no prueba suficiencia global |
| Construir el prefijo literal del modelo | BoundaryFullPrefixCandidate.boundary_full_prefix_equations | Condicionado a BoundaryWorkerLaborPackage, paquete analítico y signos de la raíz |
| Elevar prefijo a equilibrio competitivo infinito | finite_prefix_equilibrium, colas y condiciones terminales | PENDIENTE: suficiencia y puente de todas las ramas |
| Contar exactamente dos equilibrios | PrimalRepairCandidate y PrimalSeparationCandidate | PENDIENTE: no contar estructuras con duales libres |
| Probar crecimiento tendencial permanente | Acumulación y asignación condicional | PENDIENTE: falta un mecanismo probado de crecimiento sostenido |

El padre estacionario formalizado en StationaryEquilibriumCandidate **no es** por sí mismo la instancia de frontera ni una IRF ante shock. La continuidad no lineal reducida T=640 y la recursión de valor bancario tampoco prueban optimalidad dinámica para todas las políticas admisibles.

## 4. Correspondencia exacta con los enunciados del paper

**Proposición 4.1 — frontera:** la existencia de raíz de recursos no basta para elevar el prefijo a equilibrio; entre las premisas específicas está la FOC laboral en fecha cero, todavía aislada en BoundaryWorkerLaborPackage.

**Proposición 4.2 — multiplicidad:** debe distinguir las dos raíces de la complementariedad reducida de la proposición adicional de dos **equilibrios completos**. La segunda no está certificada y su contrato Lean de unicidad literal es contradictorio. La noción candidata correcta identifica clases de asignaciones **primales en el soporte**, no estructuras completas con duales libres.

**Proposición 4.5 — persistencia bajo riesgo:** exige una cola exacta, estimaciones uniformes y factibilidad global; no es la misma cosa que una IRF con prefijo Newton y cola lineal local, ni que una solución finita T=640.

**Proposición de enlace del apéndice:** es una implicación condicional válida solo después de establecer las premisas de todas las KKT originales, optimalidad de hogares/bancos/minoristas, dominio, precio global y condiciones terminales.

## 5. Compuertas para una afirmación más fuerte

1. **Semántica:** igualdad de variables primales sobre historias admisibles y dual canónico cuando la KKT lo determine.
2. **Álgebra:** las 33 ecuaciones deben reconstruir todos los presupuestos, contratos, restricciones y márgenes originales.
3. **Dinámica:** continuación no lineal exacta con condiciones terminales y optimalidad global por agente.
4. **Formalización:** testigos de CompetitiveEquilibriumWithInitialIntervention para S/B; separación primal y unicidad **modulo** duales libres, con axiomas auditados al commit exacto.
5. **Edición:** resumen, proposiciones, prueba escrita, slides y ledger de 57 resultados no pueden atribuir a las IRF un teorema de equilibrio infinito que permanece abierto.

**Decisión:** mantener PR en borrador y main intacta; la afirmación comprobable hoy son respuestas de dos soluciones numéricas locales del sistema reducido, no una multiplicidad de equilibrios completos certificados.

## 6. Adenda de formalizacion local (7 de noviembre de 2026)

El teorema abstracto anterior sobre `Set.Ici 0` sigue disponible como
antecedente, pero ya no es el unico lema escalar:

- `LocalScalarComplementarityCandidate.lean` prueba dos y solo dos soluciones
  **dentro de** `[0, eps]`, dadas continuidad y estricta monotonia decreciente
  en ese intervalo, signo `M(0)>0>M(eps)` y `eps>0`. La raiz interior
  **se construye** por el teorema del valor intermedio, en lugar de suponerse.
  Tambien prueba inexistencia local si `M(0)<0` y la funcion decrece.
  Compilacion GitHub Actions
  [42433535673](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/42433535673),
  commit `e4e953749d0ccd151754ff550b48c72ba1fde86f`.
- `LocalScalarDerivativeBridgeCandidate.lean` deriva la monotonia local
  a partir de continuidad en `[0,eps]` y `deriv M s < 0` para todos
  los puntos `s` del intervalo abierto `(0,eps)`. Reutiliza el lema
  local para obtener ambas conclusiones. Compilacion GitHub Actions
  [42433852389](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/42433852389),
  commit `e997bbe043eadbe2bfcc8fdeaa91faed23ad67bb`.
- Los registros guardados de ambos modulos muestran, en sus respectivas
  declaraciones principales, solo `propext`, `Classical.choice` y
  `Quot.sound`, sin `sorryAx`. La compilacion de un teorema condicional
  no demuestra sus premisas para el residual economico especifico.

La Proposicion 4.2 del manuscrito **si** declara `C^1` en torno a
`(s,h)=(0,0)`, con derivadas parciales negativas; el argumento escrito
es condicional a esas hipotesis. En contraste,
`EconomicModel.LocalScalarImplicitReduction` solo especifica
`DifferentiableOn` y cotas de `fderiv` en el origen. Todavia falta
derivar rigurosamente el control de derivadas sobre un entorno,
la existencia de `eps` y de signos cruzados para cada `h<0`
pequeno a partir de una fuente `C^1` verificable del sistema de 33
ecuaciones. Una derivada negativa en un solo punto, sin regularidad
adicional, **no prueba** monotonia en un intervalo.

**Alcance exacto:** se han cerrado lemas de analisis de la
complementariedad escalar bajo supuestos expuestos. NO hay aun un
teorema Lean correspondiente al enunciado completo de la
Proposicion 4.2, no hay testigos completos de equilibrio para S y B
y no se ha demostrado crecimiento sostenido.

## 7. Bifurcacion parametrica local: revision Lean verificada

Revision de **codigo**: `944e88493d9dec319193f82e5761ed00a605fb1b`.
Auditoria especializada:
[Lean 4 candidate audit 42437102498](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/42437102498)
(`success`). Se inspecciono tambien el artefacto de logs `lean-candidate-audit-logs`
de esa ejecucion: los nueve teoremas nuevos de los siguientes cuatro
modulos se elaboraron sin `sorryAx`. Las listas de axiomas incluyen solo
`propext`, `Classical.choice` y `Quot.sound`.

- `LocalScalarShockSignCandidate.lean`: una derivada negativa en cero
  y valor inicial nulo producen signos estrictos opuestos a los dos
  lados de cero, y una derivada positiva implica signo negativo bajo
  perturbaciones negativas suficientemente pequenas.
- `LocalScalarPolicyBifurcationCandidate.lean`: para `M(s,h)`, si
  `d_h M(0,0)=a<0` y una trayectoria transversal `s=-K h`,
  `K>0`, tiene derivada `c>0` en cero, continuidad y antitonicidad
  local de cada corte `M(.,h)` implican un `delta>0` y para cada
  `-delta<h<0` una raiz unica `0<r(h)<-K h`. Las soluciones
  complementarias *dentro de ese intervalo* son `0` y `r(h)`.
  Para `0<h<delta`, una condicion analoga de antitonicidad
  excluye soluciones locales. No se presupone una raiz positiva.
- `LocalScalarJointDerivativeBridgeCandidate.lean`: las derivadas
  direccionales del eje de politica y de la trayectoria proceden de
  un unico `HasFDerivAt` del mapa bivariado en `(0,0)`. Esto
  prueba las conclusiones parametricas bajo los signos del operador
  lineal y la regularidad de los cortes locales.
- `LocalScalarTransverseRayCertificateCandidate.lean`: para un
  operador lineal continuo `L` sobre `R x R`, si
  `a=L(0,1)<0` y `b=L(1,0)<0`, se prueba
  `exists K>0, L(-K,1)>0`. La construccion concreta
  `K=(1-a)/(-b)` da `L(-K,1)=1`. La existencia de la
  trayectoria no se postula.

**Instrumento:** en el codigo original, `h=v_R` se inyecta mediante
`localScalarParameterIntervention.reserveRateInnovation`.
No se debe rebautizar automaticamente como shock a la tasa de
politica general, coeficiente de encaje ni remuneracion sin mantener
las etiquetas economicas y unidades exactas. Las demas innovaciones
`v_M, v_rho, v_Delta` permanecen fijas en esta especializacion.

**Puentes pendientes y no demostrados:**

1. Exponer como `M(s,h)` del candidato es exactamente el
   `localScalarReducedMap` evaluado en la perturbacion de
   `Fin 5`, y certificar `M(0,0)=0`.
2. Obtener la derivada conjunta de `M` desde la solucion local
   de las 33 filas, incluyendo las derivadas firmadas y el control
   de regularidad en un entorno; no confundir una cota de derivada
   en el origen con la monotonia de todos los cortes.
3. Establecer el dominio de continuacion y signos sobre el cono
   `0<=s<=-K*h` para cada `h<0`, mas la recuperacion unica de
   las 33 incognitas y la correspondencia correcta de las ramas S/B.
4. Construir testigos de equilibrio infinito, optimalidad de
   todos los agentes, transversales, clearing y estabilidad de
   la cola para ambas ramas. Ninguno de los lemas de esta seccion
   establece esto, crecimiento permanente ni cuantifica bienestar.

La Proposicion 4.2 conserva por tanto el estatus de
**argumento condicional de multiplicidad reducida** con una
subcadena escalar parametrica ahora verificada en Lean. No se
promueve su afirmacion economica completa a teorema Lean cerrado.

## 8. Puentes economicos exactos de S/B (auditoria del 7 de noviembre de 2026)

**Revision de codigo auditada:** `99a0d16cb2ba585873cd9f95a2252ad5b9c62df0`.
GitHub Actions:
[Lean 4 candidate audit 42440990139](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/42440990139)
(`success`).
Artefacto `lean-candidate-audit-logs`, ID `13601423778`.
Se inspeccionaron los logs individuales de todos los modulos `LocalScalar*`
y `axioms.log`: sin `sorryAx` y sin errores de compilacion.
Este cierre **no es un certificado de las hipotesis economicas de entrada**.

### 8.1 Identidad de fuente y derivadas

- `LocalScalarEconomicSliceCandidate.lean` construye el vector
  `y(s,h)=(s,h,0,0,0)`, donde `h=v_R` es innovacion de la
  **regla de remuneracion de reservas**. La funcion
  `economicReserveRemunerationMarginal` es literalmente
  `localScalarReducedMap P Z0 solutionLog (reserveRemunerationSlice s h)`,
  esto es el dual de la firma L en las coordenadas de las 33 filas.
  A partir de `LocalScalarImplicitReduction` se extraen las filas
  modificadas, no se prueba existencia de un `solutionLog`.
- `LocalScalarEconomicDerivativeBridgeCandidate.lean` prueba que
  las derivadas sobre el eje `(0,h)` y la trayectoria
  `(-K h,h)` provienen del `fderiv` de la unica funcion
  economica `localScalarReducedMap`.
- `LocalScalarEconomicPolicyCertificateCandidate.lean` construye
  `K>0` desde los signos `b<0` y `a_R<0` y demuestra
  dos raices complementarias bajo las premisas locales. Se corrigio
  una hipotesis excesivamente fuerte: **el radio de continuidad y
  antitonicidad puede depender de `K`**, en vez de imponer un
  radio comun para todas las pendientes transversales. Se mantiene
  una cota externa `rho>0` sobre el shock.

### 8.2 Recuperacion de las 33 filas modificadas

`LocalScalarEconomicConeRowsCandidate.lean` prueba para el
vector economico de cinco coordenadas la cota
`norm(y(s,h)) <= abs(s)+abs(h)`.
Con `0<=s<=-K*h` y `h<0`, una innovacion
`-h<radius/(K+1)` deja `y(s,h)` dentro de la bola
donde el predicado `LocalScalarImplicitReduction` asegura el
cumplimiento de las **33 filas modificadas**.
En particular, se cubren tanto `s=0` como la raiz
interior `0<r(h)<-K*h`. La fila 5 modificada prescribe
la holgura; no es automaticamente una fila original de B o S.

### 8.3 Recuperacion de condiciones originales de L

- `LocalScalarEulerRegimeReconciliationCandidate.lean` prueba
  exactamente la identidad
  `Euler_B(L)-Euler_S(L) = -pledgeUnit(L)*fundingDual(L)`.
  Si el dual se anula, ambos Euler coinciden. Con tasa de
  prestamo no nula, el dual cero tambien satisface la fila
  de financiamiento de S.
- `LocalScalarOriginalEulerRowsCandidate.lean` identifica ese
  dual con `localNormalizedCollateralDualL` del mismo modelo
  original y prueba las dos implicaciones sobre las **filas fuente**
  de S (financiamiento y Euler del capital).
- `LocalScalarOriginalCollateralKktBridgeCandidate.lean`
  muestra que las primitivas de la intervencion no cambian
  directamente las formulas de holgura y dual, recupera la
  holgura original de L desde la fila 5 y demuestra la
  complementariedad original `LocalScalarComplementarityL`
  desde la complementariedad escalar.
- `LocalScalarOriginalInteriorSBranchCandidate.lean`
  utiliza `s>0`, filas modificadas 3 y 5, complementariedad
  escalar y `loanRate != 0` para recuperar el KKT de L y
  las dos filas originales propias de S.
- `LocalScalarOriginalBoundaryBBranchCandidate.lean`
  utiliza `s=0` y un **denominador de colateral no nulo**
  para reconstruir la fila original de promesa nominal
  vinculante de B. No se divide por un factor cuyo signo
  o no anulacion no haya sido supuesto.

### 8.4 Compuertas pendientes

Estos son teoremas **condicionales** compilados sobre funciones
fuente exactas; siguen sin demostrarse las siguientes premisas
y consecuencias para el modelo numerico:

1. **Existencia y dominio:** construir la referencia `Z0` y
   `solutionLog` con `LocalScalarImplicitReduction`,
   incluidas las 33 ecuaciones, unicidad y diferenciabilidad.
2. **Certificacion del Schur:** enlazar el Jacobiano economico
   real con la inversa intervalar certificada y comprobar los
   signos numericos de `a_R` y `b`, no asumirlos.
3. **Regularidad local:** derivar de una fuente `C^1`
   verificable el radio `rho_K`, la monotonia del residual
   en los cortes y `M(0,0)=0`, en lugar de introducirlos
   como premisas aun sin testigo.
4. **Dominio y ramas:** derivar positividad de tasas de
   prestamo, no anulacion del denominador de colateral y
   trasladar las otras filas del sistema auxiliar a las
   ecuaciones originales de cada regimen, comprobando
   condiciones activas y factibilidad.
5. **Equilibrio infinito:** construir `Allocation`,
   verificar `FirmOptimal`, `BankPopulationEquilibrium`,
   KKT de todos los agentes, clearing, condiciones terminales
   y continuidad de la cola. No inferir de estos lemas
   resultados de crecimiento sostenido, bienestar o
   unicidad global.

**Veredicto de calidad:** el puente desde la marginal fuente
al KKT local de L es una cadena de pruebas Lean *bajo
hipotesis explicitas*. La Proposicion 4.2 **no** debe
promoverse aun a prueba de dos equilibrios competitivos
completos ni de crecimiento de largo plazo.

## 9. Puente C1 a monotonia local: nueva cadena Lean verificada

**Codigo:** `LocalScalarEconomicC1MonotonicityCandidate.lean`,
commit `80a53bb6fe79e62a133df73e65ef08fed366d7c5`,
[CI 42442206679](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/42442206679)
(`success`). Los cuatro teoremas del modulo tienen unicamente
`propext`, `Classical.choice` y `Quot.sound` como axiomas
y ningun `sorryAx` (logs individuales y `axioms.log` inspeccionados).

**Hipotesis mas debil que C1:** continuidad en el origen de
`y ↦ (fderiv R M y) localScalarSlackDirection`.
Como `LocalScalarImplicitReduction` ya afirma
`(fderiv R M 0) localScalarSlackDirection < 0`, esa
continuidad implica una bola con derivada direccional
estrictamente negativa. La cota del cono
`norm(reserveRemunerationSlice s h) <= abs(s)+abs(h)`
entonces proporciona para cada `K>0` un radio `rhoK>0`
donde `s ↦ M(s,h)` es continua y estrictamente decreciente
sobre `[0,-K*h]`, con `-rhoK<h<0`.
**La antitonicidad deja de ser una hipotesis separada**.
El teorema final del modulo construye las dos soluciones
complementarias locales y verifica las 33 filas modificadas
en ambas, bajo `LocalScalarImplicitReduction`,
`M(0)=0` y continuidad direccional del Schur en cero.

**Puente a la notacion del manuscrito:**
`LocalScalarEconomicContDiffBridgeCandidate.lean`,
commit `f781f17a7beb6bd7aa663bbf39b2e5bb9090540c`,
[CI 42442264792](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/42442264792)
(`success`). Los dos teoremas se elaboraron sin `sorryAx`.
`ContDiffAt R 1 M 0` implica continuidad de `fderiv M`
en cero y, por evaluacion en la direccion de slack,
la condicion de continuidad anterior. Esta es una
**implicacion de analisis demostrada**, no prueba que
la `M` del sistema calibrado satisfaga `ContDiffAt`.

**No atribuir a estos lemas** existencia o unicidad de
`solutionLog` para las 33 ecuaciones; valores firmados
del Jacobiano real; realizacion de ramas S/B de la estructura
`Allocation`; ni trayectorias macroeconomicas o crecimiento.

**Nota de trazabilidad numerica:** el archivo
`code/v0m/cierre_interno_2026_10_17/finite_bridge_certificate.json`
reporta un intervalo negativo para
`branches.binding.reduced_mu_derivative_with_respect_to_slack`;
`branches.slack.reduced_mu_derivative_with_respect_to_slack`
figura `null`. No tratar ambas ramas como portadoras de
un certificado numerico independiente del mismo tipo.

**Proximo cierre:** identificar un testigo fuente de
`LocalScalarImplicitReduction`, `ContDiffAt R 1`
y `M(0)=0` conectado al Jacobiano original con
aritmetica intervalar; despues establecer suficiencia
de todas las condiciones originales y la cola dinamica.

## 10. Dominio positivo del chart original: auditoria Lean verificada

Archivo `LocalScalarPositiveLogChartDomainCandidate.lean`,
commit `32c8a4c573cd8e5bae94f8b206d1bc0307a11be3`;
[GitHub Actions 42442324909](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/42442324909):
`success`. Se inspeccionaron los siete `#print axioms` de este
modulo, todos con `propext`, `Classical.choice`, `Quot.sound`,
y ningun `sorryAx`. El `axioms.log` global tampoco incluye
`sorryAx`.

El teorema `localPrefixLogChart_positive` prueba literalmente
`LocalPrefixCoordinatesPositive (localPrefixLogChart Z0 z)`
para todo vector `z : Fin 33 -> R` si
`LocalPrefixCoordinatesPositive Z0`: cada coordenada recuperada es
`Z0_j * Real.exp(z_j)`. No hay que imponer positividad por separado
en cada shock.

Los lemas `localPrefixLogChart_loanRate_pos` y
`economic_log_solution_loanRate_ne_zero` aseguran que la tasa
de prestamo del prefijo en la rama S no se anula. Las coordenadas
capital de L, inflacion de fecha uno y precio de capital
tambien son estrictamente positivas en el chart.

Con dos premisas de dominio de primitivas,
`0 < P.pledgeability FirmType.L` y `P.depreciation < 1`,
`economic_log_solution_B_denominator_ne_zero` demuestra
la no anulacion del denominador de la ecuacion original de
colateral vinculante de B para el vector de politica de fuente.

**Alcance:** estos lemas satisfacen las condiciones de dominio
que hasta ahora eran argumentos independientes en los puentes
Euler/colateral; no construyen `Z0` ni demuestran por su
cuenta `LocalPrefixCoordinatesPositive Z0`.
El predicado `LocalReducedPrefixLogJacobianCertifiedAt`
ya incluye esta positividad como condicion explicita,
pero ese certificado de Jacobiano **no tiene testigo Lean
construido para la calibracion**.

**Proxima compuerta verificable:** producir un testigo
`LocalReducedPrefixLogJacobianCertifiedAt` con la derivada
de las 33 filas de fuente, las identidades de inversa y la
cota normada; enlazarlo mediante IFT a una funcion
`solutionLog` realmente `ContDiffAt R 1`; comprobar el
dual basal y los signos `b<0, a_R<0` sobre la misma
calibracion, sin atribuir un certificado de B a S.
