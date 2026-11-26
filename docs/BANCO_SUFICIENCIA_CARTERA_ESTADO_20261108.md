# IE project — Banco: suficiencia global de cartera en una fecha

**Fecha de investigación:** 2026-11-08.  
**Rama:** `work/lean-ci-validation-otc-20261106`.  
**Declaración Lean candidata:** `PaperBankStaticSupergradientSufficiencyCandidate.lean`.  
**Estado de evidencia:** los dos teoremas estáticos del módulo de cartera bancaria superaron CI focalizada y auditoría `#print axioms` sin `sorryAx`: [#42506496740](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/42506496740) (SHA `d42f9325709189ea87af4c686361c41ad816b8f0`) y [#42506614812](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/42506614812) (SHA `51b18f81c847e20a866850df5435a4a501de9682`). Los dos teoremas bancarios de continuación Bellman también fueron verificados por CI focalizada sin `sorryAx`: [#42506650961](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/42506650961), SHA `164c20e3f64b451a142bd11749ca9c86355e8f9c`, y [#42506762177](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/42506762177), SHA `ded39799ec6bb747ebfba5898ce229528c628ccd`. Solo abarcan comparaciones de una fecha.

## 1. Pregunta económica y alcance

La solución numérica de los regímenes S/B satisface KKT del banco y 33 ecuaciones reducidas de prefijo con residuos pequeños. Pero una condición de primer orden no equivale por sí sola a suficiencia, no demuestra optimalidad bancaria intertemporal ni justifica la selección del equilibrio.

**Meta de esta campaña:** demostrar que, en una historia agregada fijada, con precios, tecnología de liquidación, soporte de pagos y patrimonio retenido dados, una cartera factible que soporte la función cóncava de liquidez y satisfaga los precios de equilibrio no puede ser superada por **ninguna cartera alternativa factible**. No se supone que cada alternativa conserve las mismas señales de liquidación de la candidata.

## 2. Variables y ecuaciones originales del modelo

Denotar por `b,m,d,e` el préstamo, las reservas iniciales, los depósitos y el patrimonio retenido del banco individual, con identidad

```text
b + m = d + e.
```

`R^L` es la tasa bruta de préstamo; `R^R` es la remuneración bruta de reservas; `R^D` es la tasa bruta de depósitos; `rho` es el coeficiente **de encaje** (distinto de la remuneración); `xi=R^D/R^R`; `epsilon` es el shock idiosincrático de pagos y `chi` el payoff cóncavo pieza a pieza en función del saldo de liquidación.

```text
s(m,d,epsilon) = m - rho*d + (xi-rho)*epsilon*d
R(b,m,d,epsilon) =
  R^L*b + R^R*m - R^D*d + chi(s(m,d,epsilon))
E[R] = R^L*b + R^R*m - R^D*d + E[chi(s)].
```

Estas funciones son `bankSettlementSurplus`, `bankReducedPortfolioReturnWithShock` y `bankStaticPortfolioPayoffAt` del `EconomicModel.lean`. La igualdad del rendimiento **detallado** que incluye posiciones OTC/facilidad con el reducido `chi` ya está demostrada allí por `bankDetailedPortfolioReturn_eq_reduced`, bajo `R^R != 0`.

## 3. Condiciones de suficiencia y demostración matemática

Sean `(b*,m*,d*)` la cartera candidata factible, y `mu(epsilon)` un supergradiente de `chi` en el saldo de la candidata para cada pago respaldado por la distribución:

```text
chi(s(m,d,epsilon)) <= chi(s(m*,d*,epsilon))
   + mu(epsilon) [s(m,d,epsilon)-s(m*,d*,epsilon)].
```

El punto de quiebre `s*=0` NO se descarta: cualquier valor de pendiente dentro del intervalo correcto es admisible. Las probabilidades no negativas permiten integrar la desigualdad.

Definir `muBar=E[mu]`, `muShock=E[mu*epsilon]` y `Delta b=b-b*` etc. Por linealidad exacta del saldo,

```text
Delta s(epsilon) = Delta m - rho*Delta d
                   + (xi-rho)*epsilon*Delta d.
```

Así,

```text
E[R(b,m,d)] - E[R(b*,m*,d*)]
  <= R^L*Delta b + R^R*Delta m - R^D*Delta d
     + muBar*(Delta m-rho*Delta d)
     + (xi-rho)*muShock*Delta d.
```

Bajo **los precios de solución interior sin duales de caps**:

```text
R^L = R^R + muBar
R^D = R^R + (1-rho)*muBar + (xi-rho)*muShock,
```

el miembro derecho se reduce exactamente a

```text
(R^R+muBar)*(Delta b+Delta m-Delta d)=0,
```

porque ambas carteras comparten `e` en sus balances. Por tanto,

```text
E[R(b,m,d)] <= E[R(b*,m*,d*)]
```

para toda alternativa factible. El teorema Lean candidato exige factibilidad literal de cartera de la fuente, soporte válido de cada supergradiente y precios exactamente enunciados; **no introduce directamente la desigualdad final como premisa**.

## 4. Qué implica y qué NO implica

**Con las dos pruebas estáticas ya compiladas y auditadas:** se certifica un teorema de suficiencia **estática, condicional** que se mantiene ante cambios arbitrarios del patrón déficit/superávit de la cartera alternativa. Es un avance frente a la simple verificación local KKT y complementa los diagnósticos de la cartera bancaria bajo ambas ramas.

**Pendiente:** instanciar en las trayectorias numéricas exactas las condiciones de precios y gradientes como predicados `Primitives/Allocation` para cada nodo; demostrar la continuación Bellman para TODAS las alternativas admisibles; vincular el valor individual a la dinámica de equity y los pagos de salida; comprobar terminalidad; establecer factibilidad y optimalidad de todos los agentes e identificar equilibrios completos; seleccionar de forma defendible las ramas S/B. No confundir los residuos reducidos de las IRF con suficiencia de equilibrio.

La auditoría numérica existente está en `code/irf/output/financial_blocks_audit/REPORT.json` y `REPORT.md`; registra los coeficientes de soporte cercanos a cero, márgenes y duales, pero el certificado numérico de las ramas **no** demuestra estos supuestos para un equilibrio de horizonte infinito.

## 5. Segunda obligación: renovación bancaria de la fuente

La fórmula del checkpoint usa `aB = 1-bankExit+bankExit*bankSeedShare`; el reproductor Python utiliza `aB = 1/referenceLoanRate`. Son equivalentes únicamente si

```text
bankExit*(1-bankSeedShare) = 1 - 1/referenceLoanRate.
```

El módulo `LocalScalarBankRenewalCalibrationBridgeCandidate.lean` prueba la equivalencia algebraica **condicional**, no la identidad de parámetros concretos. Por ello una prueba de cartera no resuelve automáticamente la correspondencia de renovación ni el prefijo numérico. Debemos reconstruir la calibración `bankSeedShare` y verificar su admisibilidad y fuente en una prueba independiente.

## 6. Puente de suficiencia de una fecha hacia Bellman (verificado condicionalmente)

El nuevo `PaperBankBellmanStaticSufficiencyCandidate.lean` vincula el predicado fuente `BankStaticPortfolioOptimalAt` con `bankBellmanContinuationAt`. Sea `V_{t+1}(e,s)` un valor de continuación positivamente homogéneo en patrimonio para todos los estados sucesores respaldados. La biblioteca fuente establece, para toda cartera **factible** con retorno real no negativo,

```text
BellmanContinuation_t(b,m,d; V_{t+1})
 = w_t(V_{t+1}) * bankStaticPortfolioPayoff_t(b,m,d),
```

donde `w_t(V_{t+1})` es independiente de la cartera individual cuando los precios y el estado agregado se mantienen fijos.

El nuevo teorema invoca esa igualdad **separadamente para la candidata y la desviación factible**, y usa `w_t>0` para preservar la desigualdad estática. De este modo, la candidata domina cualquier desviación en la comparación de continuación de **una fecha**. No se deduce una condición terminal ni se construye un selector de estrategias para toda historia; ambos siguen pendientes.

**Estado:** los dos teoremas de comparación de una fecha pasaron Lean y auditoría de axiomas sin `sorryAx`. Evitar llamar a esto `BankOptimal` o equilibrio completo: la función de valor efectiva, la política óptima infinita y el límite terminal aún no están demostrados.

## 7. Evidencia final de la campaña bancaria

**DEMOSTRADO en Lean (enunciados condicionales originales de cartera y Bellman):**

- `source_bank_static_portfolio_optimal_of_supergradients`: [CI #42506496740](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/42506496740), SHA `d42f9325709189ea87af4c686361c41ad816b8f0`.
- `source_bank_static_portfolio_optimal_of_selected_marginal`: [CI #42506614812](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/42506614812), SHA `51b18f81c847e20a866850df5435a4a501de9682`.
- `source_bellman_portfolio_ranking_of_static_global_optimality`: [CI #42506650961](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/42506650961), SHA `164c20e3f64b451a142bd11749ca9c86355e8f9c`.
- `source_bellman_portfolio_ranking_with_derived_weight`: [CI #42506762177](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/42506762177), SHA `ded39799ec6bb747ebfba5898ce229528c628ccd`.

**Comprobación:** los cuatro `#print axioms` son compatibles con el kernel y no presentan `sorryAx`. Las dos últimas declaraciones no afirman que el banco haya maximizado su valor a lo largo de todas las historias, sino que en cada historia la comparación Bellman preserva una dominancia estática si el valor de continuación presenta las propiedades de homogeneidad requeridas. El diagnóstico de 33 ecuaciones y la auditoría de KKT del banco siguen siendo `NUMERICO`, no una instancia de `BankOptimal`. No cerrar la Proposición 3.8 original o la existencia de equilibrio completo sobre la base de estas declaraciones por separado.
