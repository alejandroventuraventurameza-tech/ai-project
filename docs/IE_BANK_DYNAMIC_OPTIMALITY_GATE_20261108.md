# IE project — compuerta de optimalidad dinámica bancaria (2026-11-08)

**Objeto exacto:** `BankContinuationOptimalAt P X t h equity candidate`, definido en `lean/checkpoint/modules/Ventura26LiquidityAllocation/EconomicModel.lean`.

**Rama de trabajo:** `work/lean-ci-validation-otc-20261106`. El PR #2 permanece **draft**; no se debe fusionar con `main` sin completar las compuertas.

## 1. Resultados demostrados por Lean en la revisión previa

**Run:** [#42524300074](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/42524300074), SHA `3ca430ed4d08b0fe2a44583d3a36f39f5eaaf577`. Compilación enfocada y auditoría `#print axioms` aprobadas, sin `sorryAx`.

- `PaperBankGlobalDividendBoundFromNormalizedCandidate`: positividad de retención en bancos factibles con patrimonio inicial positivo; cota de Bellman de cartera desde óptimo normalizado; cota conjunta de cartera y dividendos cuando `κ>=1`.
- `PaperBankZeroEquityBoundaryCandidate`: cláusula de controles nulos a patrimonio cero, retorno nulo de cartera cero, valor Bellman nulo con valor futuro homogéneo y cota conjunta de patrimonio inicial arbitrario (incluyendo cero).

Estos son **teoremas condicionales demostrados**, no una prueba de que exista un óptimo unitario, `κ>=1`, una candidata con valor alcanzado, o un equilibrio global.

## 2. Nuevas implicaciones candidatas (kernel pendiente)

**Módulos**:
- `PaperBankUnitKKTAllEquityBridgeCandidate.lean`, commit `50d2f302`. Recibe todos los cinco multiplicadores KKT no negativos, cinco complementariedades, factibilidad del portafolio de patrimonio retenido uno, supergradientes OTC y ecuaciones de precios del modelo. Deduce `BankStaticPortfolioOptimalAt` fuente para patrimonio uno invocando el teorema existente `source_bank_static_optimal_with_all_bank_nonneg_corners`. Con homogeneidad del valor, condiciones primitivas de positividad que dan `W_t>0`, y `κ_t>=1`, deduce la cota conjunta para **toda** política de continuación factible y **todo** patrimonio inicial no negativo.
- `PaperBankDynamicOptimalityFromEnvelopeCandidate.lean`, commit `1f36d9b9`. Convierte la cota conjunta anterior a la propiedad exacta `BankContinuationOptimalAt`, **solo** bajo la suma de supuestos de abajo.

Compilación y `#print axioms` integrados al workflow focalizado en commit [`4e66264c`](https://github.com/alejandroventuraventurameza-tech/ai-project/commit/4e66264c96bcb37a8ff1b8a12d28cb91b484eecc). **No promover a DEMOSTRADO hasta kernel verde del SHA correspondiente.**

## 3. Obligaciones económicas todavía sustantivas

| Id | Enunciado que requiere prueba | Por qué es necesario |
|---|---|---|
| BK1 | Construir cartera unitaria que sea fuente-factible y verificar su KKT con 5 duales y supergradientes a precios de equilibrio. | El wrapper KKT no proporciona un testigo numérico/económico. |
| BK2 | Demostrar `κ_t = W_t Π_t^* >= 1` a partir de parámetros/precios/valores consistentes, o resolver el caso `κ_t<1` sin suponer máximo inexistente. | Con `κ_t<1`, repartir dividendos puede dominar la retención y la frontera positiva puede dar no-alcanzabilidad. |
| BK3 | Construir `candidate` factible en todas las historias soportadas; verificar `BankContinuationObjectiveWellDefinedAt` (sumabilidad), `BankContinuationTerminalConditionAt` y que su valor real satisface `J_t(candidate)=κ_t e_t`. | Una cota global no demuestra que se alcance. |
| BK4 | Probar para **cada alternativa** con objetivo bien definido la sumabilidad de cada cola sucesora relevante o derivarla del objetivo global. | Habilita `bankContinuationPayoffAt_first_step`; debe usarse la medida finita soportada fuente. |
| BK5 | Probar para las mismas alternativas `J_{t+1}(tail(q,s,ω)) <= V_{t+1}(e_{t+1},h_{t+1})`, por inducción/envolvente independiente o definición de función valor, **sin presuponer `BankContinuationOptimalAt` en las colas**. | Evita circularidad. |
| BK6 | Extender la certificación local a cada fecha/historia admisible y acoplarla a `BankFeasible`, `BankBellmanLocalEnvironmentAt` y `BankOptimalWithValue`. | Cierre de `BankOptimal` y del sistema de equilibrio. |

**Precisión sobre terminalidad:** el predicado fuente exige condición terminal para la candidata, **no** TVC para toda política alternativa. El enunciado condicional nuevo respeta esta distinción.

## 4. Lectura correcta del resultado

Si BK1–BK5 son comprobados como premisas para una economía concreta, la desigualdad de primer período y la conexión con el payoff infinito proporcionan dominancia entre continuaciones, no solo entre carteras a retención fija. Solo entonces se puede certificar `BankContinuationOptimalAt` para una candidata concreta. BK6 sigue siendo necesario para `BankOptimal`. No es legítimo declarar impacto causal de política monetaria, corrección de misallocation dinámica o crecimiento de largo plazo a partir de estos puentes locales.

**Semáforo actual:**
- Condicionales compilados en #42524300074: **DEMOSTRADO**.
- Nuevos puentes BK1–BK6: **PENDIENTE** en tanto no existan testigos y/o kernel del commit actual.
- IRF y mecanismo de crecimiento: pruebas económicas/numeración causal **PENDIENTES** según auditoría propia de cada simulación.
