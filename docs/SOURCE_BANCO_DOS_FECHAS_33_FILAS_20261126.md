# SOURCE bancario: transformación exacta en dos fechas sobre las 33 ecuaciones

**Corte:** 26 de noviembre de 2026. **Fuente:** `lean/checkpoint/modules/Ventura26LiquidityAllocation/EconomicModel.lean`; módulo probado `lean/current/CurrentSourceTwoDateBankTargetization.lean`.
**Verificación kernel:** [Actions #45880659556](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/45880659556) — 2,277 trabajos completados, sin `sorryAx`, axiomas `[propext, Classical.choice, Quot.sound]`.

## Qué se demostró

Sean P las mismas primitivas SOURCE, I el mismo estado heredado, Z las coordenadas económicas del prefijo, y `dateOneState`, `recurrent` y `tail` los mismos argumentos en ambas representaciones. El vector `originalPrefix33` utiliza las 33 ecuaciones reales de `localReducedPrefixResidual`, en el orden SOURCE. `targetizedPrefix33` conserva las otras 27 filas y sustituye explícitamente las bancarias 14, 15, 16, 30, 31 y 32 por sus fórmulas SOURCE con objetivos de política monetaria. Las reglas de tasa y cantidad (12, 13, 28, 29) **no** se eliminan.

El teorema `targetizedPrefix33_eq_fullEconomicBankShear` demuestra, punto por punto en el dominio admisible, la identidad vectorial exacta

    F_target(Z) = E(Z) F_SOURCE(Z)

donde E(Z) es la transformación triangular `sourceTwoDateBankFiveRowShear`, con ocho coeficientes `sourceLoanCross`, `sourceDepositCross`, `sourceBalanceRateCross` y `sourceBalanceQuantityCross`, cuatro de cada fecha, dependientes del estado económico. No se congelan los coeficientes ni se utiliza aproximación de Taylor. Se usa la identidad exacta ya certificada `expSecant(u) * u = exp(u)-1`.

El teorema `targetizedPrefix33_zero_iff_originalPrefix33_zero` deriva la equivalencia exacta de ceros por inversión algebraica de E(Z). `targetizedLogPrefix33_zero_iff_sourceLogPrefix33_zero` reexpresa esa conclusión en la carta logarítmica real `localPrefixLogChart Z0 z` del propio SOURCE, no en una carta inventada por Python.

## Hipótesis que sí permanecen

`P.matchingIntensity = Real.log 2` y, **en cada fecha por separado**, `TargetBankAdmissible`: tightness ≤ 1, tasa de reservas realizada positiva, reservas realizadas positivas, razón reservas/depósitos SOURCE no nula, y razón de depósito evaluada a la tasa objetivo no nula. Esta prueba no acredita que una calibración o caja numérica concreta satisfaga todas esas hipótesis.

## Evidencia y trazabilidad

- [Actions #45880659556](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/45880659556): etiqueta `SOURCE_TWO_DATE_33_NONLINEAR_TARGETIZATION_KERNEL_OK`, 2,277 trabajos, sin axiomas no fundacionales.
- Los intentos iniciales #45878485964, #45879270947 y #45879875847 fallaron por estrategia de simplificación y un error de edición. No constituyen certificación; el commit `858a13c729ed708a3031d8fe974393603a56d070` corrigió la prueba y generó la ejecución final exitosa.
- No se modifican el manuscrito `paper/paper.tex`, los valores de calibración ni las IRF.

## Frontera científica abierta

El resultado es **SOURCE original vs SOURCE targetizado**. No identifica `finite_irf.py` con las 33 ecuaciones económicas, ni transporta por sí solo derivadas SOURCE a matrices Python. Faltan la identidad funcional con las 23 filas restantes y todas las convenciones de pagos, coordenadas y normalizaciones, la verificación de los supuestos sobre una bola y la diferenciabilidad de E(Z) para formalizar el transporte de Jacobiano en una raíz.

El testigo `LocalScalarImplicitReduction` para las 33 filas, la invertibilidad y cota del Jacobiano económico, la raíz aumentada 34 con dual de financiación L igual a cero, la recuperación de ambas ramas S/B para un único estado heredado, las condiciones intertemporales y la prueba oficial `PaperContribution` permanecen ABIERTAS. Una igualdad de conjuntos de ceros no demuestra que el conjunto sea no vacío.