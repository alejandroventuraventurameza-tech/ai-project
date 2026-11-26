# Proposición 5.1: cadena exacta de la matriz decimal al decaimiento

**Fuente del artículo:** `paper/body_compact_after.tex`, etiqueta `prop:compact_exact_tail_power`, fuente científica congelada `bac3c6255da39cd1169a965df35bb5e9a230e6e8`.

## 1. Matriz, sin redondeo ni sustitución

`code/irf/inputs/rational_preconditioners.json` tiene 36 cadenas decimales para `F0` (6 × 6), SHA-256 `d0cef14050de9f4725e51e5cd28b1ea77e33733dfb2c78d2e38a193200337e94`. Se convierten a `Fraction(Decimal(s))`: ese procedimiento conserva exactamente el número racional representado por cada cadena, incluidos los ceros de notación científica. `lean/current/CurrentCompactBlock48Tail.lean` contiene la misma matriz `exactDecimalF0Rat` como fracciones `numerador/10^decimales`, y `exactDecimalF0` como su imagen real.

El workflow `.github/workflows/ie-prop51-block-tail-lean.yml` verifica programáticamente, elemento por elemento, las **36** fracciones del archivo Lean frente al JSON y el SHA fijado. El verificador rechaza discrepancias: no infiere igualdad solo de una etiqueta o un nombre.

## 2. Evidencia de aritmética exacta (Python)

`code/irf/exact_linear_tail_power_certificate.py` multiplica matrices sobre `fractions.Fraction`, calcula `F0^n` para `0 ≤ n ≤ 48`, utiliza la norma inducida de máximo de sumas absolutas por fila y exige las desigualdades estrictas:

```
||F0^48||_infty < 24/25
max_{0<=r<48} ||F0^r||_infty < 61/10
||F0^7||_infty > 6
```

El último control también exige que el máximo transitorio ocurra en `r=7`. La validación independiente de robustez para `A` próxima a `F0` se trata por separado en el Lema 5.2 y **no** debe confundirse con Prop. 5.1.

La ejecución aprobada reporta los límites superiores (12 decimales, redondeados hacia arriba) **0.955246892194** para `||F0^48||_infty`, **6.097821698407** para el máximo previo a 48, con máximo en `n=7`. También reporta el mayorante robusto `a_48` inferior a **0.972103438403**; ese dato pertenece a la auditoría numérica de Lema 5.2, no a una prueba Lean de su especificación universal. El certificado acepta o rechaza las desigualdades antes de imprimir aproximaciones decimales dirigidas. La salida JSON se genera en `code/irf/output/`; puede estar ignorada por Git, por lo que su ausencia de la rama publicada no equivale a un fallo del verificador. Las Actions guardan el log como artefacto.

## 3. Demostración incondicional en Lean para el F0 decimal fijado

`block48_decay_of_norm_bounds` cuantifica sobre una **matriz real 6×6 arbitraria** `F`, un exponente `k∈ℕ` y cualquier `x∈ℝ^6`. Bajo las dos hipótesis finitas de norma prueba

`||F^k*x||_infty ≤ (61/10)*(24/25)^(k/48)*||x||_infty`.

La derivación usa `k=48m+r` con `0≤r<48`, `F^k=(F^48)^m F^r`, submultiplicatividad de la norma matricial inducida y la desigualdad norma-vector. Aquí `k/48` es división entera, el piso matemático.

La declaración `prop51FiniteBoundSpec` sigue siendo la interfaz de las dos cotas finitas, y `prop51_conditional_exact` es una implicación algebraica genérica. **La nueva prueba ya no da por supuestas esas cotas:** `rationalF0_pow48_row_norm_lt` y `rationalF0_all_transient_rows` demuestran en el kernel, mediante `decide +kernel`, las sumas absolutas por fila de la matriz `exactDecimalF0Rat` para n=48 y **cada** n=0,…,47. `rational_rows_imply_real_operator_norm` utiliza `Matrix.map_pow`, `Rat.cast_abs`, `NNReal.coe_sum` y `Matrix.linfty_opNorm_def` para trasladar esas 49 cotas racionales a la **norma real inducida de máximo de sumas por fila**, sin una premisa numérica externa. `prop51FiniteBound_proved` certifica `prop51FiniteBoundSpec` y `prop51_unconditional_exact` demuestra la conclusión para todo k y x. [Actions #45865176408](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/45865176408) prueba ambas declaraciones, sin `sorryAx` y solo con `[propext, Classical.choice, Quot.sound]`.

## 4. Clasificación y tareas pendientes

- **Aritmética exacta externa:** la fuente y las 48 potencias son comprobables en Python con `Fraction`, sin coma flotante.
- **Lean condicional VERIFICADO:** `block48_decay_of_norm_bounds` y `prop51_conditional_exact` compilaron en Lean 4.30.0-rc2. El registro `#print axioms` para ambos muestra **solo** `[propext, Classical.choice, Quot.sound]`, sin `sorryAx`, [Actions #45861545922](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/45861545922). La primera tentativa (#45861172446) falló por no abrir el ámbito de la notación matricial `*ᵥ`, corregido mediante `open scoped Matrix`; no se alteraron las hipótesis.
- **Aritmética dentro de Lean: DEMOSTRADA.** Las desigualdades finitas se han probado mediante 49 verificaciones racionales (`decide +kernel`) y el puente a la norma real; `prop51FiniteBound_proved` no tiene ninguna hipótesis. Los `#print axioms` de `prop51FiniteBound_proved` y `prop51_unconditional_exact` registraron solo los tres axiomas fundacionales, sin `sorryAx`.
- **Semántica económica pendiente:** ni este resultado ni el del Lema 5.2 establecen que `F0` sea exactamente el Jacobiano de las 34 filas del modelo SOURCE, ni existencia de equilibrio infinito, unicidad, transversalidad o crecimiento de largo plazo.
- **Manuscritos auténticos:** esta guía no sustituye la derivación personal de la Proposición 5.1; el registro de cobertura continúa 0/8 mientras no se adjunten sus hojas.

**Criterio de cierre matemático cumplido:** la Proposición 5.1 está formalizada en Lean para las **36 entradas decimales literales de F0** y para la norma matricial y vectorial reales de su enunciado. **Sigue siendo una prueba del evaluador lineal 6×6**, no una demostración de la correspondencia con el sistema de equilibrio SOURCE, ni una afirmación sobre crecimiento permanente o TVC.

## 5. Registro de errores y pruebas finalizadas

La tentativa [#45863230458](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/45863230458) falló porque `by decide` no reducía suficientemente la aritmética racional; `by decide +kernel` sí verificó las potencias, primero en [#45863623596](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/45863623596) para n=48 y después en [#45864160217](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/45864160217) para todos los n<48. El primer puente a norma real [#45864565016](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/45864565016) falló por ámbito `NNReal`, simplificación de `Rat.norm_cast_real` y normalización de coerciones, corregidos sin cambiar los supuestos. La validación íntegra [#45865176408](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/45865176408) aprobó. La vía intervalar independiente de 49 matrices también pasó pruebas aritméticas en [#45864487315](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/45864487315) y su inducción genérica en [#45864447460](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/45864447460), pero no es necesaria para la prueba directa incorporada a este archivo.
