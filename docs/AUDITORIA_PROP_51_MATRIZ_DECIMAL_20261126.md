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

## 3. Demostración universal condicionada en Lean

`block48_decay_of_norm_bounds` cuantifica sobre una **matriz real 6×6 arbitraria** `F`, un exponente `k∈ℕ` y cualquier `x∈ℝ^6`. Bajo las dos hipótesis finitas de norma prueba

`||F^k*x||_infty ≤ (61/10)*(24/25)^(k/48)*||x||_infty`.

La derivación usa `k=48m+r` con `0≤r<48`, `F^k=(F^48)^m F^r`, submultiplicatividad de la norma matricial inducida y la desigualdad norma-vector. Aquí `k/48` es división entera, el piso matemático.

`prop51FiniteBoundSpec` representa las dos hipótesis para la matriz literal `exactDecimalF0`. El endpoint `prop51_conditional_exact` deduce la conclusión **a partir de** `prop51FiniteBoundSpec`; no demuestra ese predicado. Esta separación es deliberada y evita sustituir un cálculo externo por una prueba kernel inexistente.

## 4. Clasificación y tareas pendientes

- **Aritmética exacta externa:** la fuente y las 48 potencias son comprobables en Python con `Fraction`, sin coma flotante.
- **Lean condicional VERIFICADO:** `block48_decay_of_norm_bounds` y `prop51_conditional_exact` compilaron en Lean 4.30.0-rc2. El registro `#print axioms` para ambos muestra **solo** `[propext, Classical.choice, Quot.sound]`, sin `sorryAx`, [Actions #45861545922](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/45861545922). La primera tentativa (#45861172446) falló por no abrir el ámbito de la notación matricial `*ᵥ`, corregido mediante `open scoped Matrix`; no se alteraron las hipótesis.
- **Aritmética dentro de Lean pendiente:** demostrar las dos desigualdades finitas para `exactDecimalF0` en el kernel, o incorporar un certificado racional elaborado con pruebas comprobables por el kernel. Los controles actuales no cumplen esa obligación.
- **Semántica económica pendiente:** ni este resultado ni el del Lema 5.2 establecen que `F0` sea exactamente el Jacobiano de las 34 filas del modelo SOURCE, ni existencia de equilibrio infinito, unicidad, transversalidad o crecimiento de largo plazo.
- **Manuscritos auténticos:** esta guía no sustituye la derivación personal de la Proposición 5.1; el registro de cobertura continúa 0/8 mientras no se adjunten sus hojas.

**Criterio de cierre literal:** la Proposición 5.1 no debe marcarse como plenamente formalizada en Lean hasta que ambas desigualdades numéricas, además del teorema universal, estén efectivamente demostradas para la matriz fijada.
