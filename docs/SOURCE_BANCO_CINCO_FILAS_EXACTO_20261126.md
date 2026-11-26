# SOURCE bancario: identidad exacta de cinco filas y su transformación no lineal

**Corte:** 26 de noviembre de 2026. **Evidencia formal:** [GitHub Actions #45876359130](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/45876359130), 2,276 trabajos Lean; axiomas `[propext, Classical.choice, Quot.sound]`, sin `sorryAx`.

## Sistemas comparados

En una fecha económica de `EconomicModel.lean`, el subvector de residuos SOURCE está formado por las posiciones 6–10 de `localReducedRemainingResidual`: regla de tasa de reservas, regla de cantidad de reservas, precio de préstamos, precio de depósitos y balance bancario. Los bancos SOURCE usan la tasa y la cantidad realizadas. La **targetización SOURCE**, definida en `lean/current/CurrentSourceFiveBankTargetization.lean`, sustituye solo en las tres últimas ecuaciones sus argumentos monetarios realizados por los objetivos de las reglas, manteniendo el resto de la fórmula fuente.

Sea u el residuo de la regla de tasa y v el de la regla de cantidad. Definimos phi(x)=(exp(x)-1)/x si x ≠ 0 y phi(0)=1; Lean demuestra sin aproximación `phi(x)*x=exp(x)-1`. En consecuencia, las tres diferencias de residuos tienen la forma exacta

    loan_target - loan_SOURCE = loanCross * u
    deposit_target - deposit_SOURCE = depositCross * u
    balance_target - balance_SOURCE = balanceRateCross * u + balanceQuantityCross * v

y cada coeficiente es una función literal de `Primitives`, `LocalPrefixDateData`, ratios, pendientes OTC y objetivos monetarios. No se congelan los coeficientes fuera del equilibrio.

## Condiciones explícitas

El resultado supone `P.matchingIntensity=Real.log 2`, `d.controls.tightness ≤ 1`, tasa de reservas realizada positiva, reservas realizadas positivas, razón de reservas/depósitos SOURCE no nula y razón evaluada al objetivo de tasa no nula. Son hipótesis matemáticas, no una certificación de que todos los candidatos numéricos las satisfagan sobre una bola completa.

## Pruebas verificadas

- `expSecant_mul`: identidad no lineal exacta, incluido x=0.
- `fiveBankShear_inverse`: la transformación triangular de cinco residuos es invertible, con inversa explícita.
- `fiveBankShear_zero_iff`: conserva el conjunto de ceros para cualesquiera cuatro coeficientes reales.
- `sourceTargetFiveRows_eq_nonlinearShear`: identifica la transformación con las **cinco fórmulas SOURCE económicas concretas** en una fecha.
- `sourceTargetFiveRows_zero_iff_sourceFiveRows_zero`: equivalencia de ceros económica y exacta para esas cinco ecuaciones bajo las hipótesis anteriores.

CI: [https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/45876359130](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/45876359130), completado correctamente, 2,276 trabajos. `#print axioms` muestra solo `[propext, Classical.choice, Quot.sound]`. El workflow auditó los endpoints y la ausencia de `sorryAx` y errores.

## Frontera pendiente

La demostración se aplica a `LocalPrefixDateData` de cualquier fecha y puede instanciarse por separado para t=0 y t=1, pero **no** demuestra por sí misma la igualdad funcional del vector original completo de 33 filas con `finite_irf.py`. Siguen abiertas la identificación de todas las coordenadas y parámetros, la ley de pagos original, las restantes 23 filas, el transporte del jacobiano económico completo y las cotas de su inversa. Tampoco aporta un nuevo punto de bifurcación con dual financiero igual a cero, una raíz SOURCE validada ni dos equilibrios competitivos dinámicos.

**Distinción de evidencia:** la forma triangular SOURCE-targetizada y su equivalencia de ceros están **DEMOSTRADAS**; la correspondencia literal de 33 filas SOURCE/Python, la identificación numérica y la interpretación de equilibrio completo permanecen **PENDIENTES**.