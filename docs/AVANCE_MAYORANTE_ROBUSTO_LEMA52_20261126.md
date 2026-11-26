# Lema 5.2 — inducción de mayorantes y decaimiento condicional

**Fecha:** 26/11/2026. **Fuente científica:** `ai-project@bac3c6255da39cd1169a965df35bb5e9a230e6e8`, etiqueta `lem:compact_robust_tail_power`. **Lean:** 4.30.0-rc2; **AppliedModelingLib:** `194edcc95df74806a39b961d10dedddc6e730cce`.

## Pruebas comprobadas

`CurrentCompactRobustTelescoping.lean` demuestra, para todas las matrices reales 6×6 `A,F` sin necesidad de conmutatividad,

```
A^n - F^n = ∑_{j<n} F^j (A−F) A^(n−1−j)
‖A^n‖∞ ≤ ‖F^n‖∞ + ∑_{j<n} ‖F^j‖∞ ‖A−F‖∞ ‖A^(n−1−j)‖∞
```
Kernel [#45864283745](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/45864283745), sin `sorryAx`.

`CurrentCompactRobustMajorant.lean` demuestra:

1. **Inducción:** para `δ≥0`, `‖A−F‖∞≤δ` y cualquier `a:ℕ→ℝ` con `a0≥1` y `a_n ≥ ‖F^n‖∞+δ∑_{j<n}‖F^j‖∞a_{n−1−j}`, se tiene `‖A^n‖∞≤a_n` para todo `n`.
2. **Bloques robustos:** si `‖A^48‖∞<49/50` y `max_{r<48}‖A^r‖∞<7`, entonces `‖A^k x‖∞≤7(49/50)^{floor(k/48)}‖x‖∞`.
3. **Endpoint conjunto:** `lemma52_conditional_uniform_decay` aplica 1 y 2 a toda `A` con `‖A−F‖∞≤10^-4`, **bajo los dos límites finitos explícitos** de `a`.

Los tres teoremas compilaron en [#45866200744](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/45866200744), 8,314 trabajos, `#print axioms` = `[propext, Classical.choice, Quot.sound]`, sin `sorryAx`.

## Diferenciar la hipótesis y su certificación

El paper requiere una **sucesión específica** con `F=F0` y `δ=10^-4`. El código [`code/irf/exact_linear_tail_power_certificate.py`](../code/irf/exact_linear_tail_power_certificate.py) ya calcula exactamente en Python `a48≈0.972103438402<49/50` y el máximo de las potencias 0–47 del mayorante, inferior a 7, pero ese certificado **no ha sido convertido en un teorema Lean**. Actualmente no se ha cerrado la versión íntegra source-specific del Lema 5.2.

Tampoco se ha demostrado que `F0` sea el Jacobiano de las 34 filas SOURCE ni que el cierre terminal de las IRF certifique una continuación económica infinita. La norma es **del grafo lineal decimal**, no una prueba de estabilidad DSGE global.

**Siguiente compuerta:** crear un certificado finito de la recurrencia en Lean para n=0,…,48; demostrar los umbrales y alimentar `lemma52_conditional_uniform_decay` sin hipótesis de mayorante adicionales. Mantener `PaperInterface` y los manuscritos auténticos (0/8) como pendientes separados.
