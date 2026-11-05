# Comparación de la continuación no lineal

Finite deterministic reduced paths with nonlinear rows through T-1 and an explicit boundary at T; no exact infinite-path or bank-optimality claim.

Todas las tasas, preferencias, tecnologías, posiciones heredadas y anuncios del prefijo se mantienen.
La condición terminal se declara y se varía. Una solución finita no certifica existencia, unicidad o determinación infinitas.

| Rama | T | Cierre | Output inicial (log %) | Diferencia frente a IRF original | Residuo máximo | Fallos de margen |
|---|---:|---|---:|---:|---:|---|
| slack | 6 | linear_graph | -3.559970288e-05 | 1.979e-07 | 3.12e-14 | {} |
| binding | 6 | linear_graph | -0.004142378938 | 1.721e-07 | 4.49e-14 | {} |
| slack | 12 | linear_graph | -3.559627178e-05 | 2.013e-07 | 5.53e-14 | {} |
| binding | 12 | linear_graph | -0.004142246505 | 3.045e-07 | 3.67e-14 | {} |
| slack | 6 | zero_controls | -0.0009651662195 | -0.0009294 | 4.53e-14 | {} |
| binding | 6 | zero_controls | -0.004221650844 | -7.91e-05 | 2.02e-14 | {} |
| slack | 12 | zero_controls | -0.006561891498 | -0.006526 | 2.83e-14 | {'date0_L_slack': -1.5076701527672043e-05} |
| binding | 12 | zero_controls | -0.001425919065 | 0.002717 | 4.52e-14 | {'date0_L_dual': -5.605642496908647e-05} |

## Lectura y límites
La comparación reemplaza la propagación lineal por ecuaciones no lineales en todos los períodos interiores, resolviendo el prefijo y la cola conjuntamente.
Reutiliza los residuos económicos existentes: no es una implementación independiente de todo el DSGE ni una prueba de suficiencia de sus condiciones marginales.
El cierre `zero_controls` es una condición terminal alternativa, no una afirmación de que los controles económicos deban ser cero: sus desviaciones logarítmicas terminales son cero.
Examinar convergencia entre horizontes y cierres, márgenes y signos antes de interpretar el resultado.

Reproducción: `python code/irf/compare_nonlinear_tail.py`. No sobrescribe las IRF principales.
