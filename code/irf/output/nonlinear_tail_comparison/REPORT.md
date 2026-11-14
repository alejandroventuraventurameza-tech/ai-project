# Comparación de la continuación no lineal

Finite deterministic reduced paths with nonlinear rows through T-1 and an explicit boundary at T; no exact infinite-path or bank-optimality claim.

Todas las tasas, preferencias, tecnologías, posiciones heredadas y anuncios del prefijo se mantienen.
La condición terminal se declara y se varía. Una solución finita no certifica existencia, unicidad o determinación infinitas.

| Rama | T | Cierre | Output inicial (log %) | Diferencia frente a IRF original | Residuo máximo | Fallos de margen |
|---|---:|---|---:|---:|---:|---|
| slack | 20 | linear_graph | -3.559194696e-05 | 2.056e-07 | 3.61e-14 | {} |
| binding | 20 | linear_graph | -0.004142226408 | 3.246e-07 | 3.66e-14 | {} |
| slack | 40 | linear_graph | -3.559161617e-05 | 2.06e-07 | 2.99e-14 | {} |
| binding | 40 | linear_graph | -0.004142220888 | 3.301e-07 | 4.52e-14 | {} |
| slack | 80 | linear_graph | -3.559160404e-05 | 2.06e-07 | 3.66e-14 | {} |
| binding | 80 | linear_graph | -0.004142220871 | 3.301e-07 | 3.74e-14 | {} |
| slack | 160 | linear_graph | -3.559160233e-05 | 2.06e-07 | 3.4e-14 | {} |
| binding | 160 | linear_graph | -0.004142220871 | 3.301e-07 | 5.29e-14 | {} |
| slack | 320 | linear_graph | -3.559159897e-05 | 2.06e-07 | 2.91e-14 | {} |
| binding | 320 | linear_graph | -0.004142220873 | 3.301e-07 | 4.56e-14 | {} |
| slack | 640 | linear_graph | -3.559159239e-05 | 2.06e-07 | 4.66e-14 | {} |
| binding | 640 | linear_graph | -0.004142220876 | 3.301e-07 | 4.51e-14 | {} |
| slack | 80 | zero_controls | -0.001204449893 | -0.001169 | 5.84e-14 | {} |
| binding | 80 | zero_controls | -0.003685700419 | 0.0004569 | 3.2e-14 | {} |
| slack | 160 | zero_controls | -0.0001438710543 | -0.0001081 | 4.05e-14 | {} |
| binding | 160 | zero_controls | -0.004101744236 | 4.081e-05 | 4.56e-14 | {} |
| slack | 320 | zero_controls | -4.881879864e-05 | -1.302e-05 | 4.69e-14 | {} |
| binding | 320 | zero_controls | -0.004137335856 | 5.215e-06 | 4.97e-14 | {} |
| slack | 640 | zero_controls | -3.567631947e-05 | 1.213e-07 | 4.11e-14 | {} |
| binding | 640 | zero_controls | -0.004142189601 | 3.614e-07 | 4.67e-14 | {} |

## Lectura y límites
La comparación reemplaza la propagación lineal por ecuaciones no lineales en todos los períodos interiores, resolviendo el prefijo y la cola conjuntamente.
Reutiliza los residuos económicos existentes: no es una implementación independiente de todo el DSGE ni una prueba de suficiencia de sus condiciones marginales.
El cierre `zero_controls` es una condición terminal alternativa, no una afirmación de que los controles económicos deban ser cero: sus desviaciones logarítmicas terminales son cero.
Examinar convergencia entre horizontes y cierres, márgenes y signos antes de interpretar el resultado.

Reproducción: `python code/irf/compare_nonlinear_tail.py`. No sobrescribe las IRF principales.
