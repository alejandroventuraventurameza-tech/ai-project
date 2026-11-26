# Auditoría del Lema 5.2: paso telescópico, no certificado robusto completo

**Enunciado de origen:** `paper/body_compact_after.tex`, `lem:compact_robust_tail_power`. Fuente científica congelada `bac3c6255da39cd1169a965df35bb5e9a230e6e8`. **Archivo Lean:** `lean/current/CurrentCompactRobustTelescoping.lean`. Motor fijado Lean 4.30.0-rc2 / AppliedModelingLib@194edcc95df74806a39b961d10dedddc6e730cce.

## Resultado demostrado en Lean

Para matrices reales arbitrarias `A,F ∈ R^(6×6)`, **sin conmutatividad**, `matrix_pow_difference_telescoping` prueba

`A^n−F^n = Σ_(j=0)^(n−1) F^j (A−F) A^(n−1−j)`.

La forma del artículo usa `F^(n−1−j)(A−F)A^j` y es la misma suma bajo el cambio de índice `j↦n−1−j`. La prueba no identifica una matriz financiera específica ni una dinámica de equilibrio.

El segundo resultado, `matrix_power_norm_telescoping`, deduce con la **norma inducida de máximo de sumas por fila**,

`‖A^n‖∞ ≤ ‖F^n‖∞ + Σ_(j=0)^(n−1) ‖F^j‖∞ · ‖A−F‖∞ · ‖A^(n−1−j)‖∞`.

**Compilación kernel [Actions #45864283745](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/45864283745):** ambos `#print axioms` registran solo `[propext, Classical.choice, Quot.sound]`, sin `sorryAx`. El pipeline general `build` y `editorial-qa` también aprobó para el archivo Lean en la rama antes de la actualización documental.

## Obligaciones no demostradas

1. Formular dentro de Lean la secuencia real de mayorantes `a_0=1`, `a_n=‖F0^n‖∞ + 10^(−4) Σ_{j<n} ‖F0^(n−1−j)‖∞ a_j`, demostrar inductivamente `‖A^n‖∞≤a_n` para toda `A` con `‖A−F0‖∞≤10^(−4)`.
2. Formalizar las desigualdades finitas `a_48<49/50` y `max_{0≤r<48}a_r<7`. `code/irf/exact_linear_tail_power_certificate.py` las verifica con fracciones exactas en **Python**, pero no constituye un teorema kernel de Lean.
3. Aplicar el argumento por bloques a `A`, para todo exponente y vector.
4. Mantener separada la matriz decimal `F0` del Jacobiano completo de las 34 filas de `EconomicModel.lean`: esa identificación económica permanece abierta.

**Clasificación:** DEMOSTRADO el telescopado general y su norma; NUMÉRICO las cotas finitas externas; PENDIENTE la implicación uniforme de robustez y la correspondencia source-to-Lean. No declarar completo el Lema 5.2.

## Trazabilidad de errores

El primer intento [#45863570793](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/45863570793) falló al reindexar la suma. El segundo [#45863966255](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/45863966255) detectó una resta de exponentes simplificada y una inversión en el orden de la suma de normas. Ambos errores fueron corregidos sin postular conclusiones ni modificar hipótesis; el tercero [#45864283745](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/45864283745) pasó el kernel.
