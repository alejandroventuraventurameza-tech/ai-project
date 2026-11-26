# Auditoría del Lema 5.2: paso telescópico, no certificado robusto completo

**Enunciado de origen:** `paper/body_compact_after.tex`, `lem:compact_robust_tail_power`. Fuente científica congelada `bac3c6255da39cd1169a965df35bb5e9a230e6e8`. **Archivo Lean:** `lean/current/CurrentCompactRobustTelescoping.lean`. Motor fijado Lean 4.30.0-rc2 / AppliedModelingLib@194edcc95df74806a39b961d10dedddc6e730cce.

## Resultado demostrado en Lean

Para matrices reales arbitrarias `A,F ∈ R^(6×6)`, **sin conmutatividad**, `matrix_pow_difference_telescoping` prueba

`A^n−F^n = Σ_(j=0)^(n−1) F^j (A−F) A^(n−1−j)`.

La forma del artículo usa `F^(n−1−j)(A−F)A^j` y es la misma suma bajo el cambio de índice `j↦n−1−j`. La prueba no identifica una matriz financiera específica ni una dinámica de equilibrio.

El segundo resultado, `matrix_power_norm_telescoping`, deduce con la **norma inducida de máximo de sumas por fila**,

`‖A^n‖∞ ≤ ‖F^n‖∞ + Σ_(j=0)^(n−1) ‖F^j‖∞ · ‖A−F‖∞ · ‖A^(n−1−j)‖∞`.

**Compilación kernel [Actions #45864283745](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/45864283745):** ambos `#print axioms` registran solo `[propext, Classical.choice, Quot.sound]`, sin `sorryAx`. El pipeline general `build` y `editorial-qa` también aprobó para el archivo Lean en la rama antes de la actualización documental.

## Progreso adicional: dominación de mayorantes y decaimiento condicional

El módulo `lean/current/CurrentCompactRobustMajorant.lean` añade tres pruebas verificadas en [Actions #45866200744](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/45866200744):

- `matrix_robust_majorant_induction`: si `δ≥0`, `‖A−F‖∞≤δ`, `a_0≥1`, y `a_n≥‖F^n‖∞ + δΣ_{j<n}‖F^j‖∞a_{n−1−j}`, entonces `‖A^n‖∞≤a_n` para **todo n**.
- `matrix_robust_block48_decay_of_norm_bounds`: si una matriz tiene normas `‖A^48‖∞<49/50` y `‖A^r‖∞<7` para `r<48`, obtiene la cota geométrica universal de todo `A^k x`.
- `lemma52_conditional_uniform_decay`: enlaza ambas pruebas y concluye la cota para **todas** las matrices `A` que satisfagan `‖A−F‖∞≤1/10000` bajo las dos cotas **aún supuestas** de la sucesión `a_n`. No presume conmutatividad ni un efecto monetario causal.

Los tres `#print axioms` muestran `[propext, Classical.choice, Quot.sound]`, sin `sorryAx`. Su carácter condicional no se disimula bajo un nombre de teorema.

## Obligaciones no demostradas

1. Construir dentro de Lean **la sucesión numérica literal de mayorantes para F0**, con definición verificable de `a_0=1` y la recurrencia. Su dominación general ya está demostrada; falta acreditar que el objeto concreto satisface las hipótesis del endpoint.
2. Formalizar en el kernel las desigualdades finitas de esa sucesión, `a_48<49/50` y `max_{0≤r<48}a_r<7`, que `code/irf/exact_linear_tail_power_certificate.py` acredita mediante fracciones exactas **fuera de Lean**.
3. Conectar la matriz decimal 6×6 con el Jacobiano de 34 filas del modelo `EconomicModel.lean`, si es matemáticamente procedente. Esa identidad no está demostrada.

**Clasificación:** DEMOSTRADA en Lean la cadena telescópica, la dominación universal de mayorantes y el resultado de bloques **condicional a desigualdades finitas**; NUMÉRICO el certificado externo del mayorante de F0; PENDIENTE la instancia literal y la correspondencia SOURCE. No declarar completo el Lema 5.2.

## Trazabilidad de errores

El primer intento [#45863570793](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/45863570793) falló al reindexar la suma. El segundo [#45863966255](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/45863966255) detectó una resta de exponentes simplificada y una inversión en el orden de la suma de normas. Ambos errores fueron corregidos sin postular conclusiones ni modificar hipótesis; el tercero [#45864283745](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/45864283745) pasó el kernel.
