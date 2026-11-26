# Cierre formal de la Proposición 5.1 para la matriz decimal F0

**Fecha:** 26 de noviembre de 2026. **Enunciado:** `prop:compact_exact_tail_power`, `paper/body_compact_after.tex`. **Fuente del artículo:** `ai-project@bac3c6255da39cd1169a965df35bb5e9a230e6e8`. **Compilador:** Lean 4.30.0-rc2 y AppliedModelingLib@194edcc95df74806a39b961d10dedddc6e730cce.

## Evidencia trazable

1. `code/irf/inputs/rational_preconditioners.json` almacena 36 decimales que son interpretados como racionales exactos. SHA-256: `d0cef14050de9f4725e51e5cd28b1ea77e33733dfb2c78d2e38a193200337e94`. El workflow verifica correspondencia literal celda por celda, no por nombre.
2. `rationalF0_pow48_row_norm_lt` prueba para cada fila i que `sum_j abs((F0^48)ij)<24/25`, usando `decide +kernel` sobre racionales. Compilación independiente [#45863623596](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/45863623596).
3. `rationalF0_all_transient_rows` prueba `sum_j abs((F0^r)ij)<61/10` para **todas** las filas i y todas las potencias r=0,…,47. Compilación independiente [#45864160217](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/45864160217).
4. `rational_rows_imply_real_operator_norm` formaliza `(F0_ℚ^n)` trasladado a `F0_ℝ^n` por homomorfismo, conservación de suma/valor absoluto y equivalencia con la norma real inducida de máximo de sumas por fila.
5. `prop51FiniteBound_proved : prop51FiniteBoundSpec` prueba ambas desigualdades de norma **sin premisas**.
6. `prop51_unconditional_exact` combina las cotas con `block48_decay_of_norm_bounds`, cuantificando **sobre todos** los exponentes naturales k y vectores reales x. Prueba conjunta en [Actions #45865176408](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/45865176408), `#print axioms` registra solo `[propext, Classical.choice, Quot.sound]`, sin `sorryAx`.

El resultado declarado es exactamente:
```
||F0^k x||_infinity <= (61/10) * (24/25)^(floor(k/48)) * ||x||_infinity,
for all k >= 0, all x in R^6.
```
Conexión económica: *solo* matriz decimal 6×6 del grafo lineal fijado; no demuestra igualdad con el Jacobiano completo SOURCE (34 filas), existencia de una variedad invariante ni equilibrio competitivo infinito.

## Independencia y control de regresiones

El certificado previo en Python `code/irf/exact_linear_tail_power_certificate.py` permanece como comprobación independiente de fracciones exactas. La integración en `main` conserva los tests de código, construcción LaTeX, cuatro PDF y `editorial-qa`.

**Obligaciones abiertas:** Proposición 3.1 (puente implícito local), Lema 5.2 (mayorantes numéricos robustos completos), correspondencia paper-scoped oficial, `PaperInterface`, fuente SOURCE y ocho manuscritos auténticos (0/8).
