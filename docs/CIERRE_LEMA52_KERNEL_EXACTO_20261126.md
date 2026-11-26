# Cierre matemático del Lema 5.2 en Lean: alcance exacto y límites

**Fecha:** 26 de noviembre de 2026.
**Artículo fuente:** `paper/body_compact_after.tex`, `lem:compact_robust_tail_power`, commit científico `bac3c6255da39cd1169a965df35bb5e9a230e6e8`.
**F0 fijada:** `code/irf/inputs/rational_preconditioners.json`, 36 entradas decimales tratadas como racionales exactos, SHA256 `d0cef14050de9f4725e51e5cd28b1ea77e33733dfb2c78d2e38a193200337e94`.
**Herramienta:** Lean 4.30.0-rc2, AppliedModelingLib@194edcc95df74806a39b961d10dedddc6e730cce.

## 1. Proposición matemática literal demostrada

Para toda matriz real `A ∈ ℝ^(6×6)` con `‖A−F0‖∞≤10^-4`, la verdadera norma inducida de suma absoluta máxima por fila satisface:

```
‖A^48‖∞ < 49/50
∀ r∈ℕ, r<48 : ‖A^r‖∞ < 7
∀ k∈ℕ, ∀x∈ℝ^6 :
  ‖A^k*x‖∞ ≤ 7*(49/50)^floor(k/48)*‖x‖∞.
```

La condición sobre A es **la hipótesis explícita del lema**, no un supuesto económico verificado por esta prueba.

## 2. Cadena auditada hasta el kernel

1. **Matemática general.** `CurrentCompactRobustTelescoping.lean` prueba la identidad telescópica no conmutativa y su norma. `CurrentCompactRobustMajorant.lean` prueba la dominación abstracta y el decaimiento geométrico. `CurrentCompactRobustFiniteBridge.lean` demuestra que las cotas hasta n=48 bastan, sin requerir una sucesión numérica infinita.
2. **Normas de fuente.** `CurrentCompactBlock48Tail.lean` expone la matriz racional literal y el puente de sumas racionales por fila a la norma matricial real. `CurrentCompactRobustFiniteCertificate.lean` verifica con `decide +kernel` las 49 potencias (0..48) contra 49 límites estrictos redondeados hacia arriba.
3. **Mayores robustos.** El mismo módulo prueba 48 desigualdades racionales de convolución para la sucesión de 49 majorantes `B_n/10^12`. `B_0=10^12`, `B_48=972103438404`, y `max_{r<48} B_r=6105134003467`, todos expresados en unidades `10^-12`.
4. **Control de procedencia independiente.** `python3 code/irf/check_lean_robust_majorants.py` reconstruye cada uno de los 98 enteros desde los 36 decimales originales mediante `Fraction`, coteja el SHA-256 y rechaza cambios silenciosos.
5. **Teoremas literales.** `lemma52_decimal_finite_norms` cierra las dos desigualdades estrictas para A admisible. `lemma52_decimal_full_uniform_decay` prueba la cota de todo horizonte. `lemma52_decimal_current_exact : lemma52_decimal_current_spec` reúne exactamente esas tres cláusulas.

**Control especializado:** [GitHub Actions #45871289804](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/45871289804). El pipeline verificó los enteros, recompiló las dependencias y registró para los endpoints finales exclusivamente `[propext, Classical.choice, Quot.sound]`, sin `sorryAx`.

## 3. Trazabilidad y errores corregidos

- [#45869124532](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/45869124532): target Lake desconocido; se restauró el `lakefile.toml` y raíz de módulos anclados.
- [#45869458906](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/45869458906): primera validación del certificado racional de 49 pasos.
- [#45869911037](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/45869911037): primer puente rechazado por coerciones `ℚ→ℝ`; no se debilitó ninguna cota.
- [#45870369716](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/45870369716): segunda prueba rechazó la representación de `1/10000`; se acreditó su identidad racional–real explícita.
- [#45870784979](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/45870784979): aprobó el decaimiento universal.
- [#45871289804](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/45871289804): aprobó la especificación completa, con las tres cláusulas.

## 4. Obligaciones ajenas al lema que aún bloquean el cierre del paper

El teorema **no** demuestra que F0 sea el Jacobiano de las 34 condiciones del equilibrio SOURCE en `EconomicModel.lean`, ni que ese Jacobiano esté dentro de la bola `10^-4`. El chequeo de las 16 filas linealizadas a mano y su base racional propia es evidencia distinta, condicionada a su certificado intervalar, y no resuelve automáticamente las 34 filas. Tampoco certifica selección entre ramas S/B, existencia y unicidad del equilibrio infinito, suficiencia dinámica, transversalidad, efectos de bienestar o crecimiento permanente.

**Estado global:** Lema 5.2 DEMOSTRADO sobre la clase de matrices establecida literalmente por el artículo; conexión económica y chequeo oficial `PaperContribution` PENDIENTES. Se mantienen 0/8 manuscritos personales auténticos mientras el autor no adjunte sus páginas.
