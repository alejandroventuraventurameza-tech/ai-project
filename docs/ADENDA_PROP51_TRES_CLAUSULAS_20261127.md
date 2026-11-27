# Adenda posterior al plazo — Proposición 5.1 y sus tres cláusulas originales

**Fecha de esta corrección:** 27/11/2026, después del cierre de entrega del 26/11/2026 (22:00, Lima). Esta adenda no modifica retroactivamente el artículo entregado, ni su PDF ni los handnotes.

## Hallazgo de auditoría fuente–Lean

El enunciado original de la Proposición 5.1 en `paper/body_compact_after.tex`, Git revision `bac3c6255da39cd1169a965df35bb5e9a230e6e8`, contiene **tres afirmaciones**:

1. `‖F0 ^ 48‖ < 24 / 25`, en la norma matricial inducida infinito.
2. Para **todo** entero `0 ≤ r < 48`: `‖F0 ^ r‖ < 61 / 10`, equivalente a la cota estricta del máximo entre esos 48 exponentes.
3. Para **todo** `k : ℕ` y `x : Fin 6 → ℝ`: `‖(F0 ^ k) *ᵥ x‖ ≤ (61 / 10) * (24 / 25) ^ (k / 48) * ‖x‖`.

La interfaz provisional `scripts/stage_eight_paper_interface.py` exponía **solo el punto 3** como `p51Spec`. Los puntos 1 y 2 estaban previamente **demostrados** en el módulo `CurrentCompactBlock48Tail.lean` mediante `prop51FiniteBound_proved`, y no eran hipótesis pendientes; pero aún no figuraban como cláusulas visibles de la especificación paper-facing. Esta era una brecha de **integridad del tipo formalizado**, no una ausencia de certificado matemático.

## Reparación certificada

El módulo `lean/candidates/Ventura26LiquidityAllocation/CurrentPaperSourceCompleteProp51.lean` introduce la especificación `CurrentPaperSource.prop51AllSourceClauses` con las tres conclusiones conjuntas y su demostración `prop51AllSourceClauses_proved`. La prueba utiliza `CurrentCompact.prop51FiniteBound_proved.1`, `.2` y `CurrentCompact.prop51_unconditional_exact`; no añade hipótesis, axiomas, aproximaciones de punto flotante ni cambios en los 36 coeficientes racionales de la matriz. 

La interfaz provisional `p51Spec`, su endpoint `p51` y el generador `scripts/build_eight_statement_spec.py` ahora exponen las tres afirmaciones; el resto de las siete especificaciones se conserva.

## Evidencia verificable

- [GitHub Actions #46072883272](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/46072883272) — **success**; prueba estructural de las tres cláusulas en `statement-spec`, carga de los ocho enunciados originales, verificación oficial rápida, certificado del kernel para el teorema conjunto y los ocho endpoints. La compilación final reporta **8,360 trabajos Lean**.
- La auditoría de `#print axioms` del nuevo teorema y de los ocho endpoints no contiene `sorryAx`, `admit`, metas pendientes ni axiomas nuevos.
- Todos los módulos se ejecutaron en el upstream fijo de AppliedModelingLib `194edcc95df74806a39b961d10dedddc6e730cce` con Lean `v4.30.0-rc2`.
- Los logs completos y el `statement-spec-8.json` regenerado están preservados como artefactos de la ejecución.

## Límites sin cambios

**Demostrado en Lean:** exactamente los dos límites de normas y la desigualdad de decaimiento para la matriz racional decimal fija `F0` y su interpretación en `ℝ^{6×6}`.

**No demostrado por este cambio:** que `F0` sea el Jacobiano del sistema de equilibrio SOURCE 33×33, que el evaluador Python sea funcionalmente equivalente al modelo SOURCE, o que un equilibrio dinámico infinito exista y cumpla condiciones terminales. El chequeo `--fast` y el loader oficial del `statement-spec` continúan siendo controles distintos de la auditoría semántica independiente y del closeout completo upstream.

Este hallazgo ilustra por qué **la coincidencia de nombres no sustituye la comparación cláusula por cláusula con el artículo original**.
