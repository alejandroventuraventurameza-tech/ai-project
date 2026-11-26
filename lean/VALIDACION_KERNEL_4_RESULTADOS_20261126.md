# Cuatro pruebas actuales en Lean: acta reproducible del 26 de noviembre de 2026

**Fuente económica congelada:** `paper/paper.tex` y archivos incluidos, commit `bac3c6255da39cd1169a965df35bb5e9a230e6e8`. **Inventario literal de 8 afirmaciones:** `current_paper_source_inventory_8.json`. **Compilador:** Lean `4.30.0-rc2` (commit `3dc1a088...`); **entorno:** `nikhgarg/AppliedModelingLib@194edcc95df74806a39b961d10dedddc6e730cce`.

## Verificación ejecutada

**[GitHub Actions #45851966286](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/45851966286): success.** Ejecución de `lake env lean` sobre tres archivos que contienen cuatro resultados. El log incluye `SOURCE_LOCK_OK` para los ocho enunciados originales y `LEAN_CHECK_OK` para los cuatro endpoints. Todos los `#print axioms` de estos resultados están libres de `sorryAx`; aparecen únicamente `propext`, `Classical.choice` y `Quot.sound`.

| Enunciado de la versión vigente | Especificación / prueba verificadas | Qué se acredita y qué no |
|---|---|---|
| Lema A.1.1 — Repago robusto | `repaymentCurrentSpec` / `repaymentCurrent_exact` | Cotización real de garantía, no negatividad y positividad condicional del patrimonio, incluyendo `δ=0`; no solvencia bancaria general |
| Lema A.1.2 — Depósito y préstamo interiores | `noSimultaneousInteriorCurrentSpec` / `noSimultaneousInteriorCurrent_exact` | Contradicción explícita entre FOC interiores si `RD<RL`, descuento positivo y dual de garantía no negativo. El sublema `expectedRealMarginal_pos` demuestra positividad de la esperanza bajo probabilidades de **soporte finito**, suma uno y positividad casi segura en estados de peso positivo. **No** demuestra suficiencia KKT ni sustituye la justificación de soporte finito del árbol original |
| Proposición A.1.3 — Máximo capital financiable | `financingCapacityCurrentSpec` / `financingCapacityCurrent_exact` | Cota para cualquier cartera factible, construcción alcanzable y derivada parcial negativa; no predice la elección óptima general |
| Proposición 5.3 — Cuña de precio efectivo H/L | `effectiveWedgeCurrentSpec` / `effectiveWedgeCurrent_exact` | Identidad financiera con `θ_H<θ_L` y `W>0`; no equilibrio ni bienestar |

Las fuentes son, respectivamente, `CurrentCompactWedgeRepayment.lean`, `CurrentCompactInteriorKKT.lean` y `CurrentCompactFinancingCapacity.lean` bajo `lean/candidates/Ventura26LiquidityAllocation/`. No se añadieron axiomas particulares ni hipótesis que presupongan las conclusiones.

## Evidencia histórica adicional que se encontró

**[GitHub Actions #45847597337](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/45847597337): success.** Verificó `PaperLemma43SourceCompleteCandidate.lean`, con once conclusiones integradas del lema de eficiencia y pérdida asignativa. Los axiomas de `sourceLemma43CompleteSpec_proved` son los mismos tres axiomas fundacionales, sin `sorryAx`. Consulte `COTEJO_LEMA_ASIGNACION_A14_20261126.md` para identificar sus coincidencias y las diferencias que siguen abiertas frente a la formulación actual del Lema A.1.4.

## Controles pendientes y clasificación

Las cuatro pruebas actuales son **DEMOSTRADO EN LEAN en el alcance de sus Specs autónomos**. Ello no implica automáticamente que los cuatro resultados del manuscrito sean equivalentes palabra por palabra a las declaraciones; falta la revisión independiente de tipo `source-to-Lean`, la conexión con estructuras de agentes/estados del modelo y la ejecución del empaquetado `paper_contribution.py check Ventura26LiquidityAllocation --fast`.

Los resultados macro de complementariedad (Proposición 3.1), potencia de matriz decimal (Proposición 5.1) y robustez matricial (Lema 5.2) aún carecen de equivalencia fuente–Lean completa; sus simulaciones y certificados racionales conservan categoría NUMÉRICO, no DEMOSTRADO.

**Estado de los manuscritos del autor:** pendiente de adjuntar material auténtico en `hand/`; las guías tipografiadas no satisfacen por sí mismas esa obligación.

El trabajo aquí descrito amplía `lean/` y los workflows, **sin modificar el artículo ni los PDF ya presentados**.
