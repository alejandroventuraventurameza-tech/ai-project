# Adenda técnica del 28 de noviembre de 2026 — paquete oficial de ocho resultados

**Naturaleza y fecha.** Evidencia creada el **28/11/2026**, posterior a la entrega académica del 26/11/2026. No modifica `paper/paper.pdf`, el manuscrito, las diapositivas ni los manuscritos de iPad; no sustituye ni refecha aquella entrega.

## Objeto auditable

Artículo compacto de ocho proposiciones y lemas, identificado mediante los ocho enunciados LaTeX de `lean/current_paper_source_inventory_8.json`, congelados en `ai-project@bac3c6255da39cd1169a965df35bb5e9a230e6e8`. PDF original SHA-256: `923b766624491e7f7b290c4302332140cd5636fe421ab27c7d4024377db7d2e3` (519.368 bytes).

Upstream: `nikhgarg/AppliedModelingLib@194edcc95df74806a39b961d10dedddc6e730cce`; Lean `v4.30.0-rc2`. Carpeta temporal de contribución nueva: `papers/Ventura26LiquidityAllocationEight`. El contenido se genera **en cada ejecución de GitHub Actions**; la prueba no supone que se haya fusionado una contribución en el repositorio upstream.

## Comp puertas ejecutadas y evidencia

La [ejecución reproducible #46173145169](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/46173145169) concluyó **success** el 28/11/2026:

1. Se recuperó el PDF del commit original, comprobando **Git blob, longitud y SHA-256**, y los ocho enunciados LaTeX.
2. Se ejecutó `python3 scripts/paper_contribution.py new ... --statement-spec ... --no-download` sobre un **destino nuevo**, con el cargador y el generador propios de AppliedModelingLib.
3. Se preservó `PaperInterface.lean` **generado oficialmente**; se sustituyeron los ocho borradores `by sorry` de `ProofInterface.lean` por las ocho pruebas ya demostradas en Lean.
4. Se calculó la clausura transitiva de los cuatro módulos probatorios de entrada. Se copiaron **44 archivos Lean**, modificando exclusivamente **46 rutas de importación**, y se verificó que deshacer esos cambios reconstruye exactamente los textos fuente. Después de la generación, se restauró el `AppliedModelingLib.lean` original del checkout.
5. La compilación `lake build Ventura26LiquidityAllocationEight.ProofInterface` y la auditoría de axiomas aprobaron: **8.360 trabajos Lean** en la compilación principal, sin `sorryAx` en los ocho endpoints.
6. Finalmente aprobó `python3 scripts/paper_contribution.py check Ventura26LiquidityAllocationEight --fast`, incluida la **regla de no depender transitivamente de otros objetivos paper**.

También aprobaron los controles generales de la rama sobre el commit `4a3baff986e79ccd90d946f58ce47ed94b16d9eb`: [build #46173145228](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/46173145228) y [editorial-qa #46173145183](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/46173145183). Los logs, `statement-spec`, mapa fuente y `PaperInterface` se conservaron como artefactos del workflow.

## Distinción entre contrato explícito y versión de compatibilidad

El archivo `statement-spec-8.json` se conserva con los **tipos matemáticos fuente explícitos**. La versión separada `statement-spec-8-official-compat.json` se utiliza **solo** para sortear limitaciones de elaboración del generador upstream, que al validar fragmentos aislados no abre el scope de norma matricial o multiplicación matriz-vector y no resuelve automáticamente un universo polimórfico.

Esta versión de compatibilidad utiliza **exactamente tres referencias a definiciones transparentes ya probadas**:

| Resultado | Definición usada para la elaboración del generador | Precaución |
|---|---|---|
| Proposición 5.1 | `CurrentPaperSource.prop51AllSourceClauses` | Contiene sus tres afirmaciones, pero el closeout requiere expandir y cotejar el término |
| Lema 5.2 | `CurrentCompact.lemma52_decimal_current_spec` | Cota de matrices 6×6 condicionada a la bola fija; no implica Jacobiano SOURCE |
| Lema A.1.2 | `CurrentCompact.noSimultaneousInteriorCurrentSpec.{0}` | Especializa el universo; mantiene una **esperanza de soporte finito** |

La sustitución declarada de dos apariciones del cuantificador español «todo» por «cada» en el campo usado por el parser de la Proposición 5.1 está documentada en [la adenda de fuente congelada](ADENDA_EIGHT_STATEMENT_SPEC_SOURCE_LOCK_20261127.md); la cita original y su hash permanecen intactos en la procedencia. **Ni esta sustitución ni los tres alias constituyen evidencia de equivalencia semántica independiente.**

## Interpretación y obligaciones que permanecen abiertas

**Aprobado:** origen binario del documento, esquema v1 de ocho enunciados, ejecución de `new --statement-spec` con adaptación declarada, ocho teoremas kernel-checked, paquetes Lean con importaciones aisladas y `check --fast`.

**Pendiente:** cribado independiente v11 de átomos fuente frente a `Spec` transparentes *expandidos*, cierre recursivo de premisas, evidencias source-to-library, revisión y aprobación humana de la fidelidad, y `prepare-pr`/closeout formal completo. El mapa generado por `new` conserva la marca `source_curated=false` y **no** autoriza afirmar certificación semántica integral.

**Brechas económicas ajenas a esta compuerta:** recuperación efectiva del sistema SOURCE 33×33 y de las ramas económicas en la Proposición 3.1; identidad de la matriz racional fija F0 con el Jacobiano del modelo; equivalencia funcional del evaluador Python y el sistema SOURCE; existencia de equilibrio infinito y condiciones terminales; extensión de A.1.2 desde soporte finito hacia espacios de probabilidad generales.

La certificación lograda es **técnica, reproducible y acotada**. No es una validación del modelo de equilibrio completo ni una rectificación de la entrega anterior.
