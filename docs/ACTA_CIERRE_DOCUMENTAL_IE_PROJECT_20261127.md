# IE project — Acta de cierre de la entrega académica

**Rama evaluable:** [\`main\`](https://github.com/alejandroventuraventurameza-tech/ai-project/tree/main).  
**Cierre de artefactos:** el [PR #75](https://github.com/alejandroventuraventurameza-tech/ai-project/pull/75) integró el original manuscrito y la auditoría en \`main\` mediante el commit \`d0343f496fb0e79b50f5fd194739ef80ac674ab7\`. Esta acta constituye una **adenda documental posterior**, no modifica las conclusiones científicas ni atribuye la recepción de los manuscritos a una fecha anterior a las 22:00 del 26/11/2026, Lima.

## 1. Compuertas de entrega verificadas

| Componente requerido | Evidencia disponible | Cierre documental |
|---|---|---|
| Artículo completo y bibliografía | [PDF](../paper/paper.pdf), [LaTeX](../paper/paper.tex), [BibTeX](../paper/references.bib), apéndice de ocho resultados | Disponible en \`main\`; el artículo identifica sus límites matemáticos |
| Exposición | [Presentación final](../slides/final.pdf), [fuente Beamer](../slides/final.tex), [guía](../slides/GUIA_EXPOSICION_FORMAL.md) | Disponible en \`main\` |
| Código, entradas, figuras, resultados | \`code/\`, \`code/requirements.txt\`, \`code/verify.py\`, \`code/verify_compact_paper.py\` | [Build #45934266889](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/45934266889) aprobado; pruebas solo respecto de los objetos codificados |
| Formalización matemática | \`lean/\`, [matriz paper–Lean](../paper/lean_formalization_matrix_8.md) | Lemas certificados dentro de su especificación; cinco correspondencias literales paper–Lean y la conexión económica SOURCE aún abiertas |
| Ocho pruebas manuscritas | [PDF original de doce páginas](../hand/ai-ieproject.pdf), [registro](../hand/REGISTRO_MANUSCRITOS_RECIBIDOS_20261126.md), [auditoría](../hand/AUDITORIA_ECUACIONES_MANUSCRITAS_8_20261127.md) | 8/8 recibidos y cotejados visualmente; SHA-256 \`14b081edf35c52882bd433021980a8beb12cdf805733aa4b4bca5839d9fcb8a1\` |
| Bibliografía, uso de IA, trazabilidad | \`paper/references.bib\`, [prompts](../prompts.md), [manifiesto de entrega](ENTREGA_ACADEMICA_20261126_ESTADO_Y_LIMITES.md), [mapa de verificación](../paper/verification_map_8.md) | Disponible en \`main\` |

## 2. Controles finales aprobados

- **Reproducción y compilación:** [build #45934266889](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/45934266889) — todos los trabajos completados con éxito: \`code/verify.py\` y compilación de los PDF.
- **Revisión editorial y sintáctica:** [editorial-qa #45934266939](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/45934266939) — éxito en ambas tareas.
- **Handnotes y aritmética exacta:** [auditoría #45934266870](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/45934266870) — éxito en la comprobación del PDF original, sus hashes y los ocho resultados, incluida la reproducción de las cotas del F0 decimal.
- **Integridad del PDF manuscrito:** 3,363,589 bytes; SHA-256 como arriba; Git blob \`7cc7b4378dabda89fd28eb623fa6c034c47a6ef4\`.
- **Fuente científica preservada:** los PDF del artículo, propuesta y presentaciones fueron mantenidos en su versión presentada durante el PR #75; los cambios posteriores son de documentación y custodia, no de resultados económicos.

## 3. Veredicto exacto y exclusiones

**CIERRE DOCUMENTAL: COMPLETO.** Todos los archivos enumerados se encuentran en la rama principal y la auditoría asociada pasó. No faltan pruebas manuscritas originales para los ocho resultados del artículo compacto.

**CIERRE ECONÓMICO–FORMAL INTEGRAL: PENDIENTE.** El proyecto *no* acredita todavía:
1. la regularidad \`C¹\` del operador económico SOURCE completo ni una inversa del Jacobiano 33×33;
2. correspondencia funcional completa SOURCE–Python y equivalencia de los operadores derivados;
3. dos equilibrios competitivos infinitos, criterios de selección S/B, condiciones terminales y TVC;
4. equivalencia literal completa paper–Lean para los cinco resultados que la [matriz de ocho](../paper/lean_formalization_matrix_8.md) aún mantiene abiertos.

El [PR #71](https://github.com/alejandroventuraventurameza-tech/ai-project/pull/71) es un **borrador de investigación** sin certificación especializada, excluido de la rama principal y de la entrega probatoria; no bloquea la integridad documental.

**Nota de plazo:** el enlace público a Google Drive proporcionado por el propietario es un respaldo adicional. El PDF manuscrito fue recibido después de las 22:00 (Lima) del 26/11; consta como adenda sin alterar el sello temporal de la entrega anterior. El estado de envío/recepción por terceros no puede acreditarse solo con el contenido de este repositorio.

**Juicio final:** la entrega académica es reproducible, íntegra en artefactos y explícita respecto de los límites de sus afirmaciones. No se declara completo el proyecto de investigación económica en su sentido más fuerte.


## Adenda formal POSTERIOR al plazo del 26/11/2026, 22:00 Lima

El [PR #77](https://github.com/alejandroventuraventurameza-tech/ai-project/pull/77) incorporó una interfaz paper-facing de **cinco pruebas adicionales** del artículo: Lema A.1.1, Lema A.1.2, Proposición A.1.3, Lema A.1.4 y Proposición 5.3, con un teorema conjunto. El [kernel Lean #46009434502](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/46009434502) aprobó 8,343 trabajos y las seis auditorías de axiomas sin `sorryAx`. La hipótesis adicional de soporte finito en el Lema A.1.2 representa el árbol finito del modelo y **no** generaliza la expectativa a espacios probabilísticos arbitrarios. Las pruebas se registran en [la matriz actualizada](../paper/lean_formalization_matrix_8.md) y en [el cotejo por resultado](ADENDA_POSTPLAZO_CINCO_PRUEBAS_PAPER_20261127.md).

**Se mantiene la separación entre cierre documental y cierre económico integral:** el equilibro dinámico, los puentes completos SOURCE–Python y la identificación de F0 con su Jacobiano no están demostrados. La comprobación formal `python3 scripts/paper_contribution.py check Ventura26LiquidityAllocation --fast` sobre una interfaz generada específica de ocho resultados permanece pendiente; compilar los cinco teoremas no equivale a ejecutar este protocolo. **Esta adenda no modifica los PDF/LaTeX originales ni su fecha de entrega.**


## Adenda técnica posterior — ejecución paper-scoped rápida de los ocho resultados

La [auditoría conjunta #46067342833](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/46067342833) comprobó los ocho resultados (8,357 trabajos Lean). Posteriormente, [Actions #46068856283](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/46068856283) ejecutó con éxito el comando oficial **paper_contribution.py check Ventura26LiquidityAllocation --fast** dentro de un **paquete provisional** con ocho especificaciones y ocho endpoints de prueba, seguido de la auditoría del kernel (8,359 trabajos; solo axiomas fundacionales).

**Alcance estricto:** el paquete se creó con new --no-download y sin el statement-spec oficial anclado a la fuente. Por ello, el resultado no sustituye la auditoría semántica independiente source-to-Spec, el protocolo completo de closeout ni prepare-pr. Tampoco demuestra el puente SOURCE–Python, la identidad de F0 con el Jacobiano económico o un equilibrio dinámico infinito. Se documentan la técnica, evidencia y límites en [ADENDA_FAST_PAPER_SCOPED_8_20261127.md](ADENDA_FAST_PAPER_SCOPED_8_20261127.md). La entrega original y sus archivos científicos permanecen intactos.


## Compilación documental del contrato fuente–Lean (adenda postplazo)

El original PDF del artículo quedó identificado exactamente en `ai-project@bac3c6255da39cd1169a965df35bb5e9a230e6e8` (SHA-256 `923b766624491e7f7b290c4302332140cd5636fe421ab27c7d4024377db7d2e3`). Los ocho enunciados LaTeX se recuperaron de sus Git blobs originales y se generó un `statement-spec` esquema v1 aceptado por el **loader oficial** en [Actions #46070284153](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/46070284153). La adaptación de los dos usos españoles de «todo» al parser upstream está declarada en [ADENDA_EIGHT_STATEMENT_SPEC_SOURCE_LOCK_20261127.md](ADENDA_EIGHT_STATEMENT_SPEC_SOURCE_LOCK_20261127.md) sin modificar el original.

**Delimitación:** se certificaron fuentes, hashes, localizadores y estructura de los ocho contratos, pero no el cotejo semántico independiente source-to-Spec, la ejecución completa de `new --statement-spec` ni el closeout oficial. Esta sección es posterior al corte de entrega y no modifica sus artefactos científicos.
