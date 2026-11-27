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
