# Auditoria de precierre — 25 de noviembre de 2026

Estado: candidato de entrega, no fusionado en main.

El plazo oficial del issue #7 es jueves 26 de noviembre de 2026 a las 22:00 (Lima). La rama avanzada parte de c52cabde53e67a6a70500b52318c0f1fe84f42f7; main conserva 5ecf5cd3b497d803ac2db9185cbe4264e45e9fb5.

Los procesos build #44308365992 y editorial-qa #44308365993 finalizaron correctamente en 71bc6a1. El ultimo commit solo sincronizo cuatro PDF compilados. La compilacion informa IE_COMPACT_BODY_PAGES=12, un cuerpo dentro del rango de 8–20, y paper.pdf de 145 paginas con apendices.

El manuscrito mantiene 57 resultados numerados. Segun la matriz conservadora, 24 tienen comparacion semantica dirigida y ninguna equivalencia literal completa paper–Lean esta promovida. Existen pruebas Lean auxiliares verificadas; no se debe inferir de ello que el equilibrio competitivo dinamico infinito este demostrado.

El articulo distingue dos soluciones escalares locales de complementariedad, condicionales a regularidad y signos; el propio abstract advierte una obstruccion SOURCE para recuperar la rama S bajo el mismo estado heredado en la bola auditada. Las IRF S/B son evidencia numerica del evaluador reducido, no dos equilibrios SOURCE certificados ni estimaciones para Peru.

Bloqueos de entrega: (1) apendice manuscrito autentico y veredicto del autor, (2) auditoria final de correspondencia entre paper y Lean, (3) cierre del registro de colaboracion IA, (4) inspeccion visual final de los PDF y bibliografia, (5) fusion de una PR desde la rama avanzada a main y verificacion de sus checks. El PR #2 existente parte de una rama anterior y no debe fusionarse como entrega completa sin conciliar el trabajo posterior.

No declarar el repositorio FINAL hasta cumplir estas condiciones. No se inventan pruebas, notas manuscritas ni verificaciones bibliograficas.


**Hallazgo adicional del 25/11:** al inventario de 57 resultados numerados en `paper/result_ledger.json` deben agregarse 3 proposiciones/lemas del cuerpo de `paper/body_compact_after.tex`; total de **60 resultados** con obligación de cotejo de alcance y manuscrito. Se creó `paper/compact_extra_results_3.json` y una guía de estudio en `hand/GUIA_CUERPO_3_RESULTADOS_20261125.md`. La tabla de formalización del PDF actual enumera solo los 57 originales: falta conciliar la tabla con estos 3 adicionales en una futura compilación, sin inventar cobertura Lean.

**Bibliografía:** se cotejaron metadatos de ocho referencias con fuentes editoriales; véase `docs/COTEJO_BIBLIOGRAFICO_20261125.md`. No se alteró finalmente `paper/references.bib` para preservar su correspondencia con el PDF compilado hasta regenerar ambas piezas de forma coherente.


### Control de integridad LaTeX y referencias (25/11)

Se inspeccionaron conjuntamente `paper/paper.tex`, `paper/body_compact_intro.tex`, `paper/body_compact_after.tex` y `paper/references.bib` en la rama de release. Resultado del análisis estático: **17 claves BibTeX, 17 claves únicas citadas, 0 citas sin entrada, 366 etiquetas, 0 etiquetas duplicadas y 403 referencias cruzadas con 0 destinos ausentes**. Se verificó además que los tres resultados compactos figuran en el archivo de inventario complementario. Este recuento de fuente no sustituye la compilación ni prueba la corrección matemática de las proposiciones.

### Verificaciones y costos de CI

El último conjunto de comprobaciones completo corresponde a #44308365992 y #44308365993 del 18/11; **la rama de release no tiene una ejecución nueva de Actions** porque sus commits documentales contienen `skip ci`. Se evitó disparar indiscriminadamente múltiples workflows Lean pesados en un repositorio cuyo uso previo de minutos se había señalado como costoso. Una ejecución final sobre el SHA definitivo, o una validación oficial de código y PDF equivalente, continúa pendiente antes del merge.


## Segundo corte de control independiente (25/11)

- **PDF de CI:** recuperados los cuatro PDF del artefacto `pdfs` (ID 14429203142). Se inspeccionaron visualmente 4/4 páginas de propuesta, 11/11 diapositivas iniciales, 41/41 finales y una muestra estratificada de 28/145 páginas del paper. Control geométrico del texto aplicado a las 145 páginas: cero spans fuera del rectángulo de página. Informe: [QA visual](QA_VISUAL_PDFS_20261125.md).
- **Identidad binaria:** los SHA de Git blob de los cuatro PDF del ZIP **difieren** de los cuatro objetos PDF incorporados posteriormente al repositorio, pese a tamaños idénticos. No afirmar identidad de bytes ni su causa; verificar las versiones efectivamente entregadas.
- **Tablas:** las 12 cifras de la tabla de impacto coinciden con `delivery_audit.json` al redondear a ocho decimales. Las dos identidades contables de capital de `irf_mechanism_table.tex` también cierran con las cifras publicadas. Véase [QA numérica](QA_NUMERICA_TABLAS_20261125.md).
- **README:** condensado a unas 430 palabras para ajustarse al criterio de una página, con punto decimal y enlaces al material técnico. Las tablas y figuras extensas se mantienen fuera del resumen.
- **Lean:** generado el [índice editorial de 60 resultados](../paper/lean_formalization_matrix_60.md) a partir del crosswalk conservador (57) y los 3 adicionales. **La tabla de 60 aún no está incorporada al PDF:** requiere una compilación final y no acredita ninguna nueva prueba kernel-verified.
- **Bibliografía:** confirmada fuente primaria de la versión de enero de 2026 de González–Nuño–Thaler y autoría del capítulo 3 del libro de Céspedes et al.; la cita de capítulo debe especializarse a Céspedes–Aquije–Sánchez–Vera-Tudela cuando se regenere el paper y su PDF juntos.

**Conclusión de la auditoría:** todavía no puede fusionarse la PR de entrega como cerrada. Faltan manuscritos, tabla Lean integrada al PDF y validación compilada del último SHA. El estudio visual de un artefacto de CI no demuestra ni identidad binaria ni suficiencia económica de un equilibrio dinámico.
