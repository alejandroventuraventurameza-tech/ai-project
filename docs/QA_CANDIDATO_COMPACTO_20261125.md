# QA del candidato de ocho resultados — 25/11/2026

**Rama:** `work/ie-paper-eight-results-candidate-20261125`. **Archivo científico histórico:** `archive/ie-paper-full-20261118` (commit `c52cabde53e67a6a70500b52318c0f1fe84f42f7`). **Estado:** candidato de fuente; **no hay PDF nuevo compilado**, y la rama principal sigue con la versión extensa.

## Cambios efectivos

1. `paper/paper.tex` ahora incluye el cuerpo compacto existente y llama a `paper/appendix_eight_results.tex` tras la bibliografía; la versión extensa se preserva en una rama de archivo, sin borrarla.
2. `paper/body_compact_after.tex` ya no afirma que el dossier completo figure dentro del PDF compacto: remite a la rama histórica.
3. El apéndice nuevo contiene cuatro resultados autocontenidos —repago, ahorro/endeudamiento, capacidad financiable y pérdida asignativa— además de una matriz conservadora de ocho resultados, registro de IA y protocolo de reproducción.
4. `paper/lean_formalization_matrix_8.md` y `hand/CONTROL_COBERTURA_MANUSCRITA_8.md` mapean el alcance evaluable. **0 de 8** manuscritos recibidos; ninguna equivalencia literal completa promovida para el artículo compacto.

## Comprobación estática reproducida sobre la fuente

- **8** entornos de `proposition`/`lemma`; **8** pruebas `proof`.
- **39** etiquetas, **0** duplicadas.
- **11** referencias cruzadas, **0** destinos inexistentes.
- **5** claves bibliográficas únicas citadas, **0** claves ausentes de las 17 entradas de `references.bib`.
- Anidamiento `begin/end` y balance de llaves: **sin errores**.
- Referencias a recursos existentes en el repositorio: `body_compact_intro.tex`, `body_compact_after.tex`, `appendix_eight_results.tex`, tablas `irf_impact_table.tex` y `irf_mechanism_table.tex`, figuras `figures/irf_transmission.pdf` y `figures/irf_real_allocation.pdf`.
- Se hizo una **compilación local aislada** con pdflatex de las estructuras matemáticas principales (repago, capacidad de crédito y MPK) en un documento de prueba de una página; NO equivale a compilar el artículo completo.

## Comp puertas sin cerrar

1. **PDF definitivo y límites de página:** falta compilar el nuevo `paper/paper.tex` con los recursos reales, cargar bibliografía, verificar etiquetas en el log y revisar visualmente todas las páginas nuevas. El PDF que aún está en esta rama es el **histórico** de 145 páginas, y no corresponde al nuevo fuente.
2. **Correcciones bibliográficas:** el libro `cespedes2016` no aparece citado en el cuerpo compacto; su corrección de capítulo es relevante para la versión archivada, pero no debe confundirse con una referencia efectiva del nuevo paper. Las cinco citas activas cuentan con metadatos editoriales registrados en `docs/COTEJO_BIBLIOGRAFICO_20261125.md`.
3. **Lean:** los módulos existentes son auxiliares o bajo hipótesis explícitas; falta recomprobar la correspondencia del nuevo SHA y acreditar `paper_contribution.py check`. Ninguna de las ocho filas se declara `proved` por inferencia.
4. **Handnotes:** ocho pruebas escritas genuinamente por el autor; las cinco iniciales están en elaboración y las otras tres en guía.
5. **Entrega:** no convertir esta rama en la versión oficial hasta que `paper/paper.pdf` sea regenerado y cotejado con su fuente, se aplique QA, y la PR de cambio de alcance esté lista para integrarse.

**Veredicto:** rama de edición científicamente acotada y estáticamente consistente; **NO lista para fusionar** por ausencia de PDF recompilado y manuscritos reales.


## Compilación aislada disponible

Se añadió `scripts/build_compact_paper.sh`: ejecutarlo desde la raíz con `bash scripts/build_compact_paper.sh` en un entorno con pdflatex, bibtex y fuentes del repositorio. Compila el PDF del paper y presenta el mensaje `IE_COMPACT_BODY_PAGES=` sin disparar Lean ni el conjunto amplio de Actions; **todavía no se ha ejecutado sobre la rama candidata completa** en este chat, porque el contenedor local no tiene una copia de la rama de GitHub. Un éxito del script sería una comprobación de LaTeX, no del equilibrio económico ni de todos los lemas Lean.
