# Adenda postplazo — fuente congelada y contrato de ocho enunciados

**Fecha:** 27 de noviembre de 2026, posterior a la entrega científica del 26/11. Esta adenda **no** cambia el PDF sometido, los handnotes ni la cronología de entrega.

## Fuente primaria, exactamente identificada

- Revisión original del artículo: `bac3c6255da39cd1169a965df35bb5e9a230e6e8`.
- PDF de 16 páginas: `paper/paper.pdf` en dicha revisión; 519,368 bytes.
- Git blob del PDF: `45207cd36ab8a316b4fa4f157f62e2610311ead5`.
- SHA-256 del PDF: `923b766624491e7f7b290c4302332140cd5636fe421ab27c7d4024377db7d2e3`.
- Ocho fragmentos de enunciados: `lean/current_paper_source_inventory_8.json`, cotejados con los Git blobs congelados de `paper/paper.tex`, `paper/body_compact_after.tex` y `paper/appendix_eight_results.tex`.

## Validación reproducible en GitHub Actions

La ejecución [#46070284153](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/46070284153) terminó **satisfactoriamente** usando el upstream AppliedModelingLib `194edcc95df74806a39b961d10dedddc6e730cce`.

El script `scripts/build_eight_statement_spec.py` genera una pareja de archivos `source-paper-8.pdf` + `statement-spec-8.json` con ocho registros esquema v1 (`source_item`, `source_kind`, `source_location`, `source_statement`, `lean_name`, `lean_type` y `kind`). Se construye además `statement-spec-provenance.json` con la localización original, SHA-256 de la cita literal, Git blob, tipo Lean y límites matemáticos.

**Compuertas aprobadas:**

1. Identidad de Git blob, longitud y SHA-256 del PDF original, además del conteo de 16 páginas mediante `pdfinfo`.
2. Presencia única y literal de cada uno de los ocho enunciados en su archivo LaTeX del commit original.
3. Aceptación de los ocho tipos por la función oficial upstream `scripts.new_paper.load_statement_spec`; previsualización estructural de ocho especificaciones.
4. Pruebas negativas del validador: archivo PDF alterado, tipo ficticio `True` y duplicación de nombre, todos rechazados correctamente.

Se preservan como artefactos de la ejecución el JSON de especificaciones, el registro de procedencia, una previsualización Lean y una copia byte-idéntica del PDF original. Las pruebas Lean de ocho resultados y el chequeo rápido previo están acreditados **por separado** en [#46068856283](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/46068856283), 8,359 trabajos.

## Anomalía de compatibilidad encontrada y declarada

El validador upstream utiliza una expresión regular insensible a mayúsculas para detectar el marcador inglés `TODO`. Esa regla reconoce equivocadamente dos usos legítimos de «todo» en la Proposición 5.1, «Para todo» e «y todo». Para que el formato oficial sea aceptado **sin modificar la fuente primaria**, únicamente el campo `source_statement` remitido al parser sustituye «Para todo» por «Para cada» e «y todo» por «y cada», cuantificadores equivalentes en este contexto.

El enunciado **literal original** se preserva sin cambios en `statement-spec-provenance.json`, junto con su hash, ubicación exacta y la bandera `original_statement_matches_spec_field = false`. Los otros siete enunciados coinciden literalmente con sus campos. Esta compatibilidad no equivale a una transcripción plenamente literal en el parser ni a resolver su defecto upstream; debe corregirse o justificarse en el cierre semántico.

En el tipo `a12Spec`, la referencia a la proposición de soporte finito omite el sufijo sintáctico explícito `.{u}` a fin de utilizar la generalización implícita de universo del generador; esa transformación también está marcada. No extiende el alcance a distribuciones arbitrarias.

## Alcance y obligaciones pendientes

**Completado:** identificación binaria de la fuente, cotejo de ocho enunciados LaTeX y aceptación del contrato fuente/tipos por el **loader oficial**. **No completado:** ejecutar `paper_contribution.py new --statement-spec` con todos los módulos semánticos elaborados, la auditoría independiente de átomos source-to-Spec, el protocolo no rápido y `prepare-pr` de AppliedModelingLib. El archivo `PaperInterface.source-structural-preview.lean` es una previsualización, **no** una nueva compilación autónoma de la interfaz oficial.

Tampoco se ha certificado la equivalencia entre F0 y el Jacobiano económico SOURCE, la recuperación de 33 ecuaciones, una solución del equilibrio dinámico infinito ni una comparación de bienestar de equilibrio. El resultado de A.1.2 sigue limitado a esperanzas de soporte finito y condiciones de primer orden **necesarias**.

**Conclusión verificable:** se aprobó una compuerta oficial de identidad documental y esquema v1, pero la concordancia semántica integral del modelo económico permanece abierta.
