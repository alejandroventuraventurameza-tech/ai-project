# Auditoría bibliográfica y control de versiones — 25/11/2026

**Método:** cotejo de **metadatos y versiones** con páginas de los autores, revistas, bancos centrales y NBER. NO es verificación de todas las citas textuales, ecuaciones o números de página de los 17 recursos. Los archivos bib y PDF se mantienen sincronizados con la última compilación verificada: las mejoras editoriales adicionales pueden aplicarse conjuntamente cuando sea posible regenerar el PDF.

## Entradas verificadas contra fuentes primarias / editoriales

| Clave BibTeX | Referencia comprobada | Fuente | Estado |
|---|---|---|---|
| \`gonzalez2026\` | Documento de enero de **2026**, **tres autores**: Beatriz González, Galo Nuño y Dominik Thaler. La versión histórica con Silvia Albrizio NO es el texto primario que se cita aquí | https://www.galonuno.com/uploads/1/3/4/6/134687692/aer_2026.pdf | Metadatos y portada cotejados |
| \`bianchi2022\` | Bianchi y Bigio, *Econometrica* **90(1)**, 391–454 (2022), DOI 10.3982/ECTA16599 | https://www.minneapolisfed.org/research/staff-reports/banks-liquidity-management-and-monetary-policy | Publicación verificada; la nota de manuscrito 2021 debe mantenerse como versión de lectura |
| \`bianchiSettlement2026\` | Bianchi y Bigio, *Journal of Economic Theory* **234** (2026), artículo **106166**, DOI 10.1016/j.jet.2026.106166 | https://www.sciencedirect.com/science/article/pii/S002205312600030X | Publicación verificada; el Bib existente contiene año, revista y DOI, pero falta volumen/artículo |
| \`asriyan2025\` | Asriyan et al., *Review of Economic Studies* **92(4)**, 2197–2227 (2025), DOI 10.1093/restud/rdae065 | https://academic.oup.com/restud/article/92/4/2197/7698437 | Publicación y páginas verificadas |
| \`albrizio2023\` | Albrizio, González y Khametshin, Documento de Trabajo BdE **2302** de 2023; publicado en *European Economic Review* **185** (mayo 2026), artículo **105278** | https://www.bde.es/wbe/en/publicaciones/analisis-economico-investigacion/documentos-trabajo/tale-two-margins-monetary-policy-and-capital-misallocation.html | Estado editorial 2026 ya indicado correctamente en Bib |
| \`cavenaile2023\` | Cavenaile, Celik y Tian, artículo publicado online **7 octubre 2026** en *Review of Economic Studies*, DOI **10.1093/restud/rdag110** | https://academic.oup.com/restud/advance-article/doi/10.1093/restud/rdag110/8874096 | Publicación 2026 cotejada; conservar referencia a manuscrito 2023 si sus páginas son las utilizadas |
| \`abad2025\` | Abad, Bigio, García-Villegas, Marbet y Nuño; versión posterior como NBER WP **35239**, mayo 2026, DOI 10.3386/w35239 | https://www.nber.org/papers/w35239 | Versión posterior comprobada; autoría y WP 2026 correctos, no se reemplaza sin cotejar el texto 2025 |
| \`bigioSannikov2023\` | Bigio y Sannikov, NBER WP **28540** cuya emisión inicial es **marzo de 2021**, DOI 10.3386/w28540 | https://www.nber.org/papers/w28540 | Se verifica el origen 2021; **no** se ha verificado el día exacto del manuscrito revisado en 2023 mencionado en Bib |

## Correcciones recomendadas cuando se regenere el PDF

1. Para \`gonzalez2026\`, enlazar directamente al documento de enero de 2026, en lugar de la página de navegación genérica: \`https://www.galonuno.com/uploads/1/3/4/6/134687692/aer_2026.pdf\`. Se comprobó la portada y su atribución.
2. Para \`bianchiSettlement2026\`, añadir \`volume={234}\` y \`pages={106166}\` (identificador de artículo, no intervalo).
3. Evitar convertir \`cavenaile2023\`, \`albrizio2023\` o \`abad2025\` automáticamente en citas de 2026 si el manuscrito consultado para las ecuaciones fue el de una versión anterior.
4. No mantener un estado editorial ni una paginación sin distinguir **año de versión consultada** frente a **año de publicación posterior**.

## Límites no resueltos

Quedan referencias cuya correspondencia detallada con cada párrafo del paper **no fue contrastada** en esta auditoría (incluidos Midrigan–Xu, Gopinath et al., Peters, Jiménez et al., Céspedes et al., Sims, Abbondandolo–Majer, Schmitt-Grohé–Uribe y documentación de Python). La congruencia BibTeX por sí sola no garantiza precisión de las citas a páginas, hipótesis o teoremas. Esta revisión se limita a las entradas arriba indicadas.

**Conservación de PDFs:** en esta fase se restaura el archivo \`references.bib\` original del commit \`c52cabd\` para que \`paper/paper.pdf\` siga correspondiendo a la fuente exacta previamente compilada. Aplicar cambios editoriales bibliográficos implica recompilar y confirmar el PDF nuevo antes de integrarlo en main.
