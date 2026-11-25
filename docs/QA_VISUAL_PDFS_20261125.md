# Auditoría visual y binaria de PDF — 25 de noviembre de 2026

**Origen revisado:** artefacto `pdfs` (ID 14429203142) del proceso GitHub Actions [build #44308365992](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/44308365992), basado en el commit `71bc6a119aefd9ec7515b36f4e6beb422541bd84` del 18/11/2026. **Este es un artefacto de CI anterior al commit de sincronización `c52cabd`**. No debe presentarse como inspección binaria de los cuatro PDF actualmente guardados en GitHub.

## Auditoría de extensión y aspecto

| PDF | Páginas | Inspección visual | Geometría de texto |
|---|---:|---|---|
| `proposal/proposal.pdf` | 4 | Las 4 páginas: portada, ecuaciones, conclusiones, bibliografía | Ningún span de texto fuera de página |
| `slides/topic.pdf` | 11 | Las 11 láminas; estructura, ecuaciones y tablas legibles a zoom de inspección | Ningún span de texto fuera de página |
| `slides/final.pdf` | 41 | Las 41 láminas; tablas, diagramas, IRF y anexos; varias láminas técnicas requieren zoom | Ningún span de texto fuera de página |
| `paper/paper.pdf` | 145 | Muestreo de páginas 1–18, 20–22, 50, 75, 100, 125 y 143–145 | Ningún span de texto fuera de página, incluidas las 145 páginas |

No se hallaron páginas sin texto, ni superposiciones evidentes en los contactos visuales inspeccionados. El control automático usa cajas `fitz` de los spans de texto de todas las páginas, con tolerancia geométrica de 1 punto. **No detecta necesariamente superposiciones entre objetos ni imágenes fuera de página**. Por ello el resultado no es certificación visual completa de las 145 páginas del manuscrito.

El papel es A4, una columna; el log de LaTeX fija `IE_COMPACT_BODY_PAGES=12` (cumple 8–20) y deja bibliografía/anexos aparte. La propuesta tiene 4 páginas, límite oficial 2–4. Las presentaciones conservan 11 y 41 diapositivas.

## Identidad exacta de los artefactos descargados

| Archivo | Bytes | SHA-256 de bytes del ZIP de CI | SHA-1 Git blob calculado sobre bytes de CI |
|---|---:|---|---|
| `paper/paper.pdf` | 1,313,173 | `980cf8948afce06affc1ebea83a059bf46f9e22cc91854adc15c2489f0d00e1a` | `8915189b0e2871bee9bc701720c69f45cefe7bec` |
| `slides/final.pdf` | 516,470 | `433b74fd5c29f5a3e50c9819e5120208b65c9555b71a4153e3e11a96cac89f97` | `804b9e217cdd2c82a1668459ccc7845e565a2b5a` |
| `slides/topic.pdf` | 273,789 | `924f283faa3799a773dda1f28fc328ca44f816bb8c625319c144165a7b6af1fa` | `0c1e3f53eeaa731c3670649c6eea6f649526e5c9` |
| `proposal/proposal.pdf` | 281,119 | `460f999ea59b038f23de753c5bae94b4f0093e1d5ab6497ce320c03346c013af` | `6e2013b8d0384ca8698a8b92bbd93a2021713699` |

**Advertencia comprobada:** los cuatro SHA-1 Git blob calculados sobre el contenido del ZIP de CI **no coinciden** con los SHA-1 de los cuatro PDF publicados en el commit `c52cabd` pese a tamaños iguales. No se ha probado la causa; fechas/ID internos son una posibilidad, no una conclusión. Lo correcto es verificar los PDF efectivamente presentes en `main` después del merge y no afirmar que los bytes son idénticos a los del ZIP.

En todo caso, los archivos fuente (`.tex`, `.bib`) no cambiaron entre la CI verde y la rama de precierre; las diferencias binarias de PDF no implican por sí solas diferencias visibles ni científicas, pero imposibilitan certificar identidad exacta desde el ZIP histórico.

## Puerta de cierre

**Resultado:** inspección visual muestral de PDF de CI y control geométrico completados; quedan pendientes (a) inspección de los PDF realmente comprometidos en revisión definitiva, (b) nueva comprobación oficial de código y compilación para el último commit sin `skip ci`, (c) inclusión de manuscritos reales y (d) merge a `main`. No confundir inspección visual con demostración económica.
