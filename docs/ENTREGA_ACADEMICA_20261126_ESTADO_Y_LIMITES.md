# ENTREGA ACADÉMICA — IE project (26 de noviembre de 2026)

**Estado de entrega:** **CANDIDATO DE ENTREGA CON LIMITACIONES EXPLÍCITAS**, no certificación de equilibrio dinámico completo. 
**Repositorio evaluado:** `alejandroventuraventurameza-tech/ai-project`, rama `main`.
**Referencia de integración:** PR #3 (fusionado, commit `ea920f34d9099de2a7c954cd7dc7708a6de4bcca`), complementado por los PR #67–#70 y #72, todos certificados en Lean y fusionados.
**Fecha límite acordada:** 26/11/2026, 22:00, hora de Lima.
**No se cambió el objeto evaluado por una rama no fusionada.**

## Artefactos que se entregan

| Objeto | Ruta en `main` | Estatus |
|---|---|---|
| Manuscrito académico, fuente | `paper/paper.tex` | Entregado |
| Manuscrito, PDF | `paper/paper.pdf` | Entregado; 11 páginas de cuerpo / 16 totales en el control de PR #3 |
| Bibliografía | `paper/references.bib` | Entregada |
| Presentación final | `slides/final.tex`, `slides/final.pdf` | Entregada; 41 láminas, versión final de exposición |
| Guía de exposición | `slides/GUIA_EXPOSICION_FORMAL.md` | Entregada |
| Simulaciones y reproducción | `code/verify.py`, `code/verify_compact_paper.py`, `code/irf/`, `code/output/`, `code/requirements.txt` | Entregadas, interpretadas como ejercicios reducidos/ilustrativos, NO solución completa del equilibrio infinito |
| Formalización Lean | `lean/` | Entregada; teoremas en kernel auditados por su alcance exacto |
| Matriz paper–Lean | `paper/lean_formalization_matrix_8.md`, `paper/verification_map_8.md` | Entregada |
| Registro de uso de IA | `prompts.md` | Entregado |
| Derivaciones manuscritas | `hand/` | **INCOMPLETO**: hay guías y controles de cobertura, pero NO ocho manuscritos auténticos del autor adjuntos. No simular que lo están. |

## Evidencias de publicación

- PR #3, `Entrega final IE project (candidato): paper, IRF, Lean y auditoría de precierre`: fusionado en `main`; controles de `build`, `editorial-qa` y workflows específicos aprobados en la revisión de cierre.
- PR #67: ocho prefactores bancarios SOURCE continuos en el testigo de dos fechas; kernel aprobado.
- PR #68: identidad de log-coordenadas SOURCE y derivadas de tasas/cantidades realizadas; kernel aprobado.
- PR #69: ocho cruces bancarios continuos y transporte condicional de Fréchet; kernel aprobado.
- PR #70: dos filas monetarias originales de cantidad derivadas exactamente; kernel aprobado.
- PR #72: fórmula Cobb–Douglas original con trabajo endógeno, kernel aprobado, integrada `f9a380785186a0a6b09ff074f86c405d6162e857`.

## Límites metodológicos no resueltos

1. El objeto SOURCE-33 original **no tiene certificación completa de diferenciabilidad C¹ en un entorno** ni operador Jacobiano económico completamente identificado.
2. **No hay inversa rigurosamente certificada del Jacobiano original 33×33**, ni aplicación completa del IFT al equilibrio económico.
3. **No se ha probado la correspondencia funcional total SOURCE–Python**, ni que las IRF numéricas del evaluador reducido correspondan a un equilibrio competitivo dinámico infinito.
4. **No se demuestran dos equilibrios generales completos**: las raíces escalares locales y los mecanismos condicionales tienen ese alcance y no otro.
5. Las pruebas manuscritas auténticas exigidas son un insumo del autor que permanece pendiente. Las guías tipografiadas no sustituyen evidencia manuscrita.
6. PR #71 (derivadas de reglas monetarias de tasa condicionadas a producción) sigue en borrador y con CI especializado fallido. No se incorpora a `main` como resultado demostrado.

## Reproducción y lectura responsable

Ejecutar, desde raíz del repositorio con dependencias declaradas, `python code/verify.py` y el auditor `python code/verify_compact_paper.py`. La compilación y los tests oficiales se controlan desde `.github/workflows/` y sus artefactos en GitHub Actions. Para verificar un resultado específico, consultar su módulo Lean y `#print axioms`; un workflow verde no corrige por sí solo una discrepancia de semántica económica.

**Decisión editorial de cierre:** entregar material académico reproducible y formalmente delimitado en `main`, sin renombrar hipótesis pendientes como teoremas ni reconstruir en falso manuscritos, equilibrio, inversa o IRF estructurales.
