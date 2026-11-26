# Registro de colaboración IA — fase de cierre, 25/11/2026

Este documento separa los aportes asistidos de los juicios efectivamente expresados por el autor. Los prompts históricos permanecen en ../prompts.md; los intercambios no recuperados no se reconstruyen.

| Etapa | Contribución asistida | Comprobación / veredicto atribuible |
|---|---|---|
| Modelo NK e instrumentos | Remuneración, cantidad de reservas, encaje, corredor, negociación OTC y garantías robustas | El autor exigió múltiples instrumentos, firmas heterogéneas y restricción de colateral; no se ha demostrado un equilibrio infinito completo |
| Asignación de capital | Fórmula del producto marginal y derivada de pérdida asignativa | El autor objetó que A_H>A_L implicase automáticamente MPK_H>MPK_L. Corrección incorporada al paper y slides |
| Corredor monetario | Diferencia entre desplazamiento, estrechamiento y costo de ventanilla | Revisión de las ecuaciones de slides/final.tex; el signo de tasas privadas se determina endógenamente |
| Multiplicidad S/B | Prueba escalar condicional y delimitación de la recuperación SOURCE | Proposición 4.2 y auditorías: no confundir raíces del reducido con dos equilibrios competitivos certificados |
| Corrección de slides | Notación de tipos, garantía, MPK, corredor y alcance de pruebas Lean | Commits 3b6510c y 71bc6a1; build #44308365992 y editorial-qa #44308365993 aprobadas |
| Guion oral | Reescritura académica del discurso y Word de estudio | El autor criticó explícitamente la falta de transiciones; el material fue revisado y el autor informa haber expuesto |
| Handnotes | Guía de cinco pruebas del artículo para escribir en iPad | Todavía no existe escaneo autenticado ni veredicto manuscrito del autor |
| Precierre | Inventario de integraciones y discrepancias paper–Lean | La matriz mantiene 0/57 equivalencias literales completas; no atribuir cobertura formal total |

## Veredictos y límites

Un programa que reproduce un resultado del evaluador reducido no prueba el teorema de equilibrio competitivo completo. Los resultados del shock de remuneración tienen parámetros ilustrativos, no estimación causal peruana. El documento de guion no es una prueba matemática. Un módulo Lean compilado solo acredita lo que su enunciado exacto dice bajo sus hipótesis.

**Pendiente:** que el autor adjunte sus derivaciones, identifique errores o dudas encontradas y adjudique las pruebas con sus razones. No se registra una aprobación que no haya ocurrido.

## Fuentes internas

- paper/paper.tex: proposiciones, apéndice de formalización y sección de registro de IA
- paper/result_ledger.json y paper/lean_crosswalk_57.json: estado conservador de 57 resultados
- docs/CIERRE_AVANCE_EXPOSICION_2026-11-18.md: delimitación posterior de la prueba SOURCE
- docs/AUDITORIA_PRECIERRE_20261125.md: hallazgos y puertas de entrega
