# Política monetaria, liquidez bancaria y asignación de capital

**Alejandro Ventura · Universidad del Pacífico · AI and Economic Modeling · Track B (2026-II)**

**Pregunta.** ¿Cuándo una reducción de la remuneración de reservas, transmitida por bancos y negociación interbancaria OTC, mejora o deteriora la asignación de capital entre empresas heterogéneas?

**Modelo.** Economía neokeynesiana cerrada con hogar trabajador, bancos, banco central y firmas H/L. H tiene mayor productividad tecnológica, pero menor pignorabilidad. La decisión de inversión enfrenta presupuesto y garantía de repago:

\[
c_{it}+q_t k_{i,t+1}+a_{it}=N_{it}+b_{it},
\qquad R_t^L b_{it}\leq H_{it}k_{i,t+1}.
\]

**Resultado y condiciones.** Si la función de complementariedad reducida es \(C^1\), \(\mathcal M(0,0)=0\), \(\partial_s\mathcal M(0,0)<0\) y \(\partial_h\mathcal M(0,0)<0\), una innovación \(h<0\) suficientemente pequeña genera **dos raíces escalares locales** (holgura cero y holgura positiva). Esto **no** prueba dos equilibrios competitivos infinitos. Además, una auditoría SOURCE identifica una obstrucción al recuperar ambas ramas cerca de un mismo estado heredado.

El experimento reproducible perturba **solo la remuneración de reservas**, \(h=-10^{-5}\) (aprox. −0.1 pb bajo la convención de log tasa), con encaje fijo \(\rho=0.10\), mismos estados heredados y parámetros **ilustrativos, no estimados para Perú**. Las IRF del *evaluador reducido* arrojan:

| Respuesta al impacto | S: L inicialmente holgada | B: ambas restringidas |
|:--|--:|--:|
| Tasa de préstamo (pb) | −0.063632 | −0.090908 |
| Crédito a H (log %) | +0.001095 | +0.000841 |
| Capital elegido por H (log %) | +0.000164 | −0.001073 |
| Producción corriente (log %) | −0.000036 | −0.004143 |
| Cambio de pérdida asignativa (100 Δlog) | −0.00000248 | +0.00000852 |

El capital elegido hoy se instala mañana. Más crédito no implica necesariamente más inversión; la pérdida asignativa compara producto con un referente eficiente a dotaciones dadas y **no mide bienestar**.

**Evidencia y límites.** Los controles numéricos y la compilación de cuatro PDF aprobaron en [build #44308365992](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/44308365992), con auditoría [editorial-qa #44308365993](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/44308365993), el 18/11. El cuerpo del artículo tiene **12 páginas** (145 incluyendo bibliografía y anexo histórico). Lean contiene pruebas auxiliares condicionales; el inventario histórico mantiene **0/57 equivalencias literales completas** y el cuerpo agrega tres resultados por conciliar. **No** se demuestra selección de régimen, equilibrio infinito ni crecimiento permanente.

**Archivos:** [paper PDF](paper/paper.pdf) · [LaTeX y bibliografía](paper/paper.tex) · [propuesta](proposal/proposal.pdf) · [presentación inicial](slides/topic.pdf) · [presentación final](slides/final.pdf) · [código](code/verify.py) · [Lean](lean/README.md) · [manuscritos](hand/README.md) · [prompts](prompts.md).

**Reproducción desde la raíz:** instalar code/requirements.txt y ejecutar \`python code/verify.py\`.

**Estado al 25/11:** candidato, **no fusionado en main**. Pendientes: notas manuscritas auténticas, cotejo paper–Lean por resultado, revisión definitiva de PDF/CI y merge. Detalle: [auditoría de cierre](docs/AUDITORIA_PRECIERRE_20261125.md), [cotejo bibliográfico](docs/COTEJO_BIBLIOGRAFICO_20261125.md), [QA visual PDF](docs/QA_VISUAL_PDFS_20261125.md) y [PR #3](https://github.com/alejandroventuraventurameza-tech/ai-project/pull/3). **Plazo oficial:** 26 de noviembre de 2026, 22:00 (Lima).
