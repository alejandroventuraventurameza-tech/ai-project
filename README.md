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

**Evidencia y límites.** El artículo compacto tiene **11 páginas de cuerpo y 16 en total**, con ocho resultados numerados, demostraciones analíticas y una tabla Lean que identifica sus obligaciones abiertas. El PDF fue recompilado desde las figuras originales y comprometido junto al LaTeX. Los cuatro PDF y `code/verify.py` aprobaron nuevamente en [build #45848283036](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/45848283036) y [auditoría editorial #45848283017](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/45848283017), ambos sobre `main@a76d49ee`. La [versión histórica de 145 páginas](https://github.com/alejandroventuraventurameza-tech/ai-project/tree/archive/ie-paper-full-20261118) permanece íntegra. **No está acreditada la correspondencia literal de los ocho resultados con Lean ni se han incorporado manuscritos auténticos (0/8).** Los ejemplos S/B no certifican multiplicidad de equilibrio competitivo ni crecimiento permanente.

**Archivos:** [paper PDF](paper/paper.pdf) · [LaTeX y bibliografía](paper/paper.tex) · [propuesta](proposal/proposal.pdf) · [presentación inicial](slides/topic.pdf) · [presentación final](slides/final.pdf) · [código](code/verify.py) · [Lean](lean/README.md) · [manuscritos e índice de ocho pruebas](hand/CONTROL_COBERTURA_MANUSCRITA_8.md) · [prompts](prompts.md).

**Reproducción desde la raíz:** instalar `code/requirements.txt` y ejecutar `python code/verify.py`.

**Estado de entrega (26/11):** artículo, simulaciones y cuatro PDF preservados en `main`. Los PR [#6](https://github.com/alejandroventuraventurameza-tech/ai-project/pull/6) y [#7](https://github.com/alejandroventuraventurameza-tech/ai-project/pull/7) incorporaron **cuatro demostraciones autónomas verificadas por el kernel Lean**, sin cambiar la versión científica sometida. El módulo histórico de pérdida asignativa con once cláusulas también fue compilado; el [PR #9](https://github.com/alejandroventuraventurameza-tech/ai-project/pull/9) añadió un **sublema Lean verificado** para `log(Yeff/Y)=log Yeff−log Y` bajo positividad y cota eficiente. Sin embargo, todavía falta demostrar la **equivalencia semántica íntegra de los ocho enunciados del artículo con Lean** y ejecutar el chequeo oficial paper-scoped. Los **ocho manuscritos originales** aún deben adjuntarse a `hand/`. Informes: [QA de código](docs/QA_VERIFICADORES_COMPACTO_20261125.md), [QA visual](docs/QA_CANDIDATO_COMPACTO_20261125.md), [estado Lean del artículo](lean/RECONCILIACION_ACTUAL_8_20261126.md), [log de cuatro pruebas](lean/VALIDACION_KERNEL_4_RESULTADOS_20261126.md) y [cotejo del lema de eficiencia](lean/COTEJO_LEMA_ASIGNACION_A14_20261126.md).

**Avance formal adicional (26/11):** El módulo [PaperLemma43CompactIntegratedCandidate.lean](lean/candidates/Ventura26LiquidityAllocation/PaperLemma43CompactIntegratedCandidate.lean) reúne ahora las once cláusulas históricas de eficiencia y el cociente logarítmico del paper en una sola especificación, **compilada y auditada** en [Actions #45856710241](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/45856710241), sin `sorryAx`. La derivada física del cociente de producto, antes pendiente, se demostró posteriormente en los módulos de trayectoria y en el **Spec conjunto** `compactLemmaA14CurrentFullSpec` con el teorema `compactLemmaA14CurrentFull_exact` ([Actions #45859315801](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/45859315801), 8,339 trabajos, sin `sorryAx`). Esto NO prueba equilibrio dinámico ni resuelve la correspondencia semántica paper-scoped oficial o los ocho manuscritos personales del autor.

**Avance en la Proposición 5.1 (26/11):** Los 36 coeficientes decimales originales de `F0` se fijaron como racionales exactos en [CurrentCompactBlock48Tail.lean](lean/current/CurrentCompactBlock48Tail.lean) y se cotejaron contra el SHA del JSON de origen. La [auditoría de Actions #45861545922](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/45861545922) reejecutó el certificado racional (cota 48 pasos <24/25; máximo transitorio antes de 48 <61/10, en n=7) y verificó en Lean, sin `sorryAx`, **la implicación universal de decaimiento por bloques**. Las dos desigualdades finitas aún son *premisas* en Lean, no teoremas del kernel. Ver [auditoría Prop. 5.1](docs/AUDITORIA_PROP_51_MATRIZ_DECIMAL_20261126.md). No se declara formalización literal completa ni estabilidad del equilibrio DSGE.

**Lema 5.2 — paso telescópico en Lean (26/11):** [CurrentCompactRobustTelescoping.lean](lean/current/CurrentCompactRobustTelescoping.lean) formaliza la identidad no conmutativa `A^n-F0^n` y la desigualdad de normas inducidas para cualquier par de matrices reales 6×6. [Actions #45864283745](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/45864283745) comprobó ambas pruebas sin `sorryAx` y con axiomas fundacionales. **No certifica todavía** `‖A^48‖∞<49/50`, que requiere la recursión finita de mayorantes y un puente con las cotas de `F0`. Ver [auditoría del Lema 5.2](docs/AUDITORIA_LEMA52_TELESCOPIO_20261126.md).
