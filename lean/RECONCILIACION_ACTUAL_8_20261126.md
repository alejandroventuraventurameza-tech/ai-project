# Ocho resultados del artículo vigente: comparación con Lean

**Corte:** 26 de noviembre de 2026. **Fuente del paper:** commit bac3c6255da39cd1169a965df35bb5e9a230e6e8, con ocho declaraciones literales inventariadas en current_paper_source_inventory_8.json. **Motor:** AppliedModelingLib, propietario nikhgarg, commit 194edcc95df74806a39b961d10dedddc6e730cce, Lean 4.30.0-rc2.

Esta tabla no certifica correspondencia por coincidencia del nombre. Los módulos previos son una campaña histórica; sus teoremas pueden tener hipótesis distintas.

| Resultado en el PDF | Evidencia previa | Brecha actual |
|---|---|---|
| Proposición 3.1, dos raíces locales de complementariedad | ScalarComplementarityMultiplicityCandidate.lean | El conteo Lean supone raíz positiva y antitonicidad. No demuestra el teorema de la función implícita bajo las hipótesis C1 del paper ni recuperación de equilibrio SOURCE |
| Proposición 5.1, decaimiento matricial | Certificado racional de Python para F0 | No existe un teorema Lean literal de las cotas de norma y los coeficientes de F0 |
| Lema 5.2, robustez matricial | Recursión racional de 48 pasos en Python | No está formalizado el telescopado y la desigualdad para toda matriz A próxima a F0 |
| Proposición 5.3, cuña financiera | SourceFirmEulerPledgeWedgeCandidate.lean, que trata Euler y no esta identidad | Nuevo effectiveWedgeCurrentSpec y su prueba effectiveWedgeCurrent_exact: **compilación kernel aprobada** (#45847583114, sin sorryAx). Falta correspondencia semántica oficial con firmas y garantía vinculante. |
| Lema A.1.1, repago robusto | PaperRepaymentExactCandidate.lean prueba una especificación antigua | La versión antigua exige depreciación estrictamente positiva; el nuevo artículo permite depreciación cero y plantea la garantía en unidades reales. Nuevo repaymentCurrentSpec y su prueba repaymentCurrent_exact: **compilación kernel aprobada** (#45847583114, sin sorryAx), incluyendo delta igual a cero. Falta vincular la demostración puntual con cada estado admisible del modelo. |
| Lema A.1.2, no deuda y ahorro positivos a la vez | PaperFinancialMainExactCandidate.lean (histórico) y nuevo CurrentCompactInteriorKKT.lean | **Lean aprobado** (#45851966286): expectedRealMarginal_pos y noSimultaneousInteriorCurrent_exact prueban la contradicción de las FOC bajo distribución de soporte finito, masas que suman uno, positividad casi segura y dual no negativo. Queda cotejo del soporte finito con el árbol del modelo y auditoría fuente–Spec oficial. |
| Proposición A.1.3, capacidad financiable | PaperFinancialMainExactCandidate.lean prueba la derivada y su signo | Nuevo financingCapacityCurrentSpec y su prueba financingCapacityCurrent_exact: **compilación kernel aprobada** (#45847583114, sin sorryAx); verifica máximo alcanzable, cota y derivada. Falta revisión semántica independiente. |
| Lema A.1.4, eficiencia y diferencial de pérdida | **PaperLemma43SourceCompleteCandidate.lean** ya contiene 11 cláusulas integradas y su endpoint compila en Lean (#45847597337) sin sorryAx | El trabajo histórico SÍ demuestra empleo óptimo, referente eficiente alcanzable, log-pérdida no negativa, diferencial y equivalencia de MPK. El puente autónomo `log(Yeff/Y)=log Yeff−log Y` y `log(Yeff/Y)≥0` para `0<Y≤Yeff` ya fue verificado en Lean (#45855571576, sin sorryAx) mediante `currentCompactLogLoss_exact`. **Composición integrada demostrada** en `compactLemmaA14Integrated_exact` (#45856710241, sin `sorryAx`): once cláusulas históricas más ratio logarítmico y cota no negativa, sin añadir como supuesto `Y≤Yeff`. La derivada de la razón *con producción física* está demostrada en `compactLossRatioPhysical_hasDerivAt` (#45858652855), y el Spec conjunto `compactLemmaA14CurrentFullSpec` fue probado por `compactLemmaA14CurrentFull_exact` (#45859315801). **Restan** la revisión source-to-Lean y el check oficial; consultar COTEJO_LEMA_ASIGNACION_A14_20261126.md. |

## Criterios de adjudicación

- **Demostrado en Lean:** Spec transparente con cuantificadores y supuestos del paper exacto; endpoint distinto sin sorryAx; compilación kernel real; auditoría semántica y de axiomas.
- **Demostrado bajo hipótesis adicionales:** detallar cuáles. Ejemplo: la antigua prueba del repago usa delta estrictamente positiva, frente a delta no negativa del artículo vigente.
- **Abierto:** solo existe evidencia Python, una declaración auxiliar con alcance inferior, un candidato sin compilar o falta un puente económico.

## Requisito oficial todavía por completar

La carpeta actual lean/ conserva cientos de candidatos y un checkpoint del manuscrito antiguo, **pero no es la carpeta paper-scoped final generada por AppliedModelingLib**. Falta elaborar el statement-spec con las ocho afirmaciones, obtener una PaperInterface Lean fiel, ejecutar la comprobación oficial desde AppliedModelingLib con el comando:

    python3 scripts/paper_contribution.py check Ventura26LiquidityAllocation --fast

El procedimiento de integración debe conservar los resultados anteriores pero copiar sin alteraciones el paquete generado del paper definitivo. No deben introducirse hipótesis que postulen la conclusión. El informe del 26/11 mantiene el estado ABIERTO de cualquier resultado sin esta evidencia.

La compilación más reciente de cuatro declaraciones actuales es https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/45851966286 y concluyó correctamente, con el alcance descrito en VALIDACION_KERNEL_4_RESULTADOS_20261126.md. El módulo histórico de eficiencia integrada se compiló aparte en https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/45847597337. La prueba adicional del sublema logarítmico está en https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/45855571576 y se fusionó mediante PR #9. **Ninguna de estas ejecuciones reemplaza** la revisión semántica paper-scoped oficial.
