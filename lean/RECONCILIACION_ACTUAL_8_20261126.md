# Ocho resultados del artículo vigente: comparación con Lean

**Corte:** 26 de noviembre de 2026. **Fuente del paper:** commit bac3c6255da39cd1169a965df35bb5e9a230e6e8, con ocho declaraciones literales inventariadas en current_paper_source_inventory_8.json. **Motor:** AppliedModelingLib, propietario nikhgarg, commit 194edcc95df74806a39b961d10dedddc6e730cce, Lean 4.30.0-rc2.

Esta tabla no certifica correspondencia por coincidencia del nombre. Los módulos previos son una campaña histórica; sus teoremas pueden tener hipótesis distintas.

| Resultado en el PDF | Evidencia previa | Brecha actual |
|---|---|---|
| Proposición 3.1, dos raíces locales de complementariedad | ScalarComplementarityMultiplicityCandidate.lean | El conteo Lean supone raíz positiva y antitonicidad. No demuestra el teorema de la función implícita bajo las hipótesis C1 del paper ni recuperación de equilibrio SOURCE |
| Proposición 5.1, decaimiento matricial | Certificado racional de Python para F0 | No existe un teorema Lean literal de las cotas de norma y los coeficientes de F0 |
| Lema 5.2, robustez matricial | Recursión racional de 48 pasos en Python | No está formalizado el telescopado y la desigualdad para toda matriz A próxima a F0 |
| Proposición 5.3, cuña financiera | SourceFirmEulerPledgeWedgeCandidate.lean, que trata Euler y no esta identidad | Nuevo candidato CurrentCompactWedgeRepayment.lean/effectiveWedgeCurrentSpec con precio efectivo y W positivo. Debe compilar y revisarse contra el paper |
| Lema A.1.1, repago robusto | PaperRepaymentExactCandidate.lean prueba una especificación antigua | La versión antigua exige depreciación estrictamente positiva; el nuevo artículo permite depreciación cero y plantea la garantía en unidades reales. Nuevo candidato repaymentCurrentSpec con hipótesis exactas pendiente de compilar |
| Lema A.1.2, no deuda y ahorro positivos a la vez | PaperFinancialMainExactCandidate.lean | Cotejar normalización de expectativas, signos, interioridad y multiplicadores KKT contra el nuevo texto |
| Proposición A.1.3, capacidad financiable | PaperFinancialMainExactCandidate.lean prueba la derivada y su signo | Falta acreditar en Lean la existencia y alcanzabilidad del máximo desde presupuesto y garantía |
| Lema A.1.4, eficiencia y diferencial de pérdida | PaperAllocationLossElasticityCandidate.lean prueba identidades algebraicas y orden MPK | Falta certificar el óptimo de trabajo, producto eficiente, no negatividad y derivada de agregadores reales |

## Criterios de adjudicación

- **Demostrado en Lean:** Spec transparente con cuantificadores y supuestos del paper exacto; endpoint distinto sin sorryAx; compilación kernel real; auditoría semántica y de axiomas.
- **Demostrado bajo hipótesis adicionales:** detallar cuáles. Ejemplo: la antigua prueba del repago usa delta estrictamente positiva, frente a delta no negativa del artículo vigente.
- **Abierto:** solo existe evidencia Python, una declaración auxiliar con alcance inferior, un candidato sin compilar o falta un puente económico.

## Requisito oficial todavía por completar

La carpeta actual lean/ conserva cientos de candidatos y un checkpoint del manuscrito antiguo, **pero no es la carpeta paper-scoped final generada por AppliedModelingLib**. Falta elaborar el statement-spec con las ocho afirmaciones, obtener una PaperInterface Lean fiel, ejecutar la comprobación oficial desde AppliedModelingLib con el comando:

    python3 scripts/paper_contribution.py check Ventura26LiquidityAllocation --fast

El procedimiento de integración debe conservar los resultados anteriores pero copiar sin alteraciones el paquete generado del paper definitivo. No deben introducirse hipótesis que postulen la conclusión. El informe del 26/11 mantiene el estado ABIERTO de cualquier resultado sin esta evidencia.

La compilación preliminar de dos candidatos nuevos se encuentra en https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/45845549105 . Esta nota no anticipa su veredicto.
