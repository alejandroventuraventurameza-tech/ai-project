# Adenda formal, posterior al plazo — cinco resultados del artículo compacto

**Fecha de elaboración:** 27 de noviembre de 2026, después de la hora límite del 26/11/2026, 22:00 (Lima).  
**Objeto científico congelado:** \`ai-project@bac3c6255da39cd1169a965df35bb5e9a230e6e8\`, ocho enunciados enumerados en \`lean/current_paper_source_inventory_8.json\`, con sus \`source_git_blob\` originales.  
**Entrega documental original preservada:** \`main@ab0fdb562bf20bdc9e430e1786c64b243597ba1b\` al abrir esta adenda.  
**Nueva prueba paper-facing:** \`lean/candidates/Ventura26LiquidityAllocation/PostDeadlineCurrentPaperFive.lean\`.  
**Control especializado:** [Actions en la rama de la adenda](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/workflows/ie-postdeadline-five-paper-proofs.yml). **No atribuir a la entrega de plazo**.

## Correspondencias de premisas y conclusiones

| Resultado vigente | Tipo certificado/propuesto en Lean | Enunciado y alcance auditado | Restricción que debe conservarse |
|---|---|---|---|
| Lema A.1.1, \`lem:repayment\` | \`CurrentCompact.repaymentCurrentSpec\`; endpoint \`lemma_A11_repayment_paper\` | Cobertura real \((R^Lb)/\Pi' \le \theta(1-\delta)q'k'\), \(0\le\delta<1\), \(0\le\theta<1\), \(\pi^{op}\ge0\), saldo de patrimonio con depósito seguro; cota inferior y no negatividad, estricta si \(k'>0\) o \(a>0\) | Demuestra pago/patrimonio de la firma **por estado**, no solvencia agregada de bancos ni consumo positivo |
| Lema A.1.2, \`lem:v0m_original_6_2\` | \`CurrentCompact.noSimultaneousInteriorCurrentSpec\`; endpoint \`lemma_A12_interior_FOC_paper\` | Dos FOC originales, \(\beta_E>0\), \(R^L>R^D>0\), valor marginal positivo casi seguramente y dual de colateral no negativo; contradicción lógica si posiciones de ahorro y deuda son simultáneamente interiores | **Esperanza representada en soporte finito con probabilidades no negativas y suma uno**, compatible con el árbol finito del modelo, pero no formalización de integrales sobre distribuciones arbitrarias. No prueba suficiencia global de KKT |
| Proposición A.1.3, \`prop:v0m_original_6_3\` | \`CurrentCompact.financingCapacityCurrentSpec\`; endpoint \`proposition_A13_financing_capacity_paper\` | \(n>0\), \(q>H/R^L\); presupuesto \(qk'=n+b\) y colateral \(R^Lb\le Hk'\); máximo alcanzable \(n/(q-H/R^L)\), derivada parcial exacta y signo negativo | Capacidad factible, no inversión óptima de equilibrio; \(n,q,H\) constantes al derivar |
| Lema A.1.4, \`lem:allocation_loss_identity\` | \`CurrentCompact.compactLemmaA14CurrentFullSpec\`; endpoint \`lemma_A14_physical_allocation_and_log_loss_paper\` | Misma economía H/L: masas y productividades positivas, \(L>0\), \(\alpha,\beta,d>0\), \(\alpha+\beta+d=1\), capitales positivos y caminos derivables; empleo óptimo, producción física, \(Y^{eff}\), pérdida logarítmica, derivada de reasignación y orden MPK físico | Prueba determinista de asignación para dotaciones dadas, **no** las condiciones del equilibrio infinito; el producto marginal es el parcial a empleo fijado |
| Proposición 5.3, \`prop:compact_source_collateral_effective_wedge\` | \`CurrentCompact.effectiveWedgeCurrentSpec\`; endpoint \`proposition_53_effective_price_wedge_paper\` | Misma tasa de préstamo positiva, \(J=(1-\delta)\Pi' q'>0\), \(\theta_H<\theta_L\), y precios \(p_i^{eff}=q-\theta_iJ/R^L\); diferencia positiva \(W=(\theta_L-\theta_H)J/R^L\) | Fórmula condicionada a garantía vinculante; no implica que ambas firmas estén vinculadas en una rama particular ni una respuesta de bienestar |

## Pruebas previas que se están integrando

- **A.1.1 y 5.3:** \`CurrentCompactWedgeRepayment.lean\` — \`repaymentCurrent_exact\`, \`effectiveWedgeCurrent_exact\`; validación previa [#45847583114](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/45847583114).
- **A.1.2:** \`CurrentCompactInteriorKKT.lean\` — \`expectedRealMarginal_pos\`, \`noSimultaneousInteriorCurrent_exact\`; validación [#45851966286](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/45851966286).
- **A.1.3:** \`CurrentCompactFinancingCapacity.lean\` — \`financingCapacityCurrent_exact\`; validación previa [#45847583114](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/45847583114).
- **A.1.4:** \`PaperLemma43CurrentFullCandidate.lean\` — \`compactLemmaA14CurrentFull_exact\`, cuya especificación incluye el paquete físico de once resultados y el \`HasDerivAt\` del logaritmo de la **razón de producciones originales**, y no un proxy de output; validación [#45859315801](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/45859315801).

## Criterios de aceptación de esta adenda

1. Source lock: conservar los \`statement_latex\` del inventario original, su revisión de fuente y los cinco \`label\` sin alterar.
2. Lean: compilar el módulo conjunto con upstream fijo \`194edcc95df74806a39b961d10dedddc6e730cce\`, Lean \`v4.30.0-rc2\`; inspeccionar \`#print axioms\` en **las cinco interfaces y el teorema conjunto**; rechazar \`sorryAx\`, \`admit\`, metas pendientes y errores.
3. No elevar automáticamente \`paper_contribution.py check Ventura26LiquidityAllocation --fast\` a **aprobado**: el repositorio contiene un checkpoint de la interfaz histórica de 57 resultados. El comando oficial requiere un paquete paper-scoped generado y registrado a partir del artículo compacto. Una ejecución sobre el checkpoint antiguo NO certificaría estos ocho enunciados.
4. Tras éxito del kernel, actualizar la matriz \`paper/lean_formalization_matrix_8.md\` con cada testigo y su grado exacto (demostrado bajo hipótesis fieles, o correspondencia finita de esperanza), sin borrar los límites SOURCE–Python ni prometer equilibrio infinito.
5. Mantener esta documentación en un PR **posterior al plazo**, separado de la revisión científica original. La subida no altera el sello de entrega.

## Fuera del alcance incluso después del cierre de estos cinco

Siguen abiertos la identificación de la raíz escalar con un equilibrio competitivo completo, la existencia y regularidad \`C¹\` de \`F_SOURCE\` en las 33 variables originales, la invertibilidad de su Jacobiano, y la igualdad semántica con el evaluador reducido Python/IRF. Los teoremas matemáticos de las proposiciones 3.1, 5.1 y el Lema 5.2 tienen sus propias especificaciones y certificados previos, con esas mismas fronteras económicas.
