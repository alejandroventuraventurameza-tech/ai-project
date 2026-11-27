# Cotejo de los ocho resultados del paper compacto — 25/11/2026

La rama `archive/ie-paper-full-20261118` conserva el artículo histórico de 145 páginas y los registros de 57 resultados. **Esta rama candidata reduce el paper sometido a exactamente ocho resultados numerados distintos**, identificados abajo. No elimina código, datos ni pruebas Lean históricas; los separa del objeto evaluable.

| Etiqueta en el paper compacto | Resultado | Evidencia relacionada | Estado exacto para este paper |
|---|---|---|---|
| `prop:local_macro_multiplicity` | Dos raíces locales de complementariedad | `CurrentCompactProp31C1Bridge.lean`: `prop31_scalar_from_only_C1_hypotheses`, Actions #45874767483 | **DEMOSTRADO EN LEAN PARA LA FUNCIÓN ESCALAR C1 ABSTRACTA** bajo signos y derivadas exigidos; **ABIERTO** construir dicha función y recuperación SOURCE real desde las 33 ecuaciones |
| `prop:compact_exact_tail_power` | Decaimiento de potencias de matriz decimal | `CurrentCompactBlock48Tail.lean`: `prop51_unconditional_exact`, Actions #45865176408; certificado racional Python repetido #45933840987 | **DEMOSTRADO EN LEAN PARA LOS 36 DECIMALES FIJADOS DE F0**, norma real inducida y todos los k/x; **ABIERTO** identificar F0 con la dinámica derivada del equilibrio SOURCE |
| `lem:compact_robust_tail_power` | Robustez en bola de norma matricial | `CurrentCompactRobustFiniteCertificate.lean`: `lemma52_decimal_current_exact`, Actions #45871289804; certificado racional Python #45933840987 | **DEMOSTRADO EN LEAN PARA TODA MATRIZ REAL 6×6 A A DISTANCIA ≤10^-4 DE F0**, tres cláusulas del lema; **ABIERTO** verificar la distancia del Jacobiano SOURCE efectivo a F0 |
| `prop:compact_source_collateral_effective_wedge` | Cuña de precios efectivos con garantía vinculante | `PostDeadlineCurrentPaperFive.lean`: `proposition_53_effective_price_wedge_paper`, remite a `effectiveWedgeCurrent_exact`; Actions #46009434502 | **DEMOSTRADO EN LEAN COMO IDENTIDAD ECONÓMICA CONDICIONAL**: tasa bruta común y positiva, J=(1−δ)Π' q'>0, θ_H<θ_L, y diferencia positiva. No identifica endógenamente las ramas S/B ni bienestar |
| `lem:repayment` | Cobertura de pago y patrimonio no negativo | `PostDeadlineCurrentPaperFive.lean`: `lemma_A11_repayment_paper`, desde `repaymentCurrent_exact`; Actions #46009434502 | **DEMOSTRADO EN LEAN PARA CADA ESTADO BAJO GARANTÍA ROBUSTA REAL**, incluyendo δ=0, cota inferior del patrimonio y estricta positividad si k'>0 o a>0. No prueba solvencia bancaria agregada |
| `lem:v0m_original_6_2` | Prohibición de préstamos y depósitos interiores simultáneos | `PostDeadlineCurrentPaperFive.lean`: `lemma_A12_interior_FOC_paper`, desde `noSimultaneousInteriorCurrent_exact`; Actions #46009434502 | **DEMOSTRADO EN LEAN BAJO LA SALVEDAD DE ESPERANZA DE SOPORTE FINITO**: probabilidad total uno, positividad casi segura en estados con peso positivo, dos FOC necesarias, β_E>0, R^L>R^D>0, μ≥0; no generaliza a distribuciones arbitrarias ni acredita suficiencia KKT |
| `prop:v0m_original_6_3` | Derivada de capital máximo financiable | `PostDeadlineCurrentPaperFive.lean`: `proposition_A13_financing_capacity_paper`, desde `financingCapacityCurrent_exact`; Actions #46009434502 | **DEMOSTRADO EN LEAN**: cota de capital bajo presupuesto y colateral, construcción factible que alcanza el máximo, `HasDerivAt` exacta y signo negativo, con n,q,H fijos al variar R^L. No prueba capital elegido óptimamente |
| `lem:allocation_loss_identity` | Referente eficiente y derivada de pérdida asignativa | `PostDeadlineCurrentPaperFive.lean`: `lemma_A14_physical_allocation_and_log_loss_paper`; desde `compactLemmaA14CurrentFull_exact`; Actions #46009434502 | **DEMOSTRADO EN LEAN PARA LA ECONOMÍA DE DOS FIRMAS DADA**: empleo óptimo, producción física, asignación eficiente factible, pérdida logarítmica no negativa, derivada total a lo largo de trayectorias de capital diferenciables y equivalencia MPK físico; no prueba equilibrio dinámico ni selección de ramas |

**Segunda actualización, POSTERIOR AL PLAZO, 27/11/2026:** los cinco resultados adicionales disponen de una interfaz paper-facing conjunta con cinco teoremas individuales y uno agregado en `PostDeadlineCurrentPaperFive.lean`, verificados por el kernel en [Actions #46009434502](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/46009434502), 8,343 trabajos y solo axiomas fundacionales. **Cobertura matemática acotada: ocho resultados con pruebas Lean en sus dominios explícitos (A.1.2: soporte finito).** NO significa ocho teoremas sobre el equilibrio SOURCE completo: la identificación económica de la Proposición 3.1 y de F0 con el Jacobiano sigue abierta; tampoco implica validación oficial `paper_contribution.py check --fast`. La adenda no altera la versión científica entregada el 26/11.

## Protocolo oficial y conciliación económica aún pendientes

1. Fijar commit del PDF definitivo y comprobar que coincide con las fuentes.
2. Se cotejaron los ocho enunciados completos con los Git blobs originales; conservar los tipos, signos, cuantificadores y salvedad de expectativa finita del Lema A.1.2. Queda independiente el cotejo oficial generado de AppliedModelingLib con su `PaperInterface` paper-scoped.
3. La tabla reporta ahora demostraciones exactas o condicionadas al dominio, separadas de la identificación de los objetos económicos y de la cobertura oficial. No inventar una ejecución completa de AppliedModelingLib.
4. **Completado solo el módulo adenda:** compilación kernel y auditoría de axiomas en Actions #46009434502. **Pendiente:** crear el paquete generado paper-scoped para el artículo de ocho resultados y ejecutar `python3 scripts/paper_contribution.py check Ventura26LiquidityAllocation --fast` sobre ese paquete, no sobre la interfaz histórica.
5. Incorporar la misma clasificación a la tabla dentro del PDF. La tabla ya está escrita en `paper/appendix_eight_results.tex`; necesita compilación PDF y revisión.

La matriz más amplia de 60 está preservada en `paper/lean_formalization_matrix_60.md` para trazabilidad y **no corresponde al alcance de la versión compacta**.


## Adenda manuscrita posterior al cierre del 26/11/2026

El [PDF auténtico de 12 páginas](../hand/ai-ieproject.pdf) ya está adjunto al repositorio, SHA-256 `14b081edf35c52882bd433021980a8beb12cdf805733aa4b4bca5839d9fcb8a1`. El [cotejo de los ocho resultados](../hand/AUDITORIA_ECUACIONES_MANUSCRITAS_8_20261127.md) y la [verificación numérica racional reejecutada](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/45933840987) confirman la cobertura y las cotas del F0 decimal. Las hojas llegaron después de las 22:00 de Lima; esta actualización no reescribe la cronología del PDF científico ya sometido.


## Certificación postplazo de los cinco resultados, sin atribución retroactiva

- [PR #77](https://github.com/alejandroventuraventurameza-tech/ai-project/pull/77) y [Actions #46009434502](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/46009434502): 5 endpoints + 1 conjunto; `#print axioms` solo `[propext, Classical.choice, Quot.sound]`, sin `sorryAx`; upstream `194edcc95df74806a39b961d10dedddc6e730cce` y Lean `v4.30.0-rc2`.
- [Adenda semántica](../docs/ADENDA_POSTPLAZO_CINCO_PRUEBAS_PAPER_20261127.md): hipótesis, conclusiones, fuentes originales e interpretación económica exacta.
- Los enunciados LaTeX originales no se modificaron; esta entrada es evidencia posterior al corte de las 22:00 del 26/11/2026.
