# Cierre parcial de integración del Lema A.1.4 (26/11/2026)

**Objeto:** Lema A.1.4 del artículo compacto, etiqueta `lem:allocation_loss_identity`. **Fuente científica:** `ai-project@bac3c6255da39cd1169a965df35bb5e9a230e6e8`. **Lean:** `4.30.0-rc2` y `nikhgarg/AppliedModelingLib@194edcc95df74806a39b961d10dedddc6e730cce`.

## Prueba comprobada

**Declaración:** `Ventura26LiquidityAllocation.CurrentCompact.compactLemmaA14Integrated_exact`.
**Código:** `lean/candidates/Ventura26LiquidityAllocation/PaperLemma43CompactIntegratedCandidate.lean`.

Con las mismas firmas H/L, las masas y productividades estrictamente positivas, las elasticidades `a,b,d>0` con `a+b+d=1`, los capitales en t estrictamente positivos y las trayectorias diferenciables, la especificación agrupa:

1. Las once conclusiones matemáticas del `sourceLemma43CompleteSpec` histórico: empleo óptimo, producción agregada, frontera eficiente global y alcanzable, pérdida no negativa, fórmula logarítmica, derivada de la expresión expandida, derivada de la razón de capitales, identidad de participación de producto y orden de MPK.
2. `Real.log (Yeff / Y) = Real.log Yeff - Real.log Y`.
3. `0 ≤ Real.log (Yeff / Y)`.

**No hay supuesto adicional `Y≤Yeff` en el teorema final.** Este vínculo se deduce de la cláusula de cota física global del paquete histórico, aplicándola a la asignación laboral óptima, luego se aplica la prueba autónoma del cociente logarítmico.

La compilación íntegra produjo el mensaje `A14_INTEGRATED_LEAN_OK` y `Build completed successfully (8336 jobs)` en [Actions #45856710241](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/45856710241). `#print axioms` informó `[propext, Classical.choice, Quot.sound]`, sin `sorryAx`. Los controles generales `build` y `editorial-qa` de la misma revisión también aprobaron.

## Brechas que persisten

- **Identidad funcional por trayectorias: CERRADA EN LEAN.** `compactLossRatioAggregate_hasDerivAt` y `compactLossRatioPhysical_hasDerivAt` prueban la igualdad de funciones en una vecindad, usando continuidad y positividad local de los capitales, y transfieren la derivada al cociente construido con las producciones físicas. [Actions #45858652855](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/45858652855), sin `sorryAx`.
- **Especificación unificada A.1.4: CERRADA EN LEAN PARA SU DOMINIO MATEMÁTICO.** `compactLemmaA14CurrentFullSpec` y `compactLemmaA14CurrentFull_exact` integran once cláusulas históricas, log cociente, no negatividad y derivada física. [Actions #45859315801](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/45859315801), 8,339 trabajos; axiomas `[propext, Classical.choice, Quot.sound]`. El parámetro diferenciable es una reasignación continua auxiliar, no el calendario discreto del DSGE.
- **Semántica de estado y agentes:** no existe todavía un `PaperInterface` paper-scoped del artículo vigente que conecte esta formulación estática con las estructuras `Allocation` y la dinámica SOURCE.
- **Modelo financiero:** la integración no demuestra existencia/optimalidad de equilibrio competitivo infinito, ni signo causal de IRF, ni crecimiento sostenido.
- **Entrega:** el procedimiento `python3 scripts/paper_contribution.py check Ventura26LiquidityAllocation --fast` sigue sin constancia de ejecución sobre el paquete generado oficialmente, y las ocho hojas manuscritas auténticas siguen pendientes en `hand/`.

**Clasificación:** DEMOSTRADA en Lean la especificación matemática completa de A.1.4, incluyendo la derivada del cociente físico bajo las hipótesis explícitas; PENDIENTE correspondencia paper–Lean oficial con el modelo dinámico SOURCE y formalización paper-scoped de los ocho resultados. No confundir con existencia de equilibrio infinito.
