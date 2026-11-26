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

- **Identidad funcional por trayectorias:** el paquete histórico demuestra `HasDerivAt` de la pérdida *expandida*. Falta demostrar localmente, cerca de t, que esa expresión coincide con `s ↦ log(Yeff(s)/Y(s))` para el empleo óptimo inducido por capital positivo. La identidad puntual del logaritmo verificada aquí no basta por sí sola para identificar derivadas de dos funciones.
- **Semántica de estado y agentes:** no existe todavía un `PaperInterface` paper-scoped del artículo vigente que conecte esta formulación estática con las estructuras `Allocation` y la dinámica SOURCE.
- **Modelo financiero:** la integración no demuestra existencia/optimalidad de equilibrio competitivo infinito, ni signo causal de IRF, ni crecimiento sostenido.
- **Entrega:** el procedimiento `python3 scripts/paper_contribution.py check Ventura26LiquidityAllocation --fast` sigue sin constancia de ejecución sobre el paquete generado oficialmente, y las ocho hojas manuscritas auténticas siguen pendientes en `hand/`.

**Clasificación:** DEMOSTRADO en Lean el paquete integrado descrito; PENDIENTE equivalencia literal integral paper–Lean del Lema A.1.4 y formalización paper-scoped del conjunto de ocho resultados.
