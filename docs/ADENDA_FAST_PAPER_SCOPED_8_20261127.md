# IE project — Adenda posterior al plazo: validación rápida paper-scoped de ocho resultados

**Fecha:** 27 de noviembre de 2026, Lima. Esta comprobación es posterior al plazo original de entrega académica del 26 de noviembre de 2026 a las 22:00; **no** altera retrospectivamente la versión presentada del artículo ni de los handnotes.

## Fuentes inmutables y compilación

- Artículo original cotejado: Git commit bac3c6255da39cd1169a965df35bb5e9a230e6e8. El inventario lean/current_paper_source_inventory_8.json se confrontó con sus ocho fragmentos LaTeX y sus Git blobs.
- Upstream AppliedModelingLib: 194edcc95df74806a39b961d10dedddc6e730cce, Lean v4.30.0-rc2.
- Auditoría conjunta: [Actions #46067342833](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/46067342833), satisfactoria: **8,357 trabajos** Lean, tres resultados principales y cinco paper-facing.
- Protocolo upstream rápido sobre paquete aislado: [Actions #46068856283](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/46068856283), satisfactorio: comando python3 scripts/paper_contribution.py check Ventura26LiquidityAllocation --fast, compilación adicional de Ventura26LiquidityAllocation.ProofInterface, **8,359 trabajos Lean** y ocho auditorías de axiomas.
- La interfaz del paquete se creó temporalmente mediante paper_contribution.py new --no-download. Se preparó un contrato provisional con ocho especificaciones y pruebas desde fuentes certificadas. Los módulos históricos que importaban la antigua PaperInterface se enlazaron a una copia LegacyPaperInterface solo en el runner CI para romper una dependencia circular. No se cambiaron cuerpos de demostraciones ni archivos fuente originales del proyecto.

## Ocho resultados paper-scoped verificados por el kernel

| Resultado del paper compacto | Endpoint de la prueba provisional | Alcance matemático |
|---|---|---|
| Proposición 3.1 | p31 | Multiplicidad local de una función escalar C¹; no recuperación SOURCE |
| Proposición 5.1 | p51 | Decaimiento uniforme de matriz decimal racional fija F0 |
| Lema 5.2 | l52 | Cota robusta para matrices reales 6×6 próximas a F0 |
| Proposición 5.3 | p53 | Cuña condicional de precios efectivos con garantía |
| Lema A.1.1 | a11 | Cobertura por estado y patrimonio no negativo |
| Lema A.1.2 | a12 | Imposibilidad de crédito y depósito interiores simultáneos para esperanza de soporte finito |
| Proposición A.1.3 | a13 | Capital máximo financiable y derivada parcial respecto de tasa crediticia |
| Lema A.1.4 | a14 | Producción física, frontera eficiente y derivada de pérdida asignativa |

El log imprime para los ocho endpoints únicamente [propext, Classical.choice, Quot.sound]; el workflow rechaza sorryAx, admit, errores y metas pendientes.

## Compilación correcta, pero no certificación semántica completa

**Confirmado:** el mismo comando oficial check --fast aprobó para un paquete paper-scoped provisional con ocho enunciados Lean y ocho endpoints cerrados. No es una ejecución del protocolo completo ni una aceptación de PR en el upstream público.

**Pendiente para cierre formal integral:**

1. Crear y validar el statement-spec oficial con fuente PDF anclada por SHA-256, ocho fragmentos semánticos y expansión del contenido de las definiciones referidas; el paquete rápido se generó expresamente sin ese contrato.
2. Concluir revisión independiente source-to-Spec, inventario de átomos originales, hipótesis extra y auditoría de procedencia de premisas. Las especificaciones económicas reutilizadas mediante alias transparentes aún necesitan cotejo completo; un nombre Lean no prueba equivalencia semántica.
3. Ejecutar protocolo no rápido, controles de closeout y prepare-pr solo cuando las obligaciones de su estatus científico estén satisfechas.
4. Demostrar, si se pretende una conclusión más fuerte, la identidad entre F0 y la dinámica SOURCE, la diferenciabilidad/inversa del Jacobiano económico 33×33 y los equilibrios dinámicos infinitos. Nada de ello se sigue de estos ocho endpoints.

**Conclusión delimitada:** la interfaz matemática rápida paper-scoped pasó y los ocho teoremas compilan sin huecos de prueba; la certificación integral del paper económico sigue pendiente. Mantener separadas ambas afirmaciones.
