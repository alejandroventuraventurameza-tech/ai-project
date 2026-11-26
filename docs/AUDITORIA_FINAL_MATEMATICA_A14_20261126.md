# Auditoría final del núcleo matemático A.1.4 — 26 de noviembre de 2026

**Fuente científica congelada:** `ai-project@bac3c6255da39cd1169a965df35bb5e9a230e6e8`, etiqueta `lem:allocation_loss_identity`. **Compilador:** Lean 4.30.0-rc2. **Dependencia:** `nikhgarg/AppliedModelingLib@194edcc95df74806a39b961d10dedddc6e730cce`.

## Cadena de teoremas, sin sobreinterpretación

| Etapa | Declaración | Resultado |
|---|---|---|
| 1. Física y eficiencia | `sourceLemma43CompleteSpec_proved` | Once afirmaciones de fuente: empleo óptimo, frontera global alcanzable, pérdida desarrollada, derivada de expresión expandida, cuota física y MPK |
| 2. Logaritmo | `currentCompactLogLoss_exact` | `log(Yeff/Y)=log Yeff−log Y ≥ 0` bajo positividad y cota eficiente |
| 3. Composición | `compactLemmaA14Integrated_exact` | La cota `Y≤Yeff` se **deduce** del modelo físico, no se presupone |
| 4. Derivada agregada | `compactLossRatioAggregate_hasDerivAt` | Identifica la derivada del cociente `log(Yeff(s)/Y(s))` con la de la expresión desarrollada, mediante igualdad **eventual** en una vecindad |
| 5. Producción física | `compactLossRatioPhysical_hasDerivAt` | Sustituye `L^b G^(1-b)` por la producción Cobb–Douglas física de H y L, usando asignación óptima de trabajo |
| 6. Endpoint actual único | `compactLemmaA14CurrentFull_exact` | **Spec conjunto** `compactLemmaA14CurrentFullSpec` con todas las conclusiones anteriores y la derivada física |

**Prueba de las etapas 4–5:** [Actions #45858652855](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/45858652855), 8,338 trabajos, sin `sorryAx`, `#print axioms`: `[propext, Classical.choice, Quot.sound]`.

**Prueba del endpoint 6:** [Actions #45859315801](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/45859315801), 8,339 trabajos, sin `sorryAx`, `#print axioms`: `[propext, Classical.choice, Quot.sound]`.

**Validación numérica independiente ya existente:** `code/verify_compact_paper.py`, función `verify_allocation`: 80 casos reproducibles, diferenciación compleja para la derivada y equivalencia de signos entre participación en producto y MPK. Invocada desde `code/verify.py`. El test numérico no sustituye la demostración Lean.

## Hipótesis exactas y alcance

Las masas `vH,vL`, productividades `AH,AL`, trabajo total `L`, y elasticidades `a,b,d` son estrictamente positivas, con `a+b+d=1`. En el punto estudiado se exige `kH(t),kL(t)>0` y derivabilidad local de ambas trayectorias. De ahí se **deduce** positividad en una vecindad y se aplica `HasDerivAt.congr_of_eventuallyEq`, que transfiere la derivada solo cuando existe igualdad **entre funciones cerca del punto**, no solo igualdad de valores al impacto.

La identidad física vale para la dotación agregada de capital y trabajo con asignación laboral óptima. El parámetro real `s` es una dirección continua de variación para hacer cálculo diferencial; **no es el índice discreto de tiempo** del modelo monetario.

Bajo `ω_H>κ_H` y un cambio positivo en `log(k_H/k_L)`, la pérdida se reduce localmente. Esta condición es equivalente a `MPK_H>MPK_L` en el empleo óptimo; **no** se sigue de `A_H>A_L` sin analizar los stocks relativos.

## Regla de adjudicación pendiente

**DEMOSTRADO en Lean:** la especificación matemática descrita `compactLemmaA14CurrentFullSpec`, con sus cuantificadores y supuestos explícitos.

**NO CERTIFICADO:** identificación automática del enunciado con las estructuras `Allocation`/SOURCE, existencia de equilibrio dinámico infinito, efectos de política monetaria sobre crecimiento, suficiencia KKT del equilibrio total. No se ha ejecutado el protocolo oficial de `python3 scripts/paper_contribution.py check Ventura26LiquidityAllocation --fast` sobre un `PaperInterface` generado para el artículo actual. Los otros resultados 3.1, 5.1 y 5.2 siguen sin formalización literal actual. Manuscritos personales auténticos: **0/8**.

## Incidente de compilación transparente

La primera variante (#45857976522) falló por `Unknown identifier 𝓝` (ámbito de notación). Tras abrir `Filter` y `Topology`, las pruebas completaron compilación y auditoría de axiomas. El incidente no implicó cambiar las hipótesis ni suponer la conclusión.
