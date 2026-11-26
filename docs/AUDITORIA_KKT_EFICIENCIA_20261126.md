# Auditoría dirigida de KKT y eficiencia asignativa — 26/11/2026

**Fuente económica:** `paper/appendix_eight_results.tex` de la revisión científica `bac3c6255da39cd1169a965df35bb5e9a230e6e8`. **Control:** main posterior a `0f13b880`. Informe académico dirigido, **no** certificación de equivalencia literal source-to-Lean ni chequeo oficial paper-scoped.

## A. Lema A.1.2: posiciones interiores incompatibles

**Enunciado fuente:** `lem:v0m_original_6_2`. Con `R^L>R^D>0`, `β_E>0`, `Π'>0`, `V'_N>0` casi seguramente, expectativas finitas y dual `μ≥0`, las FOC de depósitos y deuda, suponiendo `a,b>0`, implican
`0=β_E E[V'_N (R^L-R^D)/Π'] + μ R^L`, imposible porque la primera suma es positiva y la segunda no negativa.

**Lean:** `lean/candidates/Ventura26LiquidityAllocation/CurrentCompactInteriorKKT.lean`. `expectedRealMarginal` expresa la expectativa como suma sobre `W` finito. `expectedRealMarginal_pos` prueba positividad con probabilidades no negativas, masa total uno y positividad de `V'_N` y `Π'` únicamente sobre estados de peso positivo. `expectedRealMarginal_rateFactorization` retira tasas brutas constantes respecto de `w`. `noSimultaneousInteriorCurrent_exact` deduce contradicción cuando se imponen ambas FOC. Kernel: [Actions #45851966286](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/45851966286), sin `sorryAx`.

**Cotejo:** los signos, el término dual y las dos FOC son fieles al lema; el uso de `a>0,b>0` está condicionado a las FOC como hipótesis y no se construye una solución empresarial. **Diferencia relevante:** las expectativas finitas del paper permiten, en principio, un espacio probabilístico más general, mientras Lean prueba el caso de soporte finito `Fintype W`. Es una especialización válida, no una equivalencia universal del texto sin demostrar que el árbol SOURCE sea finito por período y que su expectativa coincida con esta suma. La condición `μ≥0` y la posición interior no certifican suficiencia KKT, concavidad global ni ausencia de arbitraje en un sistema dinámico distinto.

**Decisión de auditoría:** DEMOSTRADO en Lean para el Spec de soporte finito; PENDIENTE puente del árbol de estados, cuantificadores y la identificación formal del enunciado original.

## B. Lema A.1.4: referencia eficiente y pérdida asignativa

**Fuente:** `lem:allocation_loss_identity`, con `v_i,A_i,k_i,L,α,β,d>0`, `d=1-α-β`, `Y_i=A_i k_i^α ℓ_i^β`, capital y trabajo agregados con masas `v_i`. El empleo óptimo implica `Y=L^βG^{1-β}`; la reasignación conjunta de capital y trabajo alcanza `Yeff=K^α L^β ZA^d ≥ Y`, `ℒ=log(Yeff/Y)≥0`, y, en trayectorias diferenciables positivas, `dℒ=α(κ_H-ω_H)d log(k_H/k_L)`. Además, `ω_H>κ_H ↔ MPK_H>MPK_L`.

**Lean histórico:** `lean/candidates/Ventura26LiquidityAllocation/PaperLemma43SourceCompleteCandidate.lean`, `sourceLemma43CompleteSpec_proved`. La especificación conecta **once** cláusulas para las mismas firmas, masas y parámetros: empleo positivo y recurso laboral; producción agregada; cota de producto para toda asignación factible; asignación que alcanza la frontera; pérdida no negativa; fórmula logarítmica; optimalidad laboral; regla de la cadena para la pérdida; derivada del logaritmo de razón de capitales; participación de H en producto físico; equivalencia con MPK. Compilación kernel [Actions #45847597337](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/45847597337), sin `sorryAx`.

**Cotejo:** las hipótesis numéricas `a+b+d=1` con `a,b,d>0` reproducen `d=1-α-β>0`. La conclusión Lean sobre pérdida escribe `Real.log Yeff - Real.log Y`, mientras la definición literal del paper es `Real.log (Yeff/Y)`. Como ambas cantidades son estrictamente positivas bajo las hipótesis, la equivalencia se obtiene por la identidad logarítmica correspondiente; **ese puente debe incorporarse explícitamente** a la interfaz del artículo vigente. La cláusula de dirección diferencial utiliza `HasDerivAt` de caminos de capital, no acredita que sean caminos de equilibrio monetario.

**Decisión de auditoría:** DEMOSTRADO históricamente en Lean el paquete algebraico, estático y diferencial de once cláusulas; PENDIENTE interfaz exacta del paper compacto, puente logaritmo del cociente y verificación independiente de la semántica. No elevar al estado de equilibrio dinámico ni causalidad de las IRF.

## Prioridades restantes

1. Generar Spec source-locked para ocho resultados y establecer puentes explícitos sin presuponer las conclusiones.
2. Cerrar `Real.log (Yeff/Y) = Real.log Yeff - Real.log Y` bajo positividad y vincularlo al paquete histórico.
3. Vincular árbol de estados y expectativa del Lema A.1.2 con su definición fuente.
4. Demostrar o delimitar los resultados macro y matriciales 3.1, 5.1 y 5.2; no confundir Python racional con formalización Lean.
5. Ejecutar en entorno oficial `python3 scripts/paper_contribution.py check Ventura26LiquidityAllocation --fast`.
6. Incorporar ocho manuscritos genuinos del autor (estado actualmente registrado 0/8).

**Este archivo documenta comparación manual de enunciados y código, no una nueva ejecución de Lean.**
