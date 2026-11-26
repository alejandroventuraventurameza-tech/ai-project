# Cotejo dirigido: tres resultados financieros del artículo compacto

**Fecha:** 26/11/2026. **Fuente científica fijada:** `paper/paper.tex` y archivos incluidos, revisión `bac3c6255da39cd1169a965df35bb5e9a230e6e8`. **Último main inspeccionado:** `7a0dcc992b290ff6bc2069e676e6a778c97a4a56`. **Tipo de documento:** auditoría semántica dirigida, no certificado paper-scoped oficial.

## Evidencia del kernel y alcance

El workflow [#45851966286](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/45851966286) verificó cuatro endpoints actuales sin `sorryAx`. Este cotejo examina tres: `repaymentCurrent_exact`, `financingCapacityCurrent_exact`, `effectiveWedgeCurrent_exact`. El hecho de que compilen no sustituye la identificación con estados del modelo económico, ni el chequeo oficial de AppliedModelingLib.

## 1. Lema A.1.1 (`lem:repayment`)

**Fuente:** `paper/appendix_eight_results.tex`. Supuestos: `0 ≤ δ < 1`, `0 ≤ θ_i < 1`, `R^L,R^D,Π',q' > 0`, `a,b,k' ≥ 0`, `πop' ≥ 0` en cada estado admisible y `R^L b/Π' ≤ θ_i(1-δ)q'k'`. Conclusiones: cota inferior explícita de patrimonio, `N' ≥ 0` y `N' > 0` si `k' > 0` o `a > 0`.

**Lean:** `CurrentCompactWedgeRepayment.lean`, `repaymentCurrentSpec`. Cuantifica sobre reales y exige los mismos signos; permite `δ=0`. Las variables `loan,deposit,capitalNext,operatingProfit` corresponden a `b,a,k',πop'`. La expresión `lowerBound` es la cota utilizada en la prueba fuente y las tres conclusiones están expresadas en la conjunción Lean.

**Veredicto dirigido:** correspondencia algebraica y de signos consistente, incluidos los casos de frontera `δ=0`, `k'=0` y `a=0`. **Puente abierto:** cuantificar sobre *cada estado admisible* requiere conectar el teorema real-paramétrico con los contratos contingentes del modelo y sus estructuras fuente. No se establece solvencia bancaria.

## 2. Proposición A.1.3 (`prop:v0m_original_6_3`)

**Fuente:** `paper/appendix_eight_results.tex`. Escribe `n=N-c-a>0`, `q,H,R^L>0`, `q>H/R^L`, `qk'=n+b`, `R^Lb≤Hk'` y `b,k'≥0`. El máximo factible es `n/(q-H/R^L)`, se alcanza con la garantía igualada y su derivada parcial en `R^L`, fijando `n,q,H`, es estrictamente negativa.

**Lean:** `CurrentCompactFinancingCapacity.lean`, `financingCapacityCurrentSpec`. Identifica `ownResources=n`, `capitalPrice=q`, `collateral=H`, `loanRate=R^L`. Prueba por separado: cota para toda pareja factible, existencia de cartera no negativa alcanzando la cota, derivada `HasDerivAt` y signo estricto.

**Veredicto dirigido:** las obligaciones algebraicas y de factibilidad están representadas; **puente abierto:** demostrar que `n=N-c-a` y `H` de la estructura fuente corresponden a estos parámetros bajo los regímenes apropiados. La prueba no establece elección óptima ni un efecto de equilibrio general.

## 3. Proposición 5.3 (`prop:compact_source_collateral_effective_wedge`)

**Fuente:** `paper/body_compact_after.tex`. Supuestos: misma `R_t^L>0`, `δ<1`, `Π_{t+1},q_{t+1}>0`, `θ_H<θ_L`. Define `J=(1-δ)Π_{t+1}q_{t+1}`, `p_i^{eff}=q_t-θ_i J/R_t^L` y concluye `p_H^{eff}-p_L^{eff}=(θ_L-θ_H)J/R_t^L>0`.

**Lean:** `CurrentCompactWedgeRepayment.lean`, `effectiveWedgeCurrentSpec`. Incluye las mismas premisas de signo y orden, el precio común del capital que se cancela, la identidad y su positividad.

**Veredicto dirigido:** identidad algebraica consistente. **Distinción de alcance:** la igualdad entre precios *definidos* es independiente de si las garantías vinculan; que `p_i^{eff}` represente el costo marginal relevante de la empresa requiere la igualdad del colateral y la reducción del presupuesto. En la rama S, donde L tiene holgura, no debe presentarse como costo marginal efectivo observado de L. El `Spec` tampoco expresa la identidad de cambios logarítmicos `Δlog W=Δlog J-Δlog R^L`, que es una consecuencia adicional bajo positividad y una comparación de trayectorias.

## Conclusión y siguiente compuerta

**Tres correspondencias matemáticas dirigidas consistentes; cero certificaciones de equivalencia fuente–Lean integral otorgadas por este informe.** La auditoría independiente debe verificar la representación de variables indexadas por empresa, tiempo y estado, el régimen activo, la identidad de `J` y la correspondencia de dominios. No modificar los `Specs` añadiendo las conclusiones como premisas.

**Siguiente secuencia:** cotejar `noSimultaneousInteriorCurrentSpec` con el árbol de soporte finito; cotejar el módulo integrado del Lema A.1.4 con el referente eficiente del PDF; formalizar o delimitar los resultados 3.1, 5.1 y 5.2; ejecutar `python3 scripts/paper_contribution.py check Ventura26LiquidityAllocation --fast` en el entorno oficial; incorporar ocho manuscritos auténticos con veredicto del autor.
