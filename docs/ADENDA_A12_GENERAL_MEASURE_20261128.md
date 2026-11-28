# Adenda de investigación: Lema A.1.2 sin soporte finito

**Fecha:** 28/11/2026. Desarrollo **posterior** a la entrega del 26/11/2026; no modifica el manuscrito académico congelado, sus PDF ni los handnotes.

## Objeto y extensión

La fuente original `ai-project@bac3c6255da39cd1169a965df35bb5e9a230e6e8`, `paper/appendix_eight_results.tex`, Lema A.1.2, declara una distribución condicional con `V'_N>0` casi seguramente, inflación siguiente positiva y expectativas finitas. La formalización previa `CurrentCompactInteriorKKT.lean` reemplazaba estas expectativas por sumas sobre `Fintype W`, lo cual demostraba la conclusión bajo una condición de soporte finito.

El nuevo módulo `lean/candidates/Ventura26LiquidityAllocation/CurrentCompactInteriorGeneralMeasure.lean` propone:

- Un espacio de estados arbitrario `Ω` dotado de una `MeasurableSpace` y una `Measure μ` con `IsProbabilityMeasure μ`; **no** presupone `Fintype Ω` ni soporte finito.
- `0 < marginalValue ω` y `0 < inflationNext ω` **casi seguramente** bajo `μ`, sin exigencia de validez punto a punto en estados nulos.
- Integrabilidad de `ω ↦ marginalValue ω / inflationNext ω` bajo `μ`, equivalente a la finitud absoluta de la expectativa real que aparece en las FOC cuando las tasas brutas fijas son positivas.
- `β_E>0`, `R^L>R^D>0`, multiplicador dual de colateral no negativo, ambas posiciones interiores y las **dos ecuaciones necesarias de primer orden** como hipótesis, con `λ` común.

La prueba tiene tres piezas: (1) la integral del marginal real es estrictamente positiva por positividad casi segura, integrabilidad y medida total uno; (2) las tasas brutas constantes salen de ambas integrales; (3) el spread positivo implica `β_E E[R^D V'_N/Π'] < β_E E[R^L V'_N/Π'] ≤ β_E E[R^L V'_N/Π']+μ R^L`, contradicción con ambas FOC.

## Evidencia y límites

**Estado al abrir esta adenda:** CANDIDATO, prueba Lean enviada a [GitHub Actions #46175766176](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/46175766176). No declarar `DEMOSTRADO` hasta que la compilación del teorema `noSimultaneousInteriorGeneral_exact` y la auditoría `#print axioms` concluyan exitosamente.

Incluso al certificar el teorema general, **no se habrán demostrado** la existencia o suficiencia de condiciones KKT de la firma, la realización de los integrandos desde la economía SOURCE 33×33, la medición/calibración económica, la identificación F0–Jacobiano ni un equilibrio dinámico con condición terminal. Esta es una extensión de la **implicación lógica entre las FOC**, no la construcción de las FOC dentro del modelo completo.

## Puertas de integración

1. Comprobar sintaxis, tipos y el teorema general bajo el upstream anclado `194edcc95df74806a39b961d10dedddc6e730cce` y Lean `v4.30.0-rc2`.
2. Verificar dependencia exclusivamente de axiomas fundacionales, sin `sorryAx`, `axiom` nuevo ni `admit`.
3. Comparar cuantificadores, integrabilidad y casi-seguridad con el texto original y registrar cualquier premisa más fuerte.
4. Conservar la prueba finita y el PDF entregado inalterados; solo después aprobar y fusionar una adenda posterior al plazo.
