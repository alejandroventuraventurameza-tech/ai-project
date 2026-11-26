# IE Project 18 — primeras inversas exactas de filas en Lean (12-XI-2026)

## Evidencia numérica anterior

El workflow `build` del SHA `08d8c7238cfde795578555f508bdc2a158778960` superó el job `Run code/verify.py`, run [43271150245](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/43271150245). En ambas ramas, el auditor de la transformación inversa de 33 residuos SOURCE-shaped registró `1.7763568394002505e-15` de máximo error de reconstrucción en ambos sentidos y `1.1102230246251565e-16` para cada producto matriz-inversa.

Estas cifras corresponden a la *transformación de filas transcritas en Python*, no al Jacobiano económico original SOURCE. Su eventual exactitud matemática no deriva automáticamente de esa evidencia numérica.

## Seis lemas exactos introducidos al kernel de Lean

Se añadió `lean/candidates/Ventura26LiquidityAllocation/NonlinearResidualRowmapExactCandidate.lean` y se conectó a `lean-stationary-policy-payment-bridge.yml`, con seis declaraciones `#print axioms` y rechazo explícito de `sorryAx`.

Los lemas se formulan en `ℝ` y demuestran únicamente el algebra de la transformación de filas, con argumentos de coeficientes y residuos **arbitrarios** y condiciones explícitas de denominador o dominio:

- `scalarLogLevel_roundtrip`: `log(1+d*(exp p-1)/d)=p` para `d≠0`.
- `scalarLevelLog_roundtrip`: `d*(exp(log(1+s/d))-1)=s` para `d≠0` y `1+s/d>0`.
- `negativeScalarLogLevel_roundtrip`: versión para la fila SOURCE `1-r`, escrita `-d*(exp p-1)`.
- `negativeScalarLevelLog_roundtrip`: inversa negativa con `1-s/d>0`.
- `pledgeEulerShear_roundtrip` y `pledgeEulerShear_reverse_roundtrip`: identidades inversas exactas de `p_E↔p_E+a*(exp(p_P)-1)` para `a,p_P∈ℝ`.

La versión económica de estas expresiones requiere adicionalmente (d_i(z)>0) y (a_i(z)) calculados mediante definiciones del SOURCE original, con la misma carta y el mismo `tail`. Estos seis lemas son bloques abstractos, **no** equivalencias SOURCE/Python ni prueba de que los 33 campos económicos se identifican.

**Estado de los seis lemas:** PENDIENTE DE KERNEL hasta observar `success` de la nueva revisión del workflow Lean. No se informarán como DEMOSTRADO antes de ese resultado.

## Siguiente paso formal

1. Verificar los lemas por kernel Lean en el workflow fijado (sin axiomas extra ni `sorry`).
2. Sustituir las transcripciones SOURCE-shaped de los nueve residuos escalares y de las dos cizallas Euler por instancias de `localReducedPrefixResidual` del SOURCE, declarando las hipótesis de positividad de las razones.
3. Comprobar las 16 identidades restantes de filas directamente sobre las definiciones Lean y su carta, sin reutilizar una igualdad numérica.
4. Probar la equivalencia de la regla terminal SOURCE `LocalPrefixContinuationRule` y la grafica `P0` de Python, en un vecindario de la raíz.
5. Solo después trasladar un certificado riguroso de inversa al Jacobiano económico SOURCE. Ninguna de estas nuevas pruebas implica KKT, equilibrio completo o crecimiento de largo plazo.

PR #2 sigue draft y `main` no está fusionado.
