# IE Project 18 — primer puente de fila SOURCE real: pignoracion comun fecha uno

Revision inicial: `d7e7f8c8094e0b5e247bde681afa7383ff337819`.

## Evidencia anterior: algebra exacta verificada

El kernel Lean aprobo las seis identidades del modulo `NonlinearResidualRowmapExactCandidate.lean` en el commit `926da841add1857dd75bbee6455698ae1047fec8`, workflow [43271624157](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/43271624157), con comprobacion de axiomas. Estas identidades son sobre reales abstractos y no prueban identidad SOURCE/Python.

## Nueva instancia de la ecuacion economica original

El archivo `lean/candidates/Ventura26LiquidityAllocation/SourceCommonPledgeLogBridgeCandidate.lean` importa el modulo anterior y emplea expresamente `localReducedPrefixResidual` de `EconomicModel.lean`, en la fila `.commonPledgeOne`.

La definicion economica objetivo es

`A(P,Z,tail)=(1-P.depreciation) * (tail Z.stateTwo).inflation * (tail Z.stateTwo).capitalPrice`.

La fila economica SOURCE reducida es exactamente

`S_P = Z.stateTwo.commonPledgeValue - A(P,Z,tail)`.

La primera proposicion `sourceCommonPledgeResidual_exact_level` pretende establecer esa identidad por reduccion definicional del SOURCE verdadero. La segunda invoca la reconstruccion exacta

`A * (exp(log(1+S_P/A))-1) = S_P`

siempre que `A != 0` y `1+S_P/A>0`. La tercera pretende probar

`log(1+S_P/A)=0 ↔ S_P=0`

sobre el mismo dominio.

El coeficiente `A` tiene sentido economico: es el valor nominal de una unidad fisica de capital no depreciada al final de la ventana, usando la continuacion efectiva `tail`, no una constante impuesta desde Python. Por eso estas son las primeras pruebas que conectan de manera directa las identidades algebraicas de fila con una definicion **original** del SOURCE.

## Cautelas fundamentales

- El nuevo archivo contiene teoremas candidatos hasta que se complete el workflow Lean que lo compila. `#print axioms` esta activo y no se usa `sorry`.
- En esta etapa no se demuestra `A>0` a partir de la economia, sino que se exige el dominio pertinente. Una prueba posterior debe derivar esa positividad de las restricciones primitivas y del conjunto admisible.
- La igualdad de la fila SOURCE con una transformacion logaritmica no certifica su correspondencia con la fila 21 de Python ni que `tail` sea la grafica numerica `P0` en un abierto.
- El conjunto de ecuaciones SOURCE de equilibrio completo es mas amplio que estas 33 ecuaciones reducidas; existencia, KKT, cierre fiscal y crecimiento permanente siguen pendientes.

## Siguientes pasos concretos

Verificar la nueva compilacion con el kernel. Si pasa, extender el mismo tratamiento a los pares de filas de transicion bancaria, oferta laboral y Euler del hogar a fechas cero y uno, siempre leyendo `localReducedRemainingResidual` del SOURCE. En paralelo, preparar el mapeo de `LocalPrefixContinuationRule` a la regla terminal numerica y las hipotesis de positividad de la carta.

PR #2 permanece borrador. No fusionar main.
