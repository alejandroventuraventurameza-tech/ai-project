# IE Project 18 — corrección compilada de la fibra fiscal y alcance de primitivas (11-XI-2026)

## Incidencia identificada en el CI original

El workflow [43135460698](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/43135460698), correspondiente al commit `0f6fe30db3c2f12ca1bfef8ad0b5a1e90443bf92`, terminó con **failure** en el target `StationaryFiscalFiberReducedPrefixCandidate`. Se recuperó el registro de errores completo. Lean indicó `Unknown identifier ProposedStationaryInheritedState.reservesPre` en las líneas de la identidad del saldo de bonos. La consecuencia fue un `sorryAx` transitorio en ese teorema: por tanto no era aceptable llamarlo demostrado, pese a que los otros tres lemas del módulo imprimían axiomas fundacionales habituales.

La definición efectiva de `reservesPre` está en `ProposedStationaryRealScale`, en `StationaryRealScaleCandidate.lean`. El commit `dcceb9935c0a175257ce1d9e7337be04c1bfc51e` corrige ambas referencias al nombre plenamente calificado `ProposedStationaryRealScale.reservesPre`. **Estado:** parche enviado; verificar nuevo run antes de declarar el módulo completo como DEMOSTRADO.

## Separación entre variaciones del estado y de las primitivas

La instancia estacionaria `ProposedStationaryPrimitives.primitives G` incluye la deuda como `governmentBondSupply := G`. En consecuencia:

`primitives(G)` y `primitives(H)` son registros distintos cuando `G≠H`.

El teorema de invariancia del operador reducido que hemos construido conserva **la misma instancia `P` a ambos lados**:

`F(P,I(G),z)=F(P,I(H),z)`.

No establece automáticamente

`F(primitives(G),I(G),z)=F(primitives(H),I(H),z)`.

Aunque `governmentBondSupply` no se lea literalmente en el despachador de las 33 filas, hay dependencias transitivas a través de funciones auxiliares de `Primitives` que es necesario auditar antes de extender el teorema. La igualdad de funciones económicas bajo un cambio real de deuda requiere probar que esas funciones auxiliares no dependen de `governmentBondSupply`, o aportar una hipótesis de equivalencia restringida de primitivas.

## Interpretación científica

El sistema de prefijo reducido mantiene las posiciones relevantes `capital`, `firmFace`, `bankFace`, `reserveRateLag` y `reservesPreLag`. La identidad `householdBonds(G)-householdBonds(H)=G-H` muestra expresamente lo que esa proyección descarta. Por ello **no** se concluye neutralidad fiscal, equivalencia de los presupuestos o igualdad de los equilibrios completos.

El resultado útil que ya superó el kernel consiste en transportar residuos, derivadas y el predicado condicional de certificación **cuando `P` se mantiene fijo**. El paso siguiente es demostrar qué componentes de `P` son económicamente necesarios para cada residuo y, solo después, intentar relajar esa hipótesis.

PR #2 debe seguir en borrador; `main` no se fusiona.
