# IE Project 18 — invariancia fiscal candidata del operador SOURCE de 33 filas (11-XI-2026)

## Hallazgo y verificaciones de partida

El commit `411db8f` pasó las ocho comprobaciones de GitHub Actions, incluyendo el módulo `StationaryFiscalFiberReducedPrefixCandidate`. Ello certifica los lemas de invariancia del estado heredado **a primitivas fijas**. El parche `dcceb99` corrigió el identificador de `reservesPre`, cuyo error original aparecía en el workflow fallido del commit `0f6fe30`.

La instancia `ProposedStationaryPrimitives.primitives G` define `governmentBondSupply := G` y mantiene expresiones comunes para los demás campos del registro. En `EconomicModel.lean` existe una distinción de arquitectura: los 33 residuos reducidos se construyen mediante `localReducedPrefixResidual`, mientras que las operaciones de completación fiscal incorporan explícitamente la oferta de bonos públicos para determinar `householdBonds`.

## Teoremas nuevos puestos a prueba

El módulo `StationaryFiscalPrimitivesScopeCandidate.lean` contiene ahora cinco candidatos, conectados a un workflow de compilación y auditoría de axiomas:

1. `stationaryPrimitives_only_bond_supply_changes`: los registros estacionarios difieren únicamente en `governmentBondSupply`.
2. `stationaryFiscal_dateZeroData_eq`: igualdad de los datos fecha cero al modificar a la vez `P(G)` e `I(G)`, con `Z` fijo.
3. `stationaryFiscal_dateOneData_eq`: igualdad del constructor de fecha uno con el mismo `Z` y `tail`.
4. `stationaryFiscal_reducedResidual_row_eq`: igualdad **fila por fila** de las 33 ecuaciones SOURCE entre las economías estacionarias `P(G),I(G)` y `P(H),I(H)`, bajo los mismos `Z,branch,tail`. La prueba candidata hace eliminación de casos de `LocalPrefixEquation` y pide verificar igualdad definicional de cada expresión.
5. `stationaryFiscal_reducedLogOperator_eq`: igualdad de las funciones log-residuales de 33 dimensiones a base `Z0` común, a partir del resultado por filas.

El workflow `lean-stationary-policy-payment-bridge.yml` exige la compilación Lean de estos teoremas, sus cinco resultados `#print axioms`, y rechaza `sorryAx` o pruebas no verificadas. **Ninguno de los cinco resultados nuevos debe llamarse DEMOSTRADO antes de observar un run exitoso del SHA actualizado.**

## Advertencias matemáticas y económicas

La igualdad de los operadores reducidos con dos valores de `G`, si el kernel confirma las pruebas, constituye una propiedad formal de un **modelo concreto de primitivas estacionarias**, no una proposición universal sobre cambios fiscales. En el modelo económico original persisten dependencias de `G` en tenencias de bonos públicos, presupuesto fiscal y restricciones de equilibrio. El resultado no implica equivalencia de equilibrio completo, neutralidad fiscal ni insensibilidad de bienestar.

Tampoco se han identificado las primitivas SOURCE con el código Python sobre una vecindad abierta ni demostrado el enlace de continuación recurrente o la inversa del Jacobiano económico concreto. Esta igualdad, si se confirma, puede reducir considerablemente las obligaciones del puente de Jacobiano, pero **no proporciona el certificado numérico de inversa**.

## Ruta de cierre

Primero revisar el resultado del kernel del SHA `17bf5346...` y, si falla, leer los registros reales del job para corregir exactamente el contraejemplo de definiciones. Luego construir la correspondiente igualdad del predicado `LocalReducedPrefixLogJacobianCertifiedAt` para `P(G)` y `P(H)`, sin presentar un testigo inexistente. Finalmente abordar el operador SOURCE instanciado con `tail` genuino, la validación numérica dirigida y las condiciones de equilibrio completo.

PR #2 permanece draft; `main` no se fusiona.
