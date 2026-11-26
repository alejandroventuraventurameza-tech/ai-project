# IE Project 18 — alcance de las primitivas fiscales en SOURCE (11-XI-2026)

## Compilación previa recuperada

El workflow original de la fibra fiscal en `0f6fe30` falló por una referencia mal calificada a `reservesPre`. Se corrigió en `dcceb99`. En `411db8f`, las ocho ejecuciones principales, incluido el target Lean de fibra fiscal, registraron `success`. Se conservan los cuatro lemas: igualdad de los cinco campos heredados, diferencia de bonos de hogares, invariancia logarítmica con `P` fijo y equivalencia condicional del predicado de certificación.

## Nueva pregunta formal

La instancia estacionaria `ProposedStationaryPrimitives.primitives G` construye una estructura `Primitives LocalBridgePhase` y especifica `governmentBondSupply := G`. En el archivo fuente de ese constructor, los demás campos de la estructura se generan a partir de definiciones comunes que no toman `G` como parámetro.

Se propone, en `StationaryFiscalPrimitivesScopeCandidate.lean`, la igualdad de registros concreta

`primitives G = { primitives H with governmentBondSupply := G }`.

A diferencia de la invariancia heredada anterior, este enunciado **explicita dónde entra la deuda pública en las primitivas**. La prueba candidata es por igualdad definicional `rfl`; su validez está pendiente de comprobar por Lean.

## Compuertas intermedias

En lugar de afirmar directamente la igualdad de las 33 funciones, el nuevo módulo propone además dos lemas sobre los **constructores de datos**:

`localPrefixDateZeroData (primitives G) (inheritedState G) Z .dateOne = localPrefixDateZeroData (primitives H) (inheritedState H) Z .dateOne`

y

`localPrefixDateOneData (primitives G) Z .dateOne .recurrent tail = localPrefixDateOneData (primitives H) Z .dateOne .recurrent tail`.

Ambos mantienen fijos `Z` y `tail`. Estos son pasos de identificación de entradas; si el kernel los acepta, todavía falta probar que **las funciones auxiliares que generan los residuos** no leen la oferta de bonos públicos mediante otras vías.

El workflow `lean-stationary-policy-payment-bridge.yml` comprueba los tres lemas, imprime sus axiomas y rechaza `sorryAx`. No considerar sus enunciados `DEMOSTRADO` hasta una ejecución verde del SHA.

## Alcance económico

El hecho de que la oferta de bonos públicos no cambie algunos datos del prefijo reducido no implica que un cambio de deuda pública sea irrelevante para impuestos, tenencias de activos de hogares, política fiscal o equilibrio completo. La conclusión válida necesita distinguir el **operador reducido con datos compartidos** de dos economías completas con `P(G)` y `P(H)` distintos.

Además, la igualdad de constructores de fecha cero y uno, aunque se demuestre, no valida una inversa del Jacobiano SOURCE ni la correspondencia completa SOURCE–Python. El siguiente paso es una extensionalidad del operador de 33 residuos ante `governmentBondSupply` fijando todos los demás campos, y después buscar el certificado de Jacobiano económico bajo la continuación real.

PR #2 sigue en borrador; no fusionar `main`.
