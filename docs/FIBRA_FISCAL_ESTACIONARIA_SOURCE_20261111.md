# IE Project 18 — fibra fiscal de deuda publica en el estado heredado SOURCE (11-XI-2026)

## Pregunta

El registro `ProposedStationaryInheritedState.inheritedState G` es una instancia económica concreta de `InheritedState`. ¿Qué ocurre al sustituir el parámetro de deuda pública inicial `G` por `H` sin modificar las primitivas y la continuación que consume el sistema reducido de 33 residuos?

La respuesta propuesta se desarrolla en el nuevo módulo Lean `StationaryFiscalFiberReducedPrefixCandidate.lean`, que importa el archivo SOURCE estacionario y los teoremas de extensionalidad ya compilados.

## Cuatro lemas nuevos

**(1) Independencia de cinco campos heredados respecto de G.** Mediante reducción de definiciones se exhiben las igualdades exactas de `capital`, `firmFace`, `bankFace`, `reserveRateLag` y `reservesPreLag` al sustituir `G` por `H`. Son cinco campos estructurales, que expanden a siete escalares del prefijo.

**(2) Diferencia explícita de bonos domésticos.** La misma sustitución NO deja el estado heredado completo invariante, pues

`inheritedState(G).householdBonds - inheritedState(H).householdBonds = G-H`.

Por ello, `G≠H` cambia el saldo de bonos, y la proyección reducida descarta información fiscal real. Este resultado impide afirmar que ambos equilibrios completos son idénticos.

**(3) Igualdad funcional del log-residual SOURCE.** Fijando **la misma instancia de Primitives P**, la misma rama financiera, la base de coordenadas, las fechas `.dateOne` y `.recurrent` y la misma continuación `tail`, el nuevo teorema concluye igualdad de las funciones log-residuales de 33 filas que usan `inheritedState G` y `inheritedState H`.

**(4) Transporte condicional del certificado de inversa.** Bajo esas mismas hipótesis, el predicado SOURCE de diferenciabilidad, dos identidades de inversa y cota estricta de norma para el Jacobiano es equivalente al reemplazar G por H. La conclusión no contiene un testigo de inversa nuevo.

## Restricción conceptual que no puede omitirse

El lema de igualdad funcional **mantiene fija la instancia P**. No afirma que `primitives G = primitives H`; cada una puede codificar distintas condiciones fiscales y de transferencias. Tampoco mantiene necesariamente la factibilidad fiscal de ambas economías, porque la deuda de los hogares cambia.

En particular, sería ilegítimo concluir `F(P(G),I(G))=F(P(H),I(H))` a partir del lema `F(P,I(G))=F(P,I(H))` sin probar de forma adicional la igualdad de todas las primitivas utilizadas por el operador.

## Aseguramiento de calidad

El workflow `lean-stationary-policy-payment-bridge.yml` restaura el SOURCE fijado, compila `StationaryFiscalFiberReducedPrefixCandidate`, exige cuatro salidas `#print axioms` y rechaza `sorryAx` y `unsound`. **Estado actual del módulo: pendiente de compilación en CI del commit que lo introdujo.** No catalogar estas cuatro proposiciones como DEMOSTRADO antes de un run verde por SHA exacto.

## Siguiente tarea científica

Probar si la restricción sobre P puede relajarse a igualdad solamente de los campos `Primitives` que efectivamente consume cada una de las 33 ecuaciones, incluyendo el tratamiento de `G` en el cierre fiscal; estudiar luego un operador SOURCE instanciado y el residuo de transporte a Python, validando el mismo `tail`. La certificación de la inversa del Jacobiano económico sigue abierta.

PR #2 sigue draft. No fusionar main.
