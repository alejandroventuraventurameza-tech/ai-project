# IE Project 18 — lugar de ceros y Jacobiano SOURCE ante variaciones fiscales (12-XI-2026)

## Base demostrada

La revisión `2a1275728b470137196476bf9f8848c7048c6646` superó los ocho workflows principales. El módulo SOURCE `StationaryFiscalPrimitivesScopeCandidate.lean` contiene la igualdad comprobada de 33 filas al sustituir el par de datos estacionarios `(primitives G, inheritedState G)` por `(primitives H, inheritedState H)`, manteniendo iguales la rama B/S, las coordenadas `Z`, el calendario, la regla terminal `tail` y la base logarítmica `Z0` cuando proceda.

Este resultado no afirma que ambas economías completas tengan iguales bonos públicos, impuestos, restricciones bancarias u optimalidad.

## Nuevos lemas Lean sujetos a compilación

Los nuevos teoremas se agregaron al mismo módulo y al workflow `lean-stationary-policy-payment-bridge.yml`:

**Igualdad de derivadas del operador SOURCE:**
`stationaryFiscal_reducedLogJacobian_eq`.
Se reescribe la identidad de operadores logarítmicos dentro de `fderiv ℝ` en el origen de las 33 coordenadas. No se requiere invertibilidad para esta igualdad.

**Transporte del predicado de certificación:**
`stationaryFiscal_reducedLogJacobianCertified_iff`.
Se prueba, si el kernel acepta la reescritura, que el predicado fuente de diferenciabilidad en bola y existencia de una inversa acotada es equivalente para los dos valores `G,H`. No produce ninguna matriz inversa ni verifica las dos identidades de inversa.

**Invariancia del lugar de ceros reducido:**
`stationaryFiscal_reducedEquationsHold_iff`.
Se propone
`LocalReducedPrefixEquationsHold(branch, P(G), I(G), Z, ..., tail) ↔ LocalReducedPrefixEquationsHold(branch, P(H), I(H), Z, ..., tail)`.
Este enunciado conserva el candidato `Z` y no lo construye. Probar equivalencia del conjunto de ceros **no prueba que exista un cero**. Mucho menos demuestra la optimalidad ni una asignación completa de horizonte infinito.

Los tres lemas nuevos permanecen **PENDIENTES de kernel** hasta que el workflow del SHA con la nueva compuerta concluya con `success` y sin `sorryAx`.

## Compromisos de rigor

1. **DEMOSTRADO:** igualdad entre los operadores de 33 residuos reducidos SOURCE para las dos instancias estacionarias, bajo los argumentos comunes indicados (compilación `2a12757`).
2. **PENDIENTE CI:** igualdad de derivadas, equivalencia de predicado de inversa y equivalencia de lugares de ceros para variación real de `P(G)`.
3. **PENDIENTE matemática aplicada:** certificado estricto de invertibilidad del Jacobiano SOURCE instanciado y diferenciabilidad local; identidad funcional SOURCE-Python bajo estado fijo y continuación real; KKT y cierre fiscal; equilibrio de horizonte infinito; mecanismos causales y crecimiento permanente.

La oferta de bonos públicos sigue apareciendo en `governmentBondSupply` y en la completación de las cuentas fiscales. Por ello una invariancia de 33 filas **no** es una proposición de neutralidad de deuda, ni una equivalencia de bienestar.

Se conserva PR #2 en borrador; `main` no se fusiona.
