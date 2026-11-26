# IE Project 18 — transporte condicional del predicado de certificación SOURCE (11-XI-2026)

## Hecho verificado en la revisión anterior

Las ocho ejecuciones principales del commit `2fc722c6a5f7330a9cb1980b509046414e885ae6` finalizaron con `success`; específicamente la ejecución [Lean #43132841499](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/43132841499) compiló el módulo de extensionalidad heredada, incluyendo la igualdad de las derivadas de Fréchet. Esta evidencia **no** contiene ningún certificado de Jacobiano invertible de las ecuaciones económicas completas.

## Proposición nueva

El predicado original `LocalReducedPrefixLogJacobianCertifiedAt` del SOURCE exige (i) positividad de la base de coordenadas, (ii) diferenciabilidad del verdadero operador de residuos en una vecindad de la raíz logarítmica y (iii) un inverso continuo del Jacobiano con cota estricta `||Jinv|| < inverseNormBound`.

En la revisión actual se añadió el lema `localReducedPrefixLogJacobianCertifiedAt_inherited_iff`, que afirma la equivalencia de **ese mismo predicado** para dos estados heredados `I,J` cuando coinciden exactamente `capital`, `firmFace`, `bankFace`, `reserveRateLag` y `reservesPreLag`, y mantienen fijos `P`, rama, `Z0`, calendario y continuación. La demostración busca reescribir el operador logarítmico completo mediante el lema de extensionalidad ya validado.

Interpretación: el estado heredado adicional no altera la validez *condicional* de un certificado de inversa del prefijo reducido. El lema **no fabrica** un inverso: si el predicado es falso en ambos estados, su equivalencia sigue siendo cierta. Tampoco certifica Jacobianos Python, equilibrio general, cierre fiscal o KKT.

El workflow `lean-stationary-policy-payment-bridge.yml` recompila el target y exige `#print axioms` para el nuevo lema. **Al escribir este documento, el nuevo teorema permanece pendiente de compilación del SHA que lo introdujo.**

## Regla para reportar resultados

- `DEMOSTRADO`: igualdad de los residuos y operadores logarítmicos heredados, y la igualdad de sus derivadas, en los SHA de CI ya verificados.
- `PENDIENTE`: equivalencia del predicado de certificación hasta observar éxito del kernel.
- `PENDIENTE`: existencia de un certificado estricto `||Jinv||<B` para la instancia económica real; correspondencia exacta con `finite_irf.py`; validación de la regla terminal; condiciones KKT y equilibrio infinito.

El siguiente desarrollo debe concentrarse en el operador SOURCE concreto con primitivas y estado heredado instanciados, y no en ejemplos matriciales sintéticos. Mantener PR #2 en borrador.
