# IE Project 18 — transporte del Jacobiano SOURCE bajo primitivas fiscales (12-XI-2026)

## Evidencia kernel previa

Las ocho ejecuciones del commit `2a1275728b470137196476bf9f8848c7048c6646` concluyeron `success`. El job [Lean stationary policy and payment bridge #43137551608](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/43137551608) construyó `StationaryFiscalPrimitivesScopeCandidate.lean` e inspeccionó axiomas, incluyendo los lemas `stationaryFiscal_reducedResidual_row_eq` y `stationaryFiscal_reducedLogOperator_eq`.

De este modo, en el **caso estacionario SOURCE concreto**, y conservando iguales la rama, las fechas, la carta `Z0` y la continuación `tail`, el kernel ha aceptado la igualdad de los 33 residuos entre los pares `(primitives G, inheritedState G)` y `(primitives H, inheritedState H)`.

Esta propiedad no fue extrapolada a un equilibrio completo. El registro `primitives G` cambia `governmentBondSupply` y `inheritedState G` modifica los bonos del hogar, por lo que las identidades de cuentas fiscales fuera del prefijo pueden cambiar.

## Nuevas consecuencias propuestas al kernel

Se añadieron a `StationaryFiscalPrimitivesScopeCandidate.lean`:

1. `stationaryFiscal_reducedLogJacobian_eq`: reescribe la igualdad de las funciones log-residuales originales dentro de `fderiv ℝ` evaluada en la raíz logarítmica. Concluye igualdad del **objeto derivada SOURCE** para ambos pares de primitivas y estado heredado.
2. `stationaryFiscal_reducedLogJacobianCertified_iff`: reescribe el predicado original `LocalReducedPrefixLogJacobianCertifiedAt` del SOURCE; si se dispone de una certificación válida de diferenciabilidad e inversa acotada en la misma carta para un valor `G`, su validez es equivalente para el otro valor `H`.

**Estado de estos dos lemas nuevos:** PENDIENTE hasta observar `success` del workflow del SHA que los incorpora, incluyendo `#print axioms` y ausencia de `sorryAx`.

## Qué significa y qué no significa

La identidad de los operadores y sus Jacobianos no equivale a una afirmación de que la deuda pública sea neutral en todo el modelo. No prueba:

- la factibilidad del hogar respecto de títulos públicos;
- la identidad de los impuestos necesarios para el cierre fiscal;
- optimalidad individual bancaria ni satisfacción de KKT;
- igualdad de las asignaciones y precios de equilibrio infinito;
- existencia y cota estricta de una inversa real del Jacobiano; 
- igualdad SOURCE-Python, persistencia o crecimiento de largo plazo.

El predicado `LocalReducedPrefixLogJacobianCertifiedAt` incluye un inverso **si existe**; un teorema `certificado(G) ↔ certificado(H)` no aporta un testigo. Se prohíbe reportar `invertible` hasta proporcionar `Jinv`, ambas identidades de inversa y su cota de norma con aritmética certificada.

## Próximo cierre

Tras validar el nuevo kernel, identificar una instancia económica fuente `F_SOURCE(z;P,I,Z0,tail)` y certificar una correspondencia funcional con `finite_irf.prefix_residual`, cuya carta de coordenadas y parámetros debe comprobarse en vecindad, no solo en el punto estacionario. El transporte de igualdad fiscal puede entonces reducir parámetros redundantes del Jacobiano, pero nunca reemplaza el certificado numérico original.

PR #2 permanece borrador. No fusionar `main`.
