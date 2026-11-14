# IE Project 18 — lema Lean de extensionalidad del prefijo heredado (11-XI-2026)

## Resultado propuesto

Se incorporó `lean/candidates/Ventura26LiquidityAllocation/ReducedPrefixInheritedExtCandidate.lean` con un enunciado que no presupone óptimos ni equilibrio: para dos registros heredados `I,J` que coinciden en `capital`, `firmFace`, `bankFace`, `reserveRateLag` y `reservesPreLag`, el residuo SOURCE reducido `localReducedPrefixResidual` debe coincidir en cada ecuación de las 33 para todo `P,Z,branch,dateOne,recurrent,tail` común.

El argumento de prueba sustituye la igualdad de los constructores `localPrefixDateZeroData P I Z dateOne` y `localPrefixDateZeroData P J Z dateOne`, que solo utilizan los cinco campos heredados indicados. `localPrefixDateOneData` no utiliza directamente `I`.

El lema está **propuesto y pendiente de compilación** en la revisión que agrega su archivo. Se añadió al workflow `lean-stationary-policy-payment-bridge.yml` el target `Ventura26LiquidityAllocation.ReducedPrefixInheritedExtCandidate` y la inspección de `#print axioms`. El resultado del kernel debe verificarse por SHA; no se debe considerar `DEMOSTRADO` hasta obtener éxito.

## Auditoría Python y límites

El script `code/irf/audit_reduced_prefix_inherited_support.py` revisa los cinco accesos SOURCE, los doce campos del registro heredado, las estructuras de fecha cero/uno y un control de metadatos adicionales que la API `finite_irf.prefix_residual` no consume. Su informe se archiva automáticamente como `source-reduced-inherited-support` mediante `build.yml`.

**Interpretación exacta:** la reducción de los 33 residuos elimina siete campos del registro heredado de SOURCE. Esa eliminación no prueba su irrelevancia para otras ecuaciones del modelo económico original: presupuesto fiscal, títulos públicos, factibilidad bancaria después de pagos, optimalidad y contratos siguen necesitando los doce campos y las primitivas.

Una prueba de extensionalidad en SOURCE permite un transporte más limpio de los residuos entre estados heredados con la misma imagen bajo `Phi_I`; no demuestra por sí misma que los operadores Python y SOURCE coincidan o que el Jacobiano completo sea invertible.

## Obligación siguiente

Tras el kernel, habría que probar un lema análogo para el **vector de 33 residuos bajo carta logarítmica**, con la misma base `Z0` y la misma regla `tail`, y cerrar la traducción de los parámetros del modelo, las leyes bancarias/OTC y la continuación recurrente. Solo entonces aplicar certificados de invertibilidad e IFT.

Mantener PR #2 en borrador y `main` sin fusionar.
