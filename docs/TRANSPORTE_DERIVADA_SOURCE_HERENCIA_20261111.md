# IE Project 18 — derivada SOURCE transportada por igualdad heredada (11-XI-2026)

## Resultado del kernel que ya pasó

En la revisión `1a09cc9691accd4a6b1d17bf1bdb9ad8231aeba2` el workflow [Lean payment / inherited extensionality #43125495067](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/43125495067) terminó con `success`. El paso `Compile stationary policy/payment bridge and inspect axioms` pasó y el script exigió la impresión de axiomas de:

- `localReducedPrefixResidual_inherited_extensionality`;
- `localReducedPrefixLogResidualVector_inherited_extensionality`.

Los enunciados tienen como hipótesis igualdad de cinco campos estructurales heredados (`capital`, `firmFace`, `bankFace`, `reserveRateLag`, `reservesPreLag`), fijando primitivas `P`, rama `branch`, fechas `dateOne/recurrent`, carta `Z0` y continuación `tail`.

La conclusión se limita a la igualdad funcional de **los 33 residuos reducidos SOURCE** bajo estos cambios heredados. No compara implementaciones Python.

## Nueva proposición formal añadida

El archivo `ReducedPrefixInheritedExtCandidate.lean` ahora contiene:

`localReducedPrefixLogJacobian_inherited_extensionality`

que reescribe directamente la igualdad de funciones dentro de `fderiv ℝ` en el origen de la carta logarítmica. Matemáticamente, para dos registros con la misma imagen relevante,

`F_log^I = F_log^J` implica `fderiv(F_log^I,0)=fderiv(F_log^J,0)`.

No es necesaria una hipótesis de invertibilidad para establecer la igualdad de los objetos `fderiv`. Sin embargo, **la igualdad de derivadas no prueba que las funciones sean diferenciables ni que `fderiv` sea invertible**; esos son enunciados distintos.

El workflow compila el target y exige el resultado de `#print axioms localReducedPrefixLogJacobian_inherited_extensionality`, con rechazo de `sorryAx` y `unsound`. **Compilación nueva: PENDIENTE** hasta confirmar el run exacto del SHA actualizado.

## Consecuencia operacional futura

Una vez que el tercer lema compile, el certificado de Jacobiano SOURCE, si se obtiene en uno de los dos estados heredados y en la misma base logarítmica, puede utilizar la igualdad funcional para transportar las afirmaciones sobre esa matriz al otro estado de la misma fibra. No se transportan automáticamente las condiciones de factibilidad fiscal, banco y hogares ni la continuación de equilibrio.

La equivalencia `G_Python=P T F_SOURCE psi` permanece sin demostración; la matriz `T` invertible candidata no constituye el certificado de invertibilidad de `DF_SOURCE`.

Mantener PR #2 en borrador y no fusionar `main`.
