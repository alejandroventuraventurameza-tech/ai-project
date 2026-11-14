# IE Project 18 — Extensionalidad heredada del operador logarítmico (11-XI-2026)

## Nueva obligación formal

Se proponen dos lemas en `lean/candidates/Ventura26LiquidityAllocation/ReducedPrefixInheritedExtCandidate.lean`:

1. `localReducedPrefixResidual_inherited_extensionality`: invariancia, para cada ecuación del prefijo reducido, al modificar exclusivamente siete campos estructurales del registro `InheritedState` que no son leídos por `localPrefixDateZeroData`.
2. `localReducedPrefixLogResidualVector_inherited_extensionality`: invariancia **como función** de `Fin 33 → ℝ` a `Fin 33 → ℝ`, una vez fijada la misma base `Z0`, la misma carta logarítmica, las mismas primitivas, rama y regla de continuación.

Las hipótesis son igualdad de los cinco campos estructurales `capital`, `firmFace`, `bankFace`, `reserveRateLag`, `reservesPreLag` en ambos registros heredados. Los dos campos de firmas son funciones sobre H/L y equivalen a cuatro coordenadas escalares; en total son siete escalares.

**Consecuencia condicional si el kernel aprueba los dos lemas:** las funciones log-residuales SOURCE son iguales punto a punto cuando esas cinco igualdades heredadas se mantienen. En cualquier punto donde la derivada de Fréchet esté definida, ambas tienen el mismo `fderiv` por igualdad funcional. Ello no demuestra que esa derivada exista, sea invertible, ni que coincida con la derivada Python.

## Afirmaciones que siguen prohibidas

La invariancia del operador **reducido** no implica invariancia de cierre fiscal, presupuestos públicos, factibilidad de depósitos y bonos, restricciones bancarias, contratos OTC o bienestar. Tampoco sustituye la identificación de `Primitives` SOURCE y `finite_irf.steady_case`, ni de la regla `tail` con `P0`.

El control CI `lean-stationary-policy-payment-bridge.yml` incluye el target nuevo y exige la salida de `#print axioms` de ambos teoremas, rechazando `sorryAx`, `admit` y `unsound`. **La ejecución del SHA nuevo está pendiente de concluir.** No etiquetar los lemas DEMOSTRADO hasta comprobar que la compilación termina correctamente.

## Próximos pasos

Tras el éxito del kernel, establecer identidad SOURCE de las cinco coordenadas relevantes con `frozen_stationary_seed(s).X0` bajo una instancia de primitivas, probar la relación de la continuación recurrente y trasladar los 33 residuos funcionales al mismo calendario. Solo entonces tiene sentido construir el Jacobiano económico correspondiente y un certificado `||M^{-1}DR||<1`.

Mantener PR #2 como borrador y `main` sin fusionar.
