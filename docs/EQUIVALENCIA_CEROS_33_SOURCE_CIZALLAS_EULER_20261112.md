# IE Project 18 — equivalencia del conjunto de ceros de las 33 filas SOURCE bajo dos cizallas Euler

## Punto de partida verificado

El commit `e62979f8471e3d8dffb06085449045d261a6f217` concluyó correctamente las ocho compuertas de CI, incluida `Lean stationary policy and payment bridge (pinned)`, ejecución [43281304776](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/43281304776). El kernel verificó cuatro propiedades sobre la pignoración común, entre ellas la identidad exacta

`E_nominal_i(Z)=E_SOURCE_i(Z)+a_i(Z)*P_SOURCE(Z)`,

donde `P_SOURCE` es la fila ORIGINAL reducida `.commonPledgeOne`, `E_SOURCE_i` la fila ORIGINAL del Euler de capital de fecha uno para `i=H,L`, y `a_i(Z)` su coeficiente real dependiente del estado. Se conserva la regla SOURCE `tail` abstracta.

## Nueva transformación de las 33 filas

El módulo `lean/candidates/Ventura26LiquidityAllocation/SourceFirmEulerThreeRowZeroSetCandidate.lean` contiene cinco teoremas candidatos, desde la identificación individual de los Euler con la coordenada nominal hasta una equivalencia global de conjuntos de ceros.

Se define `sourceNominalPledgeShearedResidual`, un operador de tipo `LocalPrefixEquation → ℝ` que coincide en 31 filas con `localReducedPrefixResidual`, pero utiliza `sourceFirmEulerNominalPledge` para las dos filas Euler de fecha uno. No se elimina la fila de pignoración común.

El objetivo final es demostrar exactamente, para cualquier rama `branch`, parámetros SOURCE `P`, condiciones heredadas `I`, coordenadas `Z`, estados de transición `dateOne,recurrent` y continuación auténtica `tail`:

`(∀ row, sourceNominalPledgeShearedResidual(...) row = 0) ↔ (∀ row, localReducedPrefixResidual(...) row = 0)`.

No se requiere que la rama holgada posea una raíz, ni la positividad de los logaritmos, ni que exista un equilibrio. La prueba condicional usa que cualquiera de los dos conjuntos de ecuaciones incluye `P_SOURCE=0`. Con dicha fila igual a cero, el término de cizalla desaparece y los 33 residuos coinciden punto a punto.

La propiedad del conjunto de ceros es, por tanto, más fuerte que una igualdad en una raíz numérica particular, pero **mucho más débil** que la equivalencia SOURCE–Python: se trata de dos operadores definidos enteramente en Lean y basados en el mismo SOURCE real, sin afirmar que las implementaciones Python y SOURCE coincidan.

## Límite crítico

Aunque la equivalencia de conjuntos de ceros se demuestre, no basta para transportar la invertibilidad de un Jacobiano: hacen falta condiciones de diferenciabilidad, una carta `psi`, la identificación de la continuación SOURCE con `P0`, y una matriz de transformación de filas con derivada invertible en la raíz real. La condición `tail=P0` sigue sin demostrarse en el sentido funcional. Tampoco se ha demostrado que un cero del sistema finito determine un equilibrio infinito o un efecto de crecimiento de largo plazo.

## CI

El módulo se incorporó a `.github/workflows/lean-stationary-policy-payment-bridge.yml`, con compilación del kernel y verificación de `#print axioms` para los cinco nuevos teoremas; el workflow rechaza `sorryAx`. **Estado de los cinco teoremas: PENDIENTE DE KERNEL** hasta completar una ejecución satisfactoria en el SHA de la integración.

PR #2 continúa en borrador, sin fusión con `main`.
