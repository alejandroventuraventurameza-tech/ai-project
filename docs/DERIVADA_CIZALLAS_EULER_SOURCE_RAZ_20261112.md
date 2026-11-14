# IE Project 18 — derivada exacta de la cizalla Euler SOURCE en una raiz de pignoracion (12-XI-2026)

## Antecedente verificado

En el commit `d3e003223bd1640382bd84b2aa0af7a9f205008c`, el workflow [43283914375](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/43283914375) concluyó con exito en Lean. Se verifico formalmente `sourceNominalPledgeShearedResidual_all_zero_iff`: la sustitucion conjunta de los dos Euler de fecha uno por las formulas con pignoracion nominal comun preserva el conjunto de ceros del operador SOURCE completo de 33 filas. Esta prueba NO presupone que exista una raiz.

## Nueva compuerta diferencial

Se incorporo `lean/candidates/Ventura26LiquidityAllocation/SourceFirmEulerShearDerivativeCandidate.lean` al workflow fijado. El objetivo es pasar del nivel de residuos a las derivadas sobre una trayectoria escalar arbitraria `Zpath : ℝ → LocalPrefixCoordinates` en el SOURCE real.

Para una empresa `i` y una trayectoria de coordenadas `Z(t)`, la identidad SOURCE previamente demostrada es

`E_nom_i(t) = E_original_i(t) + a_i(t) P_SOURCE(t)`.

Las funciones `E_original_i(t)`, `a_i(t)`, `P_SOURCE(t)` y `E_nom_i(t)` se definen ahora literalmente a partir de `localReducedFirmCapitalEulerResidual`, `localPrefixDateOneData`, `localPrefixEntrepreneurSDF` y `localReducedPrefixResidual(...).commonPledgeOne` del SOURCE original.

Si las tres primeras funciones tienen derivada en `t0` y `P_SOURCE(t0)=0`, la regla del producto implica

`(d/dt)E_nom_i(t0)=(d/dt)E_original_i(t0)+a_i(t0)*(d/dt)P_SOURCE(t0)`.

El termino `a_i'(t0)*P_SOURCE(t0)` desaparece **porque se anula el residuo SOURCE**, y no porque `a_i` sea constante. Las proposiciones candidatas son:

1. `sourceShear_derivative_at_pledge_zero`: regla general `HasDerivAt` para una cizalla dependiente del estado.
2. `sourceFirmNominalEulerPath_shear_identity`: identidad de funciones SOURCE para toda trayectoria `Z(t)`.
3. `sourceFirmNominalEulerPath_derivative_at_pledge_zero`: transporte exacto de derivadas a lo largo de trayectorias SOURCE diferenciables.

Las tres proposiciones contienen auditoria `#print axioms`; su estatus es **PENDIENTE DE KERNEL** hasta una ejecucion GitHub Actions exitosa para la revision que las incluye.

## Limites

El lema demuestra la regla diferencial SOURCE a lo largo de una trayectoria `t↦Z(t)` **bajo hipotesis explicitas de diferenciabilidad**. No prueba que esas hipotesis sean automaticas en todo el dominio economico. Tampoco demuestra derivada de Frechet en 33 dimensiones, equivalencia SOURCE–Python, que la continuacion terminal SOURCE sea el `P0` numerico, invertibilidad del Jacobiano SOURCE, KKT, existencia de equilibrio ni crecimiento de largo plazo.

El siguiente paso matematico es levantar esta regla de derivada escalar a una identidad lineal de Frechet en la carta de 33 variables, con la verdadera continuacion y sus denominadores positivos. Solo entonces podra hacerse un transporte riguroso de la invertibilidad mediante operaciones de filas con determinante no nulo.

PR #2 sigue en borrador; `main` no se fusiona.
