# SOURCE: transporte de Jacobianos en una raíz — auditoría condicional

**Corte:** 26 de noviembre de 2026. **Estado:** derivación matemática condicional, pendiente de certificación Lean en el operador SOURCE.  
**Antecedente comprobado:** PR #20, `CurrentSourceTwoDateBankTargetization.lean`, teoremas `targetizedPrefix33_eq_fullEconomicBankShear`, `targetizedPrefix33_zero_iff_originalPrefix33_zero`, `targetizedLogPrefix33_zero_iff_sourceLogPrefix33_zero`. Compilación referida: Actions #45880659556.

## Alcance exacto

El PR #20 prueba, sobre el dominio admisible en ambas fechas y con `P.matchingIntensity = Real.log 2`, la identidad punto a punto del prefijo SOURCE de 33 ecuaciones, `G(z)=E(z)F(z)`. Aquí `F` es SOURCE original, `G` SOURCE targetizado, y `E` una transformación triangular dependiente del estado. Las seis filas bancarias afectadas son 14,15,16,30,31,32 (índices Lean de `Fin 33`); las otras 27 filas permanecen. Esta identidad **no** compara SOURCE con `finite_irf.py`.

## Proposición matemática de transporte (CONDICIONAL)

Sea `U` un abierto de `ℝ³³`, `F,G : U → ℝ³³` y `E : U → GL(33,ℝ)`. Supóngase que las tres funciones son diferenciables en `z₀ ∈ U`, que `G(z)=E(z)F(z)` en un entorno de `z₀`, y que `F(z₀)=0`. Por la regla de Leibniz, en toda dirección `h`:

`DG(z₀)[h] = DE(z₀)[h]F(z₀) + E(z₀)DF(z₀)[h] = E(z₀)DF(z₀)[h]`.

Así, `DG(z₀)=E(z₀)DF(z₀)`. Dado que `E(z₀)` es invertible, `DG(z₀)` es invertible si y solo si `DF(z₀)` es invertible. Cuando ambas inversas existen,

`(DG(z₀))⁻¹=(DF(z₀))⁻¹(E(z₀))⁻¹`.

Bajo una norma submultiplicativa:

`||(DG(z₀))⁻¹|| ≤ ||(DF(z₀))⁻¹|| · ||(E(z₀))⁻¹||`.

**No se ha demostrado para el operador económico concreto que exista el `z₀` supuesto, que la condición admisible defina un entorno abierto, ni que exista una cota certificada para `DF(z₀)⁻¹`.**

## Fuera de la raíz

En general,

`DG(z)[h]=DE(z)[h]F(z)+E(z)DF(z)[h]`.

El primer sumando no puede descartarse fuera de una raíz. Para el uso de Newton/Krawczyk o cotas en una bola, será indispensable controlarlo explícitamente. Tampoco basta el supuesto `tightness ≤ 1` para garantizar interioridad: hay que excluir la frontera o construir una formulación relativa adecuada. Deben auditarse positividad, denominadores no nulos y diferenciabilidad de los coeficientes, incluido el secante exponencial en su extensión por cero.

## Coordinadas y shocks

Si SOURCE emplea la carta `z=φ(x)`, es preciso incorporar `Dφ(x₀)` mediante la regla de la cadena. Si las variables exógenas son `p`, entonces en una raíz `∂pG=E·∂pF`, siempre que estén fijados coherentemente el estado y las variables endógenas; fuera de la raíz queda el término `(∂pE)F`. No se pueden atribuir a SOURCE las matrices de `finite_irf.py` antes de probar la igualdad funcional fila por fila y compatibilidad de parámetros, unidades, pagos y convenciones.

## Obligaciones abiertas, ordenadas por dependencia

1. Probar que las condiciones del PR #20 valen en un entorno abierto de un candidato SOURCE económico, no solo en un punto.
2. Probar diferenciabilidad de `E`, `F` y `G` en ese entorno y formalizar el transporte con `fderiv` en Lean.
3. Obtener una raíz SOURCE certificada (o inclusión validada) y demostrar las hipótesis del teorema en esa raíz.
4. Certificar cuantitativamente la invertibilidad y norma del Jacobiano SOURCE 33×33; transportar correctamente la cota.
5. Auditar las 23 filas restantes de la comparación SOURCE–Python; reconciliar la caja numérica, carta, parametrización y ley de pagos.
6. Conectar con reducción escalar, raíz aumentada 34 dual-cero, ambas ramas S/B para idéntico estado heredado, condiciones intertemporales y `PaperContribution`.

## Ledger de evidencia

- **DEMOSTRADO EN LEAN:** igualdad exacta y equivalencia de ceros SOURCE–SOURCE targetizado del PR #20, condicionadas al dominio.
- **DEMOSTRADO MATEMÁTICAMENTE BAJO NUEVAS HIPÓTESIS:** identidad de los Jacobianos en una raíz y relación de sus inversas.
- **PENDIENTE:** formalización Lean del transporte para SOURCE, regularidad y dominio sobre abierto, raíz, norma del inverso, equivalencia con Python y equilibrio completo.

Esta nota es exclusivamente documental. No modifica Lean, manuscrito, parámetros, figuras, outputs ni IRF.
