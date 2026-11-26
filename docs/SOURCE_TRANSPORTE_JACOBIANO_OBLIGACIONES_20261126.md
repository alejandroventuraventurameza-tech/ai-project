# SOURCE: transporte de Jacobianos en una raíz — auditoría condicional

**Corte:** 26 de noviembre de 2026. **Estado:** transporte Fréchet y preservación condicional de inyectividad DEMOSTRADOS EN LEAN para el operador SOURCE exacto. La verificación de las hipótesis económicas y las cotas numéricas continúa PENDIENTE.  
**Antecedente comprobado:** PR #20, `CurrentSourceTwoDateBankTargetization.lean`, teoremas `targetizedPrefix33_eq_fullEconomicBankShear`, `targetizedPrefix33_zero_iff_originalPrefix33_zero`, `targetizedLogPrefix33_zero_iff_sourceLogPrefix33_zero`. Compilación referida: Actions #45880659556.

## Evidencia formal posterior a esta auditoría

- **PR #24 — transporte Fréchet condicional SOURCE:** `CurrentSourceTwoDateFDerivTransport.lean`, teorema `targetizedLogPrefix33_hasFDerivAt_at_source_root`. [Actions #45891228241](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/45891228241): 2,278 trabajos; solo `[propext, Classical.choice, Quot.sound]`, sin `sorryAx`. Se demuestra la identidad de derivadas **supuestas la raíz, diferenciabilidad y admisibilidad en un entorno**.
- **PR #26 — preservación de inyectividad del Jacobiano SOURCE:** `CurrentSourceTwoDateFDerivRank.lean`, teorema `targetizedLogPrefix33_jacobian_injective_iff`. [Actions #45891910632](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/45891910632): 2,279 trabajos; los mismos axiomas fundacionales, sin `sorryAx`. Inyectividad de los dos Jacobianos es equivalente **bajo las premisas explícitas**. En dimensión finita 33×33, ello implica equivalencia condicional de invertibilidad.
- **NO certificados:** existencia de una raíz SOURCE, diferenciabilidad de las expresiones económicas en una bola admisible, la norma del inverso SOURCE, identidad funcional con `finite_irf.py`, raíz 34 dual-cero, S/B y `PaperContribution`.

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

## Cota algebraica que falta conectar al dato económico

La transformación triangular documentada en PR #20 y en `sourceShearCLM_apply` tiene la estructura `E = I + N`, donde `N` solo añade combinaciones de las filas monetarias 12/13 y 28/29 a las filas bancarias 14/15/16 y 30/31/32. Puesto que `N` **no modifica las filas monetarias**, `N²=0`. Por álgebra matricial,

`E⁻¹=I-N`.

En la norma infinito de vectores y la correspondiente norma máxima de suma absoluta por fila, para los coeficientes evaluados **en un mismo estado**:

`||E⁻¹||∞ = 1 + max(|loan0|, |deposit0|, |balanceRate0|+|balanceQuantity0|, |loan1|, |deposit1|, |balanceRate1|+|balanceQuantity1|)`.

Esta es una **deducción algebraica matemática**, no un nuevo teorema de normas certificado por Lean ni una cota económica numérica. Harán falta intervalos validados de los ocho coeficientes y una cota verificada para el inverso del Jacobiano SOURCE. Entonces, *si existe la raíz común y son invertibles los dos Jacobianos*:

`||(DG(z₀))⁻¹||∞ ≤ ||(DF(z₀))⁻¹||∞ · (1 + M)`.

La demostración de esta desigualdad abstracta no sustituye un certificado cuantitativo efectivo.

## Fuera de la raíz

En general,

`DG(z)[h]=DE(z)[h]F(z)+E(z)DF(z)[h]`.

El primer sumando no puede descartarse fuera de una raíz. Para el uso de Newton/Krawczyk o cotas en una bola, será indispensable controlarlo explícitamente. Tampoco basta el supuesto `tightness ≤ 1` para garantizar interioridad: hay que excluir la frontera o construir una formulación relativa adecuada. Deben auditarse positividad, denominadores no nulos y diferenciabilidad de los coeficientes, incluido el secante exponencial en su extensión por cero.

## Coordinadas y shocks

Si SOURCE emplea la carta `z=φ(x)`, es preciso incorporar `Dφ(x₀)` mediante la regla de la cadena. Si las variables exógenas son `p`, entonces en una raíz `∂pG=E·∂pF`, siempre que estén fijados coherentemente el estado y las variables endógenas; fuera de la raíz queda el término `(∂pE)F`. No se pueden atribuir a SOURCE las matrices de `finite_irf.py` antes de probar la igualdad funcional fila por fila y compatibilidad de parámetros, unidades, pagos y convenciones.

## Obligaciones abiertas, ordenadas por dependencia

1. Probar que las condiciones del PR #20 valen en un entorno abierto de un candidato SOURCE económico, no solo en un punto.
2. **Acreditar para SOURCE concreto** diferenciabilidad de `E` y `F` en ese entorno. El transporte condicional de `fderiv` y la equivalencia de inyectividad **ya** están formalizados en Lean (PR #24/#26); no confundir estas premisas todavía abiertas con la estructura del teorema demostrada.
3. Obtener una raíz SOURCE certificada (o inclusión validada) y demostrar las hipótesis del teorema en esa raíz.
4. Certificar cuantitativamente la invertibilidad y norma del Jacobiano SOURCE 33×33; transportar correctamente la cota.
5. Auditar las 23 filas restantes de la comparación SOURCE–Python; reconciliar la caja numérica, carta, parametrización y ley de pagos.
6. Conectar con reducción escalar, raíz aumentada 34 dual-cero, ambas ramas S/B para idéntico estado heredado, condiciones intertemporales y `PaperContribution`.

## Ledger de evidencia

- **DEMOSTRADO EN LEAN:** igualdad exacta y equivalencia de ceros SOURCE–SOURCE targetizado (PR #20); transporte Fréchet condicional de las 33 filas (PR #24); equivalencia condicional de inyectividad del Jacobiano de 33×33 (PR #26).
- **DERIVACIÓN ALGEBRAICA AÚN NO FORMALIZADA EN LEAN:** inversa triangular `E⁻¹=I-N` y fórmula explícita de norma infinita, sin valores económicos certificados.
- **PENDIENTE:** demostrar que las hipótesis de regularidad y dominio valen para un entorno de raíz SOURCE; construir/certificar la raíz; obtener la norma del inverso económico; comprobar correspondencia funcional con Python y equilibrio dinámico completo.

Esta nota es exclusivamente documental. No modifica Lean, manuscrito, parámetros, figuras, outputs ni IRF.
