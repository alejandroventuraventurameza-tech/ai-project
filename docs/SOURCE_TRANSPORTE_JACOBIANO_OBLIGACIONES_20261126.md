# SOURCE: raíz estacionaria vinculante y transporte de Jacobianos — auditoría de alcance

**Corte:** 26 de noviembre de 2026. **Estado:** raíz exacta de las 33 ecuaciones del prefijo SOURCE vinculante con continuación estacionaria P0, y transporte condicional de Fréchet/rango/inverso, DEMOSTRADOS EN LEAN. También se ha probado que la referencia estacionaria no es una raíz de frontera de 34 ecuaciones. Diferenciabilidad local, inverso efectivo del Jacobiano, raíz 34 con cambio de coordenadas endógenas y equilibrio infinito permanecen PENDIENTES.  
**Antecedente comprobado:** PR #20, `CurrentSourceTwoDateBankTargetization.lean`, teoremas `targetizedPrefix33_eq_fullEconomicBankShear`, `targetizedPrefix33_zero_iff_originalPrefix33_zero`, `targetizedLogPrefix33_zero_iff_sourceLogPrefix33_zero`. Compilación referida: Actions #45880659556.

## Evidencia formal posterior a esta auditoría

- **PR #24 — transporte Fréchet condicional SOURCE:** `CurrentSourceTwoDateFDerivTransport.lean`, teorema `targetizedLogPrefix33_hasFDerivAt_at_source_root`. [Actions #45891228241](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/45891228241): 2,278 trabajos; solo `[propext, Classical.choice, Quot.sound]`, sin `sorryAx`. Se demuestra la identidad de derivadas **supuestas la raíz, diferenciabilidad y admisibilidad en un entorno**.
- **PR #26 — preservación de inyectividad del Jacobiano SOURCE:** `CurrentSourceTwoDateFDerivRank.lean`, teorema `targetizedLogPrefix33_jacobian_injective_iff`. [Actions #45891910632](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/45891910632): 2,279 trabajos; los mismos axiomas fundacionales, sin `sorryAx`. Inyectividad de los dos Jacobianos es equivalente **bajo las premisas explícitas**. En dimensión finita 33×33, ello implica equivalencia condicional de invertibilidad.
- **PR #28 — inversa exacta de la transformación bancaria SOURCE:** `CurrentSourceTwoDateFDerivInverse.lean`, teoremas `sourceShearInvCLM_left`, `sourceShearInvCLM_right` y `targetizedLogPrefix33_inverse_from_source`. [Actions #45897691177](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/45897691177): 2,280 trabajos; `[propext, Classical.choice, Quot.sound]`, sin `sorryAx`. Demuestra que el shear admite inversa lineal continua por negación de los ocho coeficientes, y que **un inverso SOURCE supuesto** se transporta al targetizado con una cota submultiplicativa simbólica. Test auxiliar con aritmética racional exacta: 12 casos estructurales sintéticos; NO es un dato económico.
- **PR #30 — dominio bancario parcial:** `CurrentPinnedBankDomain.lean`, [Actions #45899416069](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/45899416069), 2,281 trabajos, axiomas fundacionales. Positividad de tasas de reserva y reservas preliquidación en ambas fechas para todo desplazamiento logarítmico finito; estrechez estricta <1 cuando `z[16],z[32]<log 2`. Inicialmente redujo la admisibilidad a no-anulación de dos razones por fecha, posteriormente resuelta por PR #33.
- **PR #33 — dominio bancario completo en región logarítmica abierta:** `CurrentPinnedOpenBankDomain.lean`, `pinned_both_dates_bank_admissible`, [Actions #45902880770](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/45902880770): 2,282 trabajos, sin `sorryAx`, solo axiomas fundacionales. Bajo las primitivas estacionarias exactas y para cualquier `G` y `z` con `z[16],z[32] < log 2`, ambas fechas cumplen `TargetBankAdmissible`. Se demuestra positividad de las razones reservas/depósitos realizadas y objetivo, no solo su no-anulación. Esta región contiene `z=0` y es matemáticamente abierta. Todavía no se ha formalizado en Lean la conversión explícita de esta condición puntual en `∀ᶠ z in 𝓝 0, ...` para el teorema de Fréchet.
- **PR #31 — datos de las dos fechas:** `CurrentPinnedSourceDateParity.lean`, [Actions #45900184596](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/45900184596), 2,241 trabajos y solo axiomas fundacionales. Demuestra que el origen de la carta es el testigo estacionario SOURCE, y que fecha cero y fecha uno coinciden exactamente con `ProposedStationaryRealScale.dateData`.
- **PR #32 — raíz exacta vinculante:** `CurrentPinnedStationaryPrefix33Root.lean`, `pinned_stationary_binding_prefix33_root`, [Actions #45902492547](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/45902492547), 2,242 trabajos, sin `sorryAx`, solo axiomas fundacionales. Demuestra `F_SOURCE^binding(0;G)=0` **en el prefijo finito de 33 ecuaciones, para el testigo estacionario y la continuación P0 fijada**, con `G` como parámetro. No elige `G` fiscalmente admisible ni construye una `Allocation` infinita.
- **PR #34 — dual positivo y frontera:** `CurrentPinnedStationaryFundingDual.lean`, [Actions #45902646892](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/45902646892), 2,243 trabajos, solo axiomas fundacionales. `mu_L(0)=1/R_L-24/25>0` porque `R_L<25/24`; demuestra `fullyPinnedStationaryP0SOURCE34(G,0,h)!=(0,0)` **para todo h, a las mismas coordenadas z=0**. No excluye raíz de frontera en otro z.
- **NO certificados:** diferenciabilidad SOURCE en una bola abierta, cota efectiva de `DF_SOURCE(0)^{-1}`, igualdad funcional con `finite_irf.py`, raíz 34 de dual cero con cambios endógenos, rama S y equilibrio completo, resultados finales de `PaperContribution`.

## Alcance exacto

El PR #20 prueba, sobre el dominio admisible en ambas fechas y con `P.matchingIntensity = Real.log 2`, la identidad punto a punto del prefijo SOURCE de 33 ecuaciones, `G(z)=E(z)F(z)`. Aquí `F` es SOURCE original, `G` SOURCE targetizado, y `E` una transformación triangular dependiente del estado. Las seis filas bancarias afectadas son 14,15,16,30,31,32 (índices Lean de `Fin 33`); las otras 27 filas permanecen. Esta identidad **no** compara SOURCE con `finite_irf.py`.

## Proposición matemática de transporte (CONDICIONAL)

Sea `U` un abierto de `ℝ³³`, `F,G : U → ℝ³³` y `E : U → GL(33,ℝ)`. Supóngase que las tres funciones son diferenciables en `z₀ ∈ U`, que `G(z)=E(z)F(z)` en un entorno de `z₀`, y que `F(z₀)=0`. Por la regla de Leibniz, en toda dirección `h`:

`DG(z₀)[h] = DE(z₀)[h]F(z₀) + E(z₀)DF(z₀)[h] = E(z₀)DF(z₀)[h]`.

Así, `DG(z₀)=E(z₀)DF(z₀)`. Dado que `E(z₀)` es invertible, `DG(z₀)` es invertible si y solo si `DF(z₀)` es invertible. Cuando ambas inversas existen,

`(DG(z₀))⁻¹=(DF(z₀))⁻¹(E(z₀))⁻¹`.

Bajo una norma submultiplicativa:

`||(DG(z₀))⁻¹|| ≤ ||(DF(z₀))⁻¹|| · ||(E(z₀))⁻¹||`.

**Ahora se conoce la raíz concreta `z₀=0` de `F_SOURCE^binding` del prefijo finito P0 por PR #32.** No se ha demostrado aún su diferenciabilidad en una bola, la cota del inverso de `DF_SOURCE(0)`, la existencia de una raíz 34 dual-cero ni la correspondencia con el modelo de Python.

## Cota algebraica que falta conectar al dato económico

La transformación triangular documentada en PR #20 y en `sourceShearCLM_apply` tiene la estructura `E = I + N`, donde `N` solo añade combinaciones de las filas monetarias 12/13 y 28/29 a las filas bancarias 14/15/16 y 30/31/32. Puesto que `N` **no modifica las filas monetarias**, `N²=0`. Por álgebra matricial,

`E⁻¹=I-N`.

En la norma infinito de vectores y la correspondiente norma máxima de suma absoluta por fila, para los coeficientes evaluados **en un mismo estado**:

`||E⁻¹||∞ = 1 + max(|loan0|, |deposit0|, |balanceRate0|+|balanceQuantity0|, |loan1|, |deposit1|, |balanceRate1|+|balanceQuantity1|)`.

**La inversa algebraica del shear y su transporte de cotas ya son teoremas Lean (PR #28)**. La fórmula cerrada de la **norma infinito** anterior sigue siendo una deducción matemática y un test racional estructural, no un teorema de norma infinita certificado en Lean ni una cota económica evaluada. Harán falta intervalos validados de los ocho coeficientes y una cota verificada para el inverso del Jacobiano SOURCE. Entonces, *si existe la raíz común y son invertibles los dos Jacobianos*:

`||(DG(z₀))⁻¹||∞ ≤ ||(DF(z₀))⁻¹||∞ · (1 + M)`.

La demostración de esta desigualdad abstracta no sustituye un certificado cuantitativo efectivo.

## Fuera de la raíz

En general,

`DG(z)[h]=DE(z)[h]F(z)+E(z)DF(z)[h]`.

El primer sumando no puede descartarse fuera de una raíz. Para el uso de Newton/Krawczyk o cotas en una bola, será indispensable controlarlo explícitamente. Tampoco basta el supuesto `tightness ≤ 1` para garantizar interioridad: hay que excluir la frontera o construir una formulación relativa adecuada. Deben auditarse positividad, denominadores no nulos y diferenciabilidad de los coeficientes, incluido el secante exponencial en su extensión por cero.

## Coordinadas y shocks

Si SOURCE emplea la carta `z=φ(x)`, es preciso incorporar `Dφ(x₀)` mediante la regla de la cadena. Si las variables exógenas son `p`, entonces en una raíz `∂pG=E·∂pF`, siempre que estén fijados coherentemente el estado y las variables endógenas; fuera de la raíz queda el término `(∂pE)F`. No se pueden atribuir a SOURCE las matrices de `finite_irf.py` antes de probar la igualdad funcional fila por fila y compatibilidad de parámetros, unidades, pagos y convenciones.

## Obligaciones abiertas, ordenadas por dependencia

1. **Dominio bancario resuelto en PR #30/#33:** `TargetBankAdmissible` vale en las dos fechas en el abierto explícito `U={z: z[16]<log2, z[32]<log2}` que contiene la raíz `0`. Falta formalizar, si se requiere en el teorema dependiente, el testigo topológico `∀ᶠ z in 𝓝 0, ...` a partir de esa región, y abordar otras hipótesis de regularidad SOURCE no incluidas en `TargetBankAdmissible`.
2. **Acreditar para SOURCE concreto** diferenciabilidad de `E` y `F` en ese entorno. El transporte condicional de `fderiv` y la equivalencia de inyectividad **ya** están formalizados en Lean (PR #24/#26); no confundir estas premisas todavía abiertas con la estructura del teorema demostrada.
3. **Resuelto SOLO para el prefijo finito vinculante B en `z=0`** mediante PR #31/#32, bajo la construcción estacionaria P0. Validar por separado el régimen fiscal/financiero del `G` elegido, y NO promover esa raíz a solución de la frontera aumentada 34 ni de la economía infinita.
4. Certificar cuantitativamente la invertibilidad y la norma del inverso del Jacobiano SOURCE 33×33. El transporte **simbólico** al Jacobiano targetizado está probado en Lean (PR #28), pero falta una cota efectiva de los ocho coeficientes del shear y del inverso SOURCE sobre un mismo testigo económico.
5. Auditar las 23 filas restantes de la comparación SOURCE–Python; reconciliar la caja numérica, carta, parametrización y ley de pagos.
6. Conectar con reducción escalar y localizar una posible raíz aumentada de 34 ecuaciones con dual cero en otro punto `z`, dado que PR #34 prueba que **ningún `h` basta en `z=0`**; después verificar ramas S/B para idéntico estado heredado, condiciones intertemporales y `PaperContribution`.

## Ledger de evidencia

- **DEMOSTRADO EN LEAN:** igualdad exacta y equivalencia de ceros SOURCE–SOURCE targetizado (PR #20); transporte Fréchet condicional de las 33 filas (PR #24); equivalencia condicional de inyectividad del Jacobiano 33×33 (PR #26); inversa exacta del shear y transporte condicional del inverso Jacobiano y su cota submultiplicativa (PR #28).
- **DERIVACIÓN MATEMÁTICA Y REGRESIÓN RACIONAL SINTÉTICA, TODAVÍA SIN TEOREMA DE NORMA INFINITA:** la fórmula explícita `||E⁻¹||∞ = 1+M`. El inverso E⁻¹ en ambas direcciones SÍ está probado en Lean (PR #28); ninguna cota numérica de parámetros económicos ha sido certificada.
- **DEMOSTRADO EN LEAN (alcance finito):** PR #30 (positividad de reservas y estrechez), PR #33 (dominio bancario completo en abierto), PR #31 (paridad estacionaria de ambas fechas), PR #32 (raíz exacta vinculante de 33 ecuaciones) y PR #34 (dual L positivo y no-raíz 34 en el punto fijo). Los hechos de la construcción no implican óptimo global ni equilibrio infinito.
- **PENDIENTE:** regularidad/diferenciabilidad del operador SOURCE completo en una bola, certificado de la norma del inverso del Jacobiano, raíz de frontera 34 fuera de `z=0`, correspondencia funcional SOURCE–Python, rama S y equilibrio dinámico completo.

## Ruta cuantitativa mínima restante

El verificador existente `code/v0m/certified_ift/check_quantitative_ift.py` acepta racionales exactos en un JSON `ie-quantitative-ift-v1`. Con (R) una matriz precondicionadora y una bola SOURCE legítima de radio `r`, la aritmética demanda `q = sup ||I-R DF(z)||∞ < 1`, `eta = ||R F(z0)||∞`, `eta + q*r < r`. El programa declara explícitamente `verified_economic_source_enclosures=False`: su éxito aritmético NO acredita procedencia SOURCE de `F`, `DF` ni regularidad de la bola.

El testigo de referencia `fullyPinnedStationarySOURCEZ0` es positivo en sus 33 coordenadas y la calibración estacionaria fija `matchingIntensity = Real.log 2` y `tightness=1/2`. El teorema `fullyPinnedStationaryP0SOURCE_root_exists_iff` sigue siendo **solo** una equivalencia de existencia entre las representaciones aumentada/reducida con dual; NO equivale a la raíz vinculante de 33 filas que el PR #32 sí construyó. El PR #34 prueba que el dual L es estrictamente positivo en el testigo fijo, de modo que esa raíz NO resuelve el sistema aumentado de frontera dual-cero. Aún debe fijarse/validarse `G` para admisibilidad fiscal, así como derivadas y cotas numéricas sobre el mismo testigo.

Esta nota es exclusivamente documental. No modifica Lean, manuscrito, parámetros, figuras, outputs ni IRF.
