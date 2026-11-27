# SOURCE: raíz estacionaria vinculante y transporte de Jacobianos — auditoría de alcance

**Corte:** 26 de noviembre de 2026. **Estado:** raíz exacta de las 33 ecuaciones del prefijo SOURCE vinculante con continuación estacionaria P0, y transporte condicional de Fréchet/rango/inverso, DEMOSTRADOS EN LEAN. También se ha probado que la referencia estacionaria no es una raíz de frontera de 34 ecuaciones. Diferenciabilidad local, inverso efectivo del Jacobiano, raíz 34 con cambio de coordenadas endógenas y equilibrio infinito permanecen PENDIENTES.  
**Antecedente comprobado:** PR #20, `CurrentSourceTwoDateBankTargetization.lean`, teoremas `targetizedPrefix33_eq_fullEconomicBankShear`, `targetizedPrefix33_zero_iff_originalPrefix33_zero`, `targetizedLogPrefix33_zero_iff_sourceLogPrefix33_zero`. Compilación referida: Actions #45880659556.

## Evidencia formal posterior a esta auditoría

- **PR #24 — transporte Fréchet condicional SOURCE:** `CurrentSourceTwoDateFDerivTransport.lean`, teorema `targetizedLogPrefix33_hasFDerivAt_at_source_root`. [Actions #45891228241](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/45891228241): 2,278 trabajos; solo `[propext, Classical.choice, Quot.sound]`, sin `sorryAx`. Se demuestra la identidad de derivadas **supuestas la raíz, diferenciabilidad y admisibilidad en un entorno**.
- **PR #26 — preservación de inyectividad del Jacobiano SOURCE:** `CurrentSourceTwoDateFDerivRank.lean`, teorema `targetizedLogPrefix33_jacobian_injective_iff`. [Actions #45891910632](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/45891910632): 2,279 trabajos; los mismos axiomas fundacionales, sin `sorryAx`. Inyectividad de los dos Jacobianos es equivalente **bajo las premisas explícitas**. En dimensión finita 33×33, ello implica equivalencia condicional de invertibilidad.
- **PR #28 — inversa exacta de la transformación bancaria SOURCE:** `CurrentSourceTwoDateFDerivInverse.lean`, teoremas `sourceShearInvCLM_left`, `sourceShearInvCLM_right` y `targetizedLogPrefix33_inverse_from_source`. [Actions #45897691177](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/45897691177): 2,280 trabajos; `[propext, Classical.choice, Quot.sound]`, sin `sorryAx`. Demuestra que el shear admite inversa lineal continua por negación de los ocho coeficientes, y que **un inverso SOURCE supuesto** se transporta al targetizado con una cota submultiplicativa simbólica. Test auxiliar con aritmética racional exacta: 12 casos estructurales sintéticos; NO es un dato económico.
- **PR #30 — dominio bancario parcial:** `CurrentPinnedBankDomain.lean`, [Actions #45899416069](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/45899416069), 2,281 trabajos, axiomas fundacionales. Positividad de tasas de reserva y reservas preliquidación en ambas fechas para todo desplazamiento logarítmico finito; estrechez estricta <1 cuando `z[16],z[32]<log 2`. Inicialmente redujo la admisibilidad a no-anulación de dos razones por fecha, posteriormente resuelta por PR #33.
- **PR #33 — dominio bancario completo en región logarítmica abierta:** `CurrentPinnedOpenBankDomain.lean`, `pinned_both_dates_bank_admissible`, [Actions #45902880770](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/45902880770): 2,282 trabajos, sin `sorryAx`, solo axiomas fundacionales. Bajo las primitivas estacionarias exactas y para cualquier `G` y `z` con `z[16],z[32] < log 2`, ambas fechas cumplen `TargetBankAdmissible`. Se demuestra positividad de las razones reservas/depósitos realizadas y objetivo, no solo su no-anulación. Esta región contiene `z=0` y es matemáticamente abierta. La conversión topológica a `∀ᶠ z in 𝓝 0, ...` se certificó posteriormente en el PR #36.
- **PR #36 — vecindad abierta y transporte Fréchet en raíz B:** `CurrentPinnedLocalNeighborhood.lean`, [Actions #45904239800](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/45904239800), 2,285 trabajos, axiomas fundacionales, sin `sorryAx`. Prueba `pinnedBankLogRegion_isOpen`, `pinnedBankLogRegion_zero_mem`, `pinned_banking_admissible_eventually` y `pinned_targetized_hasFDerivAt_stationary_root`. Éste **elimina** las premisas de raíz y admisibilidad en vecindad del transporte Fréchet al testigo B; **conserva como hipótesis** las derivadas de `F_SOURCE` y del shear `E`.
- **PR #37 — márgenes bancarios cuantitativos:** `CurrentPinnedQuantitativeBankMargins.lean`, [Actions #45905016903](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/45905016903), 2,286 trabajos, axiomas fundacionales, sin `sorryAx`. Si `||z||∞ < log(2)/2`, entonces `z∈U` y las **cuatro** razones reservas/depósitos (realizadas/objetivo, fechas 0/1) son estrictamente mayores que `2/25` para todo `G`. Sus inversos, por tanto, están entre cero y `25/2`. No son cotas del Jacobiano ni certificado de invertibilidad.
- **PR #31 — datos de las dos fechas:** `CurrentPinnedSourceDateParity.lean`, [Actions #45900184596](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/45900184596), 2,241 trabajos y solo axiomas fundacionales. Demuestra que el origen de la carta es el testigo estacionario SOURCE, y que fecha cero y fecha uno coinciden exactamente con `ProposedStationaryRealScale.dateData`.
- **PR #32 — raíz exacta vinculante:** `CurrentPinnedStationaryPrefix33Root.lean`, `pinned_stationary_binding_prefix33_root`, [Actions #45902492547](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/45902492547), 2,242 trabajos, sin `sorryAx`, solo axiomas fundacionales. Demuestra `F_SOURCE^binding(0;G)=0` **en el prefijo finito de 33 ecuaciones, para el testigo estacionario y la continuación P0 fijada**, con `G` como parámetro. No elige `G` fiscalmente admisible ni construye una `Allocation` infinita.
- **PR #34 — dual positivo y frontera:** `CurrentPinnedStationaryFundingDual.lean`, [Actions #45902646892](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/45902646892), 2,243 trabajos, solo axiomas fundacionales. `mu_L(0)=1/R_L-24/25>0` porque `R_L<25/24`; demuestra `fullyPinnedStationaryP0SOURCE34(G,0,h)!=(0,0)` **para todo h, a las mismas coordenadas z=0**. No excluye raíz de frontera en otro z.
- **PR #39 — interioridad local de la rama vinculante:** `CurrentPinnedStrictBindingNeighborhood.lean`, [Actions #45905466237](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/45905466237), 2,307 trabajos, axiomas fundacionales, sin `sorryAx`. La continuidad del dual original, deducida de la diferenciabilidad ya certificada del dual en carta logarítmica positiva, y su signo estricto en `z=0` prueban `∀ᶠ z in 𝓝 0, mu_L(z)>0` y, para los mismos `z` próximos y **todo** shock `h`, `fullyPinnedStationaryP0SOURCE34(G,z,h) != (0,0)`. No excluye raíces de 34 filas en coordenadas alejadas ni da radio numérico del entorno.
- **PR #38 — continuidad del secante exponencial SOURCE en cero:** `CurrentSourceExpSecantContinuity.lean`, [Actions #45905655281](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/45905655281), 2,277 trabajos, axiomas fundacionales, sin `sorryAx`. Demuestra `expSecant_continuousAt_zero` para la extensión exacta de `(exp u - 1)/u`, y `expSecant_comp_continuousAt_at_zero` cuando el residuo monetario es continuo y vale cero en la raíz. Es **continuidad de un factor**, no diferenciabilidad de `expSecant`, ni continuidad automática de los ocho coeficientes completos, ni diferenciabilidad de las 33 filas SOURCE.
- **PR #41 — radio conjunto explícito DEMOSTRADO EN LEAN:** `CurrentPinnedJointQuantitativeBall.lean`; [Actions #45915131059](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/45915131059), 2,353 trabajos, axiomas fundacionales sin `sorryAx`. Prueba `r_joint=min(log 2/2, log(25/(24 R_L))/4)>0`, fórmula económica SOURCE original del dual de L, `mu_L(z)>0` en `||z||∞<r_joint`, cota bancaria heredada y no-raíz del sistema de 34 filas allí para todo `G,h`. Fusionado: `39b3618bf88fcb91f9299b34ba327b519ec2e9be`.
- **PR #42 — testigo fiscal exacto DEMOSTRADO EN LEAN:** `CurrentPinnedFiscalFiberWitness.lean`; [Actions #45915339275](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/45915339275), 2,243 trabajos, sin `sorryAx`. Fija `G*=2 Mpre` y acredita `B^H=Mpre>0`, `MonetaryPolicyPrimitiveDomain`, `FiscalClosure` **del portador contable** y la raíz SOURCE vinculante de 33 filas con la misma continuación P0. No convierte al portador en equilibrio óptimo infinito. Fusionado: `347ad480d79bf69f6b346a416da80d9797115eab`.
- **PR #43 — distancia necesaria hasta una raíz de frontera 34 DEMOSTRADA EN LEAN:** `CurrentPinnedBoundaryDistance.lean`, [Actions #45917345185](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/45917345185), 2,355 trabajos, sin `sorryAx`, fusionado `1165766e191a7b350842433d45e22b346715de6b`. Para el testigo fiscal G*=2 Mpre, cualquier raíz 34 exige `r_joint ≤ ||z||∞` para todo shock h. No prueba que exista una raíz alejada ni acota h.
- **PR #44 — lema Fréchet con coeficiente escalar continuo DEMOSTRADO EN LEAN:** `CurrentSourceContinuousRootCoefficient.lean`, [Actions #45917920642](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/45917920642), 2,277 trabajos, sin `sorryAx`, fusionado `098c698b2924545002005989ab9c1d56f875da19`. Si `F(x)=0`, `HasFDerivAt F J x` y `ContinuousAt a x`, entonces `HasFDerivAt (fun z => a z * F z) ((a x) • J) x`. Solo prueba la regla analítica escalar; no acredita los ocho coeficientes concretos.
- **PR #45 — cota racional DEMOSTRADA EN LEAN:** `CurrentPinnedRationalBall.lean`, [Actions #45917759589](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/45917759589), 2,354 trabajos, sin `sorryAx`, fusionado `33cb15efa19013737c6edbf0f93c4bde4ed47fe0`. Demuestra `R_L < 81/80`, `1/200 < r_joint`, positividad de `mu_L` y exclusión de la frontera 34 dentro de `||z||∞ < 1/200` para todo `G,h`. No es cota de la inversa del Jacobiano ni certificado IFT.
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

El primer sumando no puede descartarse fuera de una raíz. Para el uso de Newton/Krawczyk o cotas en una bola, será indispensable controlarlo explícitamente. Tampoco basta el supuesto `tightness ≤ 1` para garantizar interioridad: hay que excluir la frontera o construir una formulación relativa adecuada. La positividad de las razones bancarias está cerrada por PR #37 y la **continuidad del secante exponencial en cero** por PR #38. Siguen pendientes la continuidad de los ocho coeficientes económicos completos y, para usar el teorema existente sin relajarlo, sus derivadas. Las otras ramas condicionales y denominadores fuera del bloque bancario también requieren auditoría.

## Coordinadas y shocks

Si SOURCE emplea la carta `z=φ(x)`, es preciso incorporar `Dφ(x₀)` mediante la regla de la cadena. Si las variables exógenas son `p`, entonces en una raíz `∂pG=E·∂pF`, siempre que estén fijados coherentemente el estado y las variables endógenas; fuera de la raíz queda el término `(∂pE)F`. No se pueden atribuir a SOURCE las matrices de `finite_irf.py` antes de probar la igualdad funcional fila por fila y compatibilidad de parámetros, unidades, pagos y convenciones.

## Obligaciones abiertas, ordenadas por dependencia

1. **Dominio bancario y testigo topológico RESUELTOS en PR #30/#33/#36:** `TargetBankAdmissible` vale en ambas fechas en `U={z: z[16]<log2, z[32]<log2}`, abierto que contiene `0`, y está probado `∀ᶠ z in 𝓝 0, ...`. **PR #37** provee además la bola explícita `||z||∞<log(2)/2` con cuatro razones bancarias `>2/25`. Permanecen las otras hipótesis de regularidad SOURCE no comprendidas en `TargetBankAdmissible`.
2. **Acreditar para SOURCE concreto** diferenciabilidad del residuo `F` en la raíz y regularidad apropiada del shear `E` (la prueba Lean actual asume su diferenciabilidad). Los PR #24/#26/#28/#36 ya formalizan el transporte condicional de `fderiv`, rango e inversa en la raíz concreta. **PR #38 prueba solo la continuidad en cero del factor `expSecant` y su composición con un residual continuo**, no de los ocho coeficientes bancarios. Matemáticamente, si `F(0)=0`, continuidad de `E` en cero basta para derivar `D(EF)(0)=E(0)DF(0)`, y el PR #44 prueba la correspondiente regla analítica para un coeficiente escalar continuo. **Falta el transporte económico concreto para los ocho coeficientes de la transformación bancaria y la derivabilidad SOURCE.**
3. **Raíz finita con fibra fiscal concreta:** PR #31/#32 prueban el prefijo vinculante en `z=0`; PR #42 fija `G*=2 Mpre` y demuestra dominio monetario, bonos heredados positivos y cierre fiscal **contable del portador**. Todavía falta acreditar factibilidad/optimalidad global de los agentes, terminalidad y equilibrio infinito; no promover la raíz 33 a solución de frontera 34.
4. Certificar cuantitativamente la invertibilidad y la norma del inverso del Jacobiano SOURCE 33×33. El transporte **simbólico** al Jacobiano targetizado está probado en Lean (PR #28), pero falta una cota efectiva de los ocho coeficientes del shear y del inverso SOURCE sobre un mismo testigo económico.
5. Auditar las 23 filas restantes de la comparación SOURCE–Python; reconciliar la caja numérica, carta, parametrización y ley de pagos.
6. Conectar con reducción escalar y localizar una posible raíz aumentada de 34 ecuaciones con dual cero en otro punto `z`. El PR #34 da obstrucción en `z=0`; #39 en vecindad; **#41 añade radio explícito `r_joint>0` para todo `G,h`**. El PR #43 demuestra ya la distancia necesaria `r_joint ≤ ||z||∞` para cualquier raíz 34 de frontera en el testigo `G*`, sin afirmar existencia. Por separado, contrastar S/B con idéntico estado heredado, condiciones intertemporales y `PaperContribution`.

## Ledger de evidencia

- **DEMOSTRADO EN LEAN:** igualdad exacta y equivalencia de ceros SOURCE–SOURCE targetizado (PR #20); transporte Fréchet condicional de las 33 filas (PR #24); equivalencia condicional de inyectividad del Jacobiano 33×33 (PR #26); inversa exacta del shear y transporte condicional del inverso Jacobiano y su cota submultiplicativa (PR #28).
- **DERIVACIÓN MATEMÁTICA Y REGRESIÓN RACIONAL SINTÉTICA, TODAVÍA SIN TEOREMA DE NORMA INFINITA:** la fórmula explícita `||E⁻¹||∞ = 1+M`. El inverso E⁻¹ en ambas direcciones SÍ está probado en Lean (PR #28); ninguna cota numérica de parámetros económicos ha sido certificada.
- **DEMOSTRADO EN LEAN (alcance finito):** PR #30 (reservas y estrechez), PR #33 (dominio bancario completo), PR #36 (vecindad y transporte en raíz con dos hipótesis de derivadas), PR #37 (bola explícita y razones >2/25), PR #38 (continuidad del secante exponencial en cero), PR #31 (paridad de fechas), PR #32 (raíz B 33 exacta), PR #34 (dual L positivo/no-raíz 34 en punto fijo) y PR #39 (dual positivo y obstrucción 34 en vecindad no cuantificada). No implica óptimo global ni equilibrio infinito.
- **DEMOSTRADO EN LEAN (alcance finito adicional):** PR #41, bola conjunta con `r_joint>0`, `mu_L(z)>0` y ausencia de raíz 34 dentro de ella; PR #42, fibra fiscal concreta `G*=2 Mpre` con dominio monetario, cierre fiscal contable del portador y raíz vinculante 33.
- **DEMOSTRADO EN LEAN (especialización fiscal):** PR #43, separación de toda raíz SOURCE 34 de la raíz vinculante del testigo fiscal por al menos `r_joint` en norma sup, para cualquier innovación h.
- **DEMOSTRADO EN LEAN (lema analítico general):** PR #44, derivación de coeficiente escalar continuo por residuo cero.
- **DEMOSTRADO EN LEAN (radio racional):** PR #45, `R_L<81/80` y `1/200<r_joint`, con estrictez del dual L y exclusión 34 en bola racional.
- **PENDIENTE:** continuidad de los ocho coeficientes SOURCE específicos; diferenciabilidad del residuo económico 33 y controles sobre una bola; cota efectiva de la inversa del Jacobiano; existencia de frontera 34 fuera de la bola; correspondencia funcional SOURCE–Python; rama S y equilibrio dinámico completo.

## Radio conjunto de interioridad vinculante (DEMOSTRADO EN LEAN, PR #41)

Para la carta SOURCE original, la identidad económica exacta del dual de financiamiento L es
`mu_L(z)=1/(R_L exp(z[15]))-(24/25)exp(z[8]-z[24]-z[28])`.
La prueba de Lean construye `m=log(25/(24 R_L))>0`, demuestra que `||z||∞<m/4` implica `mu_L(z)>0` y combina esta desigualdad con el margen bancario de PR #37. Queda probado

`r_joint=min(log 2/2, log(25/(24 R_L))/4)>0`,

y, siempre que `||z||∞<r_joint`, la admisibilidad bancaria en ambas fechas y el dual estricto L; el sistema aumentado 34 de dual-cero no tiene raíz allí para ningún `G,h`. Se trata de una **exclusión espacial local** para la carta logarítmica; **NO** implica una cota del tamaño de la perturbación de política, ni una inversión del Jacobiano.

El **PR #45** ha demostrado y fusionado el refinamiento racional exacto `1/200 < r_joint`, usando una cota más estricta `R_L < 81/80`. Por tanto, `||z||∞ < 1/200` garantiza dominio bancario y dual L positivo; cualquier frontera de 34 filas debe quedar fuera de esa bola. Ese radio puede suministrarse como entrada racional para una futura validación intervalar, **pero no certifica las cotas de `DF_SOURCE` ni su inversa**.

## Ruta cuantitativa mínima restante

El verificador existente `code/v0m/certified_ift/check_quantitative_ift.py` acepta racionales exactos en un JSON `ie-quantitative-ift-v1`. Con (R) una matriz precondicionadora y una bola SOURCE legítima de radio `r`, la aritmética demanda `q = sup ||I-R DF(z)||∞ < 1`, `eta = ||R F(z0)||∞`, `eta + q*r < r`. El programa declara explícitamente `verified_economic_source_enclosures=False`: su éxito aritmético NO acredita procedencia SOURCE de `F`, `DF` ni regularidad de la bola.

El testigo de referencia `fullyPinnedStationarySOURCEZ0` es positivo en sus 33 coordenadas y la calibración estacionaria fija `matchingIntensity = Real.log 2` y `tightness=1/2`. El teorema `fullyPinnedStationaryP0SOURCE_root_exists_iff` sigue siendo **solo** una equivalencia de existencia entre las representaciones aumentada/reducida con dual; NO equivale a la raíz vinculante de 33 filas que el PR #32 sí construyó. Los PR #34/#39 prueban que el dual L es estrictamente positivo en el testigo fijo **y en una vecindad de éste**, de modo que ninguna coordenada de tal vecindad resuelve el sistema aumentado de frontera dual-cero, para ningún shock `h`. El PR #42 ya fija `G*=2 Mpre` con dominio monetario y cierre fiscal contable del portador, pero todavía se requieren admisibilidad/optimalidad de equilibrio completo, derivadas y cotas de Jacobiano sobre el mismo testigo.

Esta nota es exclusivamente documental. No modifica Lean, manuscrito, parámetros, figuras, outputs ni IRF.
