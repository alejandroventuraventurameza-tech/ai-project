# SOURCE Primitives / Python: 37 economic fields and 22 proof obligations

**Checkpoint de alcance, 10-XI-2026.** Los 33 residuos no se convierten en el mismo operador por identificar sus escalas, su carta logaritmica o las formulas de dos mercados. Todavia hay que construir una instancia completa de la estructura real Lean \`Primitives S\` que reproduzca \`steady_case()\`, \`make_boundary()\`, el calendario exogeno, los pagos y las reglas de politica.

El SOURCE contiene 37 campos de datos y funciones, seguidos de 22 obligaciones de positividad, orden, soporte y momentos. Esta enumeracion se deriva literalmente de \`lean/checkpoint/modules/Ventura26LiquidityAllocation/EconomicModel.lean\`, estructura \`Primitives\`, no de un modelo simplificado inventado para el audit.

## 1. Mapa de campos, sin promocion de evidencia

| Campo(s) SOURCE | Candidato Python / interpretacion | Estado |
|---|---|---|
| tree | \`localBridgeTree\`, calendario 0->1->2->2 | SOURCE define el arbol y tiene lemas de soporte; **falta incorporarlo a la instancia economica completa** |
| mass | \`s.mass=[.5,.5]\` | candidato numerico |
| productivity | \`s.technology=[1.01,1.0]\` para H/L | candidato numerico |
| aggregateProductivity | productividad comun igual a uno en la ilustracion Python | candidato FUNCIONAL: definir sobre los tres estados y demostrarlo |
| pledgeability | \`s.pledge=[.15,.4]\` | candidato numerico |
| alpha, beta, depreciation | \`s.alpha=.4\`, \`s.beta=.5\`, \`s.delta=.025\` | candidato numerico |
| entrepreneurDiscount, workerDiscount | \`s.be=.96\`, \`s.bw=.99\` | candidato numerico |
| entrepreneurRiskAversion, workerRiskAversion | \`s.sigmaE=1\`, \`s.sigmaW=1\` | candidato numerico |
| laborCurvature, laborScale | \`s.varphi=1\`, \`s.chiW=1\` | candidato numerico |
| priceElasticity, priceAdjustmentCost | \`s.eps=6\`, coeficiente Rotemberg 150 (coste Python 75*(Pi-1)^2*Y) | candidato por formula; equivalencia del objeto dinamico pendiente |
| capitalAdjustmentCost | \`s.phiI=.5\` | candidato numerico |
| bankExit, bankSeedShare | \`s.eta=.1\`, \`(1/s.rate-(1-s.eta))/s.eta=0.8809519524...\` | candidato condicionado; \`bankRenewalFactor=1/s.rate\` |
| bankDepositCap, bankLoanCap | 4 y 6 en diagnosticos Python | **no** implica optimalidad ni verificacion por tipo bancario |
| matchingIntensity | SOURCE \`lambda=ln2\` equivale a Python \`s.aa=.5\` solo como cuota de matches | igualdades SOURCE probadas localmente para tau<=1; rama tau>1 incompatible |
| governmentBondSupply | NO identificado con un campo de \`steady_case()\` | **abierto**; no asumir cero silenciosamente |
| reserveRatePersistence, reserveQuantityPersistence | coeficientes de rezago .5 en \`auxiliary\` | candidato funcional |
| reserveRateSteady, reserveQuantitySteady | \`s.rr\`, \`s.M\` | candidato numerico |
| outputReference | \`s.Y\` | candidato numerico |
| inflationResponse, outputResponse | 1.5 y .125 dentro de la regla de remuneracion | candidato funcional |
| reserveRateInnovation, reserveQuantityInnovation | estados inicial/dateOne: \`base.e0\`, \`base.e1\`; recurrente: cero | **pendiente** prueba de funcion exogena sobre \`LocalBridgePhase\` |
| reserveRequirementPath, corridorWidthPath | \`s.rho\`, \`s.Delta\`, con perturbacion solo en fecha cero | soporte de politica inicial cotejado; falta instancia con historias |
| paymentSupport, paymentProbability, paymentShock | ley binaria simetrica candidata, momento absoluto \`s.zeta=.2\` | **abierto**: SOURCE exige soporte exacto, probabilidades positivas, suma uno y media cero |

El mapa ocupa **todos los 37 campos** sin marcar ninguno como instancia SOURCE ya construida. Algunos valores son candidatos ilustrativos; las funciones de politica, pagos e historia requieren objetos Lean completos y lemas de representacion.

## 2. Las 22 obligaciones de \`Primitives\`

Se deben rellenar explicitamente:

\`\`\`text
mass_pos, productivity_pos, productivity_order,
aggregate_productivity_pos, pledgeability_mem,
alpha_pos, beta_pos, decreasing_returns,
price_elasticity_gt_one, capital_adjustment_cost_pos,
matching_intensity_pos, depreciation_mem,
discount_order, bank_exit_mem, bank_seed_mem, bank_caps_nonneg,
payment_probability_nonneg, payment_probability_pos_on_support,
payment_shock_gt_neg_one_on_support,
payment_probability_zero_outside,
payment_probability_sum_one, payment_shock_mean_zero.
\`\`\`

Los candidatos escalares satisfacen a primera vista muchas restricciones: .4+.5=.9<1, 1.01>1.00>0, 0<.96<.99<1, 0<.025<1, 0<.15/.4<1, \`lambda=log2>0\`, \`eta=.1\` y \`omega_B≈.88095\` dentro de (0,1). Pero estas comprobaciones aisladas no rellenan los campos de prueba de la estructura Lean, especialmente las seis obligaciones de la ley de pagos.

## 3. Orden de cierre recomendado

Primero construir un archivo Lean independiente que instancie \`Primitives LocalBridgePhase\` con el arbol ya probado, productividad y masa de firmas, parametros, politica por fecha e innovaciones heredadas. Segundo construir la ley de pagos binaria exactamente con dos \`BankPayment\` diferentes y verificar soporte, normalizacion y momento. Tercero reproducir \`LocalPrefixDateData\` y el comportamiento del tail y cotejar las 33 filas bajo el mismo objeto \`P\` y la carta positiva. Solo entonces convertir la matriz candidata T en una igualdad de operadores, probar el Jacobiano SOURCE y aplicar IFT. Los teoremas de existencia/optimalidad bancaria, TVC y crecimiento permanente se evaluan aparte.

**Estado:** inventario de obligaciones y mapa candidato; no es un testigo Lean de \`Primitives\` ni una certificacion completa. Mantener PR #2 draft y main sin modificar.
