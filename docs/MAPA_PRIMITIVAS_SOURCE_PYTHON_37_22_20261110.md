# SOURCE Primitives / Python: 37 campos, 22 pruebas y testigo estacionario real

**Corrección de inventario (10-XI-2026).** El SOURCE contiene 37 campos económicos y funcionales, junto con 22 obligaciones de admisibilidad. **La instancia estacionaria ya está construida**, no es una tarea pendiente desde cero: `lean/candidates/Ventura26LiquidityAllocation/StationaryPrimitivesCandidate.lean` define `primitives (G : ℝ) : Primitives LocalBridgePhase` y proporciona las pruebas de todos esos campos. El módulo compiló en [Lean candidate audit #42935620974](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/42935620974), commit `0b9409fe`. Sus predicados `stationary_parameters`, `stationary_recurrent_inputs` y `binary_payment_law` se apoyan en las definiciones literales de `EconomicModel.lean`.

**No confundir tres afirmaciones distintas:** (a) se construyó una instancia SOURCE que satisface su tipo y restricciones; (b) existe un testigo estacionario para las ecuaciones reducidas bajo esa instancia; (c) falta demostrar que esa instancia y una intervención de cuatro instrumentos reproducen la totalidad del operador dinámico del ejecutor Python. (a) y el alcance reducido de (b) están compilados; (c) sigue pendiente.

## 1. Correspondencias existentes y pendientes

| Bloque de SOURCE | Testigo estacionario ya compilado | Relación con Python / pendiente |
|---|---|---|
| Calendario y productividad agregada | `tree := localBridgeTree` y `aggregateProductivity := fun _ => 1` | Comparar historias y fechas de todos los datos del prefijo; no basta el árbol |
| Tipos de firmas y tecnología | masas `1/2`, productividades `1.01/1.0`, `alpha=2/5`, `beta=1/2`, colaterales `0.15/0.4` | Valores compatibles con `steady_case()`; cotejo funcional de producción, empleo y riqueza todavía abierto |
| Preferencias y ajuste | `beta_E=24/25`, `beta_W=99/100`, aversión 1, curvatura y escala 1, depreciación `1/40`, elasticidad 6, coste Rotemberg 150, coste de capital `1/2` | Candidatos compatibles con parámetros de Python, pero no prueba completa de sus Euler y presupuestos sobre la misma historia |
| Renovación bancaria | `bankExit=1/10`, `bankSeedShare=10/Rstar-9`, límites 4 y 6 | El teorema fuente `bankRenewalFactor_eq` da `a_B=1/Rstar`. Las dos filas bancarias tienen equivalencia nivel/log verificada |
| Matching OTC | `matchingIntensity := Real.log 2` | `1-exp(-log 2)=1/2`, la cuota efectiva Python `aa`. La igualdad de pendientes está demostrada únicamente en la rama `tau<=1`; no equivale al SOURCE para `tau>1` |
| Pagos bancarios | soporte exacto `{0,1}`, shocks `-1/5,+1/5`, probabilidades `1/2,1/2` | Las seis obligaciones de soporte/probabilidades/media están ya resueltas; `BinarySymmetricPaymentLaw` y `localPrefixMeanAbsolutePaymentShock_eq_of_binarySymmetric` proporcionan la reducción `E|ω|=1/5` |
| Reglas de política | coeficientes de persistencia `1/2`, `phi_pi=3/2`, `phi_y=1/8`, trayectorias base `rho=1/10`, `Delta=1/50`, innovaciones base cero | El SOURCE `initialIntervenedPrimitives` añade los cuatro shocks solo en fecha cero. Falta integrar todas las funciones con los controles y datos del mismo experimento Python |
| Referencias estacionarias | tasas, reservas y output del paquete `ProposedStationaryBank` y escala productiva | Comparar objetos numéricos y dominios con `make_boundary` y raíces de S/B separadas |
| Bonos públicos | `governmentBondSupply := G`, libre | No imponer `G=0` ni `G=2M` sin demostrarlo; cierre fiscal y estado heredado pendientes |

## 2. Las 22 obligaciones verificadas por el testigo

El SOURCE requiere: `mass_pos`, `productivity_pos`, `productivity_order`, `aggregate_productivity_pos`, `pledgeability_mem`, `alpha_pos`, `beta_pos`, `decreasing_returns`, `price_elasticity_gt_one`, `capital_adjustment_cost_pos`, `matching_intensity_pos`, `depreciation_mem`, `discount_order`, `bank_exit_mem`, `bank_seed_mem`, `bank_caps_nonneg`, `payment_probability_nonneg`, `payment_probability_pos_on_support`, `payment_shock_gt_neg_one_on_support`, `payment_probability_zero_outside`, `payment_probability_sum_one` y `payment_shock_mean_zero`.

Todas aparecen como campos de prueba de `ProposedStationaryPrimitives.primitives`. Los teoremas de dicho archivo son **compilados**, pero la compilación de un testigo de parámetros no demuestra que una `Allocation` completa exista o sea óptima.

## 3. Próxima compuerta, sin duplicar trabajo existente

El módulo nuevo `StationaryInterventionSourceBridgeCandidate.lean` intenta demostrar que la ley de pagos, su momento absoluto, el factor de renovación y las expresiones de encaje/OTC del SOURCE se conservan bajo `initialIntervenedPrimitives (primitives G) v`. El gate focalizado es `lean-stationary-policy-payment-bridge.yml`; **no elevar sus seis lemas a DEMOSTRADOS hasta verificar kernel y ausencia de `sorryAx` en el SHA exacto**.

Después de esa compuerta faltan: identificar la misma estructura `LocalPrefixDateData` (historia, estados, precios, OTC, datos terminales) en Lean y Python; demostrar la igualdad funcional de los 33 residuos y la transformación del Jacobiano; conectar los 34 términos KKT según rama, la optimalidad dinámica y el horizonte infinito. La igualdad de una fila o la inversión de la matriz candidata no resuelven esas obligaciones.

**PR #2 permanece draft; `main` sin modificaciones.**
