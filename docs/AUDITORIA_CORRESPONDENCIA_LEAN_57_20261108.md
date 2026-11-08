# Matriz de correspondencia entre los 57 resultados y Lean

## Puente fisico del producto marginal de capital

La [CI focalizada #42505447150](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/42505447150), commit `17a56a00f5ce372039f00cada55d6f185891bdff`, verifico dos teoremas adicionales de la tecnologia original: `original_firm_production_hasDerivAt_capital` y `original_firm_mpk_equals_elasticity_times_output_per_capital`. El kernel y `#print axioms` no reportaron `sorryAx`. La igualdad MPK = alpha*Y/k se deduce de Cobb-Douglas, con k>0 y empleo individual fijo en la derivacion.

**42 declaraciones Lean relacionadas con 4.3** (37 auxiliares previos, 3 integradores, 2 MPK fisicos); no confundir declaraciones de composicion con mecanismos independientes. **0/57 equivalencias formales integrales** respecto a la vieja interfaz fuente. La prueba de once clausulas es un predicado nuevo y mas fiel al manuscrito, no una traduccion literal auditada del checkpoint.


## Integracion de las once afirmaciones fuente del Lema 4.3

El teorema `original_source_static_lemma43_bundle` paso compilacion y auditoria de axiomas sin `sorryAx` en [CI #42505059048](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/42505059048), SHA `0cb2bb63`. Su equivalente diferenciable `original_source_dynamic_lemma43_bundle` paso [CI #42505126404](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/42505126404), SHA `5f407870`.

**La composicion de las once conclusiones esta formalmente demostrada** como `sourceLemma43CompleteSpec_proved`, [CI focalizada #42505264161](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/42505264161), SHA `b132b91d`. No hay `sorryAx` en los tres controles. Es una demostracion de un predicado NUEVO mas fiel al manuscrito; no una equivalencia demostrada con el viejo `allocationLossIdentitySpec` ni con el equilibrio dinamico.

**Total formal de declaraciones relacionadas con 4.3: 40** (37 auxiliares anteriores y 3 integradores). Las tres ultimas agrupan resultados previos: el numero de declaraciones no debe confundirse con 40 resultados economicos independientes. **Estado de los 57 enunciados numerados originales: 0 en equivalencia integral.**


## Regla de cadena fuente cerrada en Lean, con cuota física y cociente de capitales

La [CI focalizada #42504364485](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/42504364485), SHA exacto `eaa08a328974c9462e8b5cdaa85a33f0dd88546b`, compiló `PaperSourceLossChainRuleCandidate.lean`, `PaperSourceOutputShareCandidate.lean` y `PaperSourceLogCapitalRatioCandidate.lean` y auditó **tres teoremas adicionales sin `sorryAx`**. La primera tentativa falló por `import` faltante ([#42503619169](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/42503619169)); la segunda por mera asociación de productos ([#42503922235](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/42503922235)); ambas incidencias fueron corregidas antes del run verde.

**Total auxiliar Lema 4.3: 37 teoremas Lean verificados**. La derivada de la pérdida `alpha*(kappaH-omegaH)*d log(kH/kL)` ahora se obtiene de `K(k)`, `G(k)` y la diferenciación de las funciones de capital positivas. Se verificó `omegaH=vH*YH/Y` con la distribución óptima de trabajo, y el diferencial logarítmico del cociente físico. No se eleva ningún resultado numerado a equivalencia completa hasta revisar el enunciado literal integral y la economía dinámica.


## Derivadas fuente K/G verificadas, regla completa pendiente

La [CI #42503513399](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/42503513399), commit `a6f83b4e`, verificó por kernel cuatro teoremas `HasDerivAt` para `K(t)`, `G(t)`, `log K(t)` y `log G(t)` desde los capitales y productividades fuente. La [CI #42503571340](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/42503571340), commit `4cf59454`, verificó dos identidades exactas de `kappa_H` y `omega_H` en esos diferenciales. Ambas ejecuciones `#print axioms` sin `sorryAx`.

**Total actual de pruebas auxiliares de 4.3: 34**, pero la prueba compuesta de `dLoss` sigue pendiente. La primera CI de regla de cadena [#42503619169](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/42503619169) falló por falta de un `import`, corregido en commit `06ed880a`; no contar aún el teorema compuesto.


## Cierre del puente físico conjunto: cuatro pruebas adicionales verificadas

La [CI focalizada #42502060253](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/42502060253), commit `5ea744a50d068d1e4efee613522f1e8b63242f67`, compiló los módulos `PaperJointEfficiencyPhysicalCandidate.lean` y `PaperOriginalLogLossCandidate.lean`; la auditoría `#print axioms` de **cuatro teoremas** pasó sin `sorryAx`. El resultado físico admite repartos no negativos de ambos factores, presupuestos agregados positivos y exponentes comunes; el candidato alcanza la frontera `Yeff`. En cantidades positivas, la pérdida `log(Yeff/Y)` es no negativa y, para trabajo óptimo, se recupera la fórmula exacta de logaritmos del paper.

**Total auxiliar del Lema 4.3: 28 declaraciones kernel-checked** (20 previas, cuatro de puente K/L, cuatro físicas/log). **0 de 57 resultados numerados** elevados a `same_statement_proved`: la identidad diferencial de pérdida desde funciones fuente y la traducción semántica completa siguen abiertas.


## Progreso adicional: puente de eficiencia conjunta K/L verificado parcialmente

Se verificaron en el kernel **cuatro lemas nuevos** para la frontera productiva conjunta: `normalized_source_firm_output` y `normalized_joint_scale_identity` ([CI focalizada #42501665345](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/42501665345), commit `c578e398`), más `normalized_two_type_source_output_le_efficient` y `source_resource_budget_normalizes` ([CI #42501725491](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/42501725491), commit `f8e1125b`). Cada ejecución confirmó `#print axioms` sin `sorryAx`.

**Total auxiliar 4.3 en este corte: 24 teoremas.** La cota íntegra del producto físico para cualquier asignación no negativa, la alcanzabilidad y el log-loss físico permanecen bajo auditoría (no se promocionan por su similitud con los cuatro lemas verificados). Ninguno de los 57 resultados del paper se acredita completo por estas pruebas auxiliares.


## Avance verificable adicional: nueve lemas de producción física y trabajo

Los módulos `PaperAllocationSourceAlgebraBridgeCandidate.lean` y
`PaperOptimalLaborCandidate.lean` ahora cuentan con **nueve teoremas
adicionales verificados** sobre tecnología microagregada, asignación de
trabajo, factibilidad y cota global con capital fijo. La
[CI focalizada #42500091118](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/42500091118)
en commit `e9ec2024da991768115ecb70e39acdfb647f8b9a` compiló y realizó
`#print axioms` sin `sorryAx`. Se agregaron nueve entradas
`source_labor_kernel_verified` a la matriz y una validación de conjuntos,
SHA y run al auditor `code/audit_lean_crosswalk.py`. **Total auxiliar 4.3: 20 teoremas**, de ellos nueve anteriores y nueve nuevos; **0 de los 57
resultados del paper** elevados a equivalencia formal completa.

La cota para **cualquier** asignación laboral original factible
sin presupuesto normalizado supuesto ahora está **kernel-checked**:
`original_two_type_labor_global_bound` y
`original_labor_candidate_attains_global_bound` compilaron y pasaron
`#print axioms` sin `sorryAx` en la
[CI focalizada #42500721984](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/42500721984),
commit `548911a4b763f8d75ad635338d27752253d71231`. También faltan frontera eficiente conjunta de K/L desde la
fuente, la derivada de Loss y la equivalencia con los predicados económicos.


**Corte editorial:** 8 de noviembre de 2026. **Rama de investigación:**
`work/lean-ci-validation-otc-20261106`. **Fuente de verdad:**
`paper/result_ledger.json` y `paper/lean_crosswalk_57.json`.

## Actualización CI: cuatro declaraciones financieras comprobadas

La auditoría Lean
[42457259796](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/42457259796),
commit `c006e00c437243c3f6f44ec3c102df4286c545e0`,
**compiló y auditó `#print axioms` sin `sorryAx`** para
`exact_noSimultaneousSavingBorrowingSpec` (3.2),
`exact_financingCapacityComparativeSpec` (3.3),
`original_fundingSupergradientSpec_false` (contraejemplo a
la versión mal parentizada de 3.5) y
`corrected_fundingSupergradientSpec` (superdiferencial de
3.5 matemáticamente corregido). La especificación literal
3.5 no se declara probada: está refutada. El checkpoint
`PaperInterface.lean` permanece intacto.

El Lema 3.1 también quedó **DEMOSTRADO como especificación literal
Lean**: `PaperRepaymentExactCandidate.exact_repaymentSpec`
compiló y pasó `#print axioms` sin `sorryAx` en
[42458034938](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/42458034938),
commit `acc4263a2c60c6ec3a90c3331aef9cb522e4427a`.
Cubre por estado la cota de repago real, la desigualdad de
patrimonio, su no negatividad y su positividad si hay capital o
depósito positivo. No acredita suficiencia dinámica ni
solvencia bancaria en presencia de retiradas.

El Lema 4.3 cuenta ahora con **tres identidades auxiliares
formalmente verificadas** en
`PaperAllocationLossElasticityCandidate.lean`. Pasaron el kernel
y `#print axioms` sin `sorryAx` en
[Lean focalizado #42458449121](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/42458449121),
commit `1e797f886dea03a6fdea135338e6408a3e8ab91b`:
(1) álgebra del diferencial si se conocen las logderivadas agregadas,
(2) orden de participaciones y producto por capital positivo,
(3) signo negativo de la pérdida cuando se mueve capital relativo
hacia el tipo con mayor participación de producto que de capital.

El **Lema 4.3 integral sigue pendiente**: demostrar el reparto
laboral óptimo, la referencia eficiente y su superioridad productiva
desde los problemas originales, junto con las derivadas de
agregadores Cobb–Douglas. La versión de `allocationLossIdentitySpec`
tampoco contiene la ecuación diferencial completa del paper. Véase
`docs/LEMA_4_3_MECANISMO_ASIGNATIVO_20261108.md`.
La matriz registra run y commit para estos fragmentos sin cambiar
su relación a `same_statement_proved` del resultado académico.

La matriz `paper/lean_crosswalk_57.json` registra
la evidencia verde de estos cuatro objetos, pero
`paper_proof_equivalent_in_lean` conserva el valor
`not_established` en el registro: se certifican las
**proposiciones Lean exactas o corregidas**, no por ello
la totalidad de las obligaciones intertemporales del paper.

## Actualización AM–GM: cota global normalizada verificada

El conjunto de cuatro teoremas de
`PaperAllocationEfficiencySupportCandidate.lean` **pasó el kernel
Lean y `#print axioms` sin `sorryAx`** en
[CI focalizada #42459394970](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/42459394970),
commit `8e883b7993f39d29ae431c44a6a14e45ca55707d`:
`normalized_two_type_output_le_benchmark`,
`normalized_benchmark_attained`,
`normalized_log_loss_nonneg` y
`efficient_candidate_clears_resources`.

Es una prueba global bajo presupuestos normalizados,
no solo KKT. Falta el transporte formal a la tecnología
individual original, el reparto óptimo de trabajo,
las definiciones físicas de `Y` y `Yeff` y la
derivada del índice de pérdida desde los agregadores
Cobb–Douglas. El `PaperInterface.allocationLossIdentitySpec`
carece además de restricciones que hagan comunes los
exponentes de H y L, define `Y` y `Yeff` por las
igualdades que después repite, y omite la derivada
completa del paper. Por ello **no** se declara resuelto
el Lema 4.3 integral.

Véase `docs/LEMA_4_3_PUENTE_EFICIENCIA_AMGM_20261108.md`
para la reconstrucción analítica y los puentes pendientes.

## Actualización: potencia y pérdida agregada ahora kernel-checked

`PaperAllocationSourceAlgebraBridgeCandidate.lean` contiene
dos nuevas declaraciones que superaron
[Lean focalizado #42459648021](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/42459648021),
commit `aef180ba9595e426c32236a2941731837151fdcc`,
con `#print axioms` sin `sorryAx`:
`productivity_weight_recovers_A` y
`positive_aggregate_loss_log_formula`. Se registraron
en `paper/lean_crosswalk_57.json` como auxiliares
verificados, no como equivalencia integral del Lema 4.3.

Así se dispone de **9 lemas auxiliares formalmente verificados
para el Lema 4.3** (3 de derivadas/participaciones/signo,
4 de eficiencia global normalizada, 2 de potencias/logaritmos).
Faltan la igualdad de la producción original
microagregada con la fórmula `L^b G^(1-b)`,
la optimalidad laboral y la formalización explícita
de la derivada de `G` a partir de `k_i` con
exponentes comunes en ambas firmas.

## 1. Veredicto general sin sobredeclaración

Se han inspeccionado de manera dirigida **24 de 57** afirmaciones:
se localizó al menos una declaración Lean con objeto relacionado, y
se describió explícitamente por qué no alcanza, todavía, a demostrar
el enunciado completo del paper. **33 resultados** siguen pendientes
de cotejo semántico individual. El identificador histórico de cada
resultado, su título y el hash de su enunciado son trazables en JSON.

El estatus de formalización integrada del registro fuente permanece
`not_run` en los **57/57 casos**; por tanto **ningún resultado
numerado se promociona a prueba formal de igual alcance**.
Eso no niega que existan teoremas Lean válidos; impide confundirlos
con enunciados que cambian cuantificadores, funciones, hipótesis,
dominios, calendarios o conclusiones.

El auditor `code/audit_lean_crosswalk.py`, agregado a
`editorial-qa.yml`, verifica uno por uno: cardinalidad, etiquetas,
títulos, hashes de enunciados, enlace a las declaraciones
Lean efectivamente existentes, existencia de las referencias
numéricas y ausencia de promoción espuria de cobertura.
Su salida `PASS_SYNTAX_AND_SCOPE_ONLY_NOT_EQUIVALENCE` solo
certifica **integridad del inventario y alcance declarado**;
no es una prueba Lean ni una certificación de correspondencia.
El módulo Lean especializado `LocalScalarStationaryPythonCalibrationCandidate`
y otras identidades sí pasaron sus propias auditorías de
compilación y axiomas en los runs registrados en la nota
`PUENTE_ESTACIONARIO_PYTHON_LEAN_20261108.md`.

## 2. Lectura precisa de la proposición central

La proposición `prop:local_macro_multiplicity` del paper considera
una función reducida `M(s,h)`, de clase `C¹` cerca de
`(0,0)`, con `M(0,0)=0`,
`b=∂_s M(0,0)<0` y `a_R=∂_h M(0,0)<0`.
Para `h<0` pequeño obtiene una solución en el borde `s=0`
y una raíz positiva `s(h)>0`; para `h>0` pequeño,
no hay solución complementaria cercana.

Las declaraciones Lean relacionadas **no son literalmente iguales**:

| Declaración Lean localizada | Qué afirma realmente | Qué falta para el paper |
|---|---|---|
| `ProposedScalarComplementarityMultiplicity.scalar_complementarity_exactly_two` | Cuenta dos soluciones dada antitonicidad en el semieje no negativo, una raíz positiva explícita y `M(0)>0` | Derivar raíz y signos para `h` desde `C¹`; antitonicidad aquí es global sobre el semieje |
| `ProposedLocalScalarPolicyBifurcation.negative_shock_creates_exactly_two_local_scalar_roots` | Produce la raíz en una cuña local si se tienen derivadas y continuidad/monotonía en dicha cuña | Identificar efectivamente esas premisas con el Schur complement fuente |
| `ProposedLocalScalarEconomicPolicyCertificate.source_economic_negative_remuneration_shock_two_roots` | Especializa al mapa económico de fuente, pero presupone `LocalScalarImplicitReduction`, dual nulo en el punto de base y regularidad local uniforme de cortes | Certificar las premisas en la instancia numérica fuente, no asumirlas a partir del Python heredado |
| `ProposedProposition42Audit.localMacroMultiplicitySpec_false` | Refuta el contrato original que pedía unicidad literal de la estructura `Allocation` con un campo `collateralDual` no restringido por el predicado de equilibrio | Reformular unicidad primal sobre soporte admisible, probar existencia de las dos ramas económicas y condiciones terminales |

**Conclusión responsable:** la prueba escrita de complementariedad
local es matemáticamente coherente bajo sus premisas,
pero las **premisas del modelo económico original**
aún no están plenamente verificadas para ambas ramas.
El contraejemplo de la especificación Lean original
no constituye una refutación de la multiplicidad
económica que compara variables primales.

## 3. Resultados principales y el tipo de brecha

Las numeraciones de la tabla son **identificadores históricos** del
ledger; el cuerpo compacto conserva una paginación nueva y
los números de PDF antiguos no deben usarse como localizadores.

| ID del ledger | Hallazgo del cotejo dirigido | Veredicto |
|---|---|---|
| 3.3 — efecto parcial de menor tasa | `rate_cut_raises_capacity_given_same_funds` y `firmFeasible_binding_capital_formula` son lemas algebraicos del mismo canal | Prueba auxiliar, no cálculo diferencial completo de equilibrio |
| 3.6 — KKT financiero | `source_scalar_complementarity_recovers_original_L_KKT` recupera la condición escalar de L | No cubre equivalencia total de KKT ni suficiencia |
| 3.8 — spread no negativo | `bank_margins_and_pricing` fija signos del testigo estacionario | No demuestra la proposición general de covarianza |
| 3.9 — consistencia de flujos | `parent_resourceClears`, `parent_bankBalance`, `parent_creditClears` cierran cuentas estacionarias | La prueba general por historias permanece abierta |
| 4.1 — equilibrio de frontera | `BoundaryFullPrefixCandidate` verifica filas del prefijo | No demuestra todas las premisas de equilibrio competitivo |
| 4.2 — multiplicidad local | Teoremas escalares y contraejemplo literal citados arriba | Correspondencia económica completa no establecida |
| 4.4 — asignación opuesta S/B | Existe una cuenta numérica reproducible y lemas de raíces escalares | No existe prueba Lean de los signos de capital, pérdida y soluciones de equilibrio |
| 4.5 — persistencia bajo riesgo | Todavía no se cotejó con declaración de mismo alcance | Revisión prioritaria pendiente |

Los **14 resultados numerados del cuerpo histórico** ya tienen cotejo
semántico dirigido. Esto no acredita cobertura integrada: para cada
resultado se han registrado las hipótesis y las brechas.

## 4. Cinco relaciones auxiliares del anexo

Se localizaron relaciones parciales relevantes para
`prop:stationaryexistence` (testigo estacionario
`parent_competitiveEquilibrium`),
`lem:statewise_collateral` (garantía de una trayectoria),
`lem:nominal_face_identity` (identidad de cara nominal),
`lem:common_pledge_state` (equivalencia de ceros de fila 21),
y `lem:CRRA_H_demand` (identidad de presupuesto y cobertura,
sin derivar utilidad CRRA). Ninguna ha sido promovida a
igualdad literal con el lema del anexo.

## 4 bis. Hallazgo del módulo fuente `FinancialCore.lean`

La segunda revisión reveló una omisión metodológica del primer inventario:
en `lean/checkpoint/modules/Ventura26LiquidityAllocation/FinancialCore.lean`
hay **tres teoremas fuente** mucho más cercanos al paper de lo
que sugerían los nombres de los módulos candidatos:

| Resultado | Prueba fuente ya declarada | Nuevo puente exacto candidato |
|---|---|---|
| Lema 3.2: no ahorrar y endeudarse simultáneamente | `no_simultaneous_saving_and_borrowing`: contradicción de KKT si `RL>RD>0` y ambos saldos positivos | `exact_noSimultaneousSavingBorrowingSpec` |
| Proposición 3.3: efecto parcial de la tasa | `financingCapacity_hasDerivAt_and_deriv_neg`: derivada exacta de capacidad con fondos, `q` y garantía fijos | `exact_financingCapacityComparativeSpec` |
| Lema 3.5: superdiferencial | `isFundingSupergradient_iff_cases`: equivalencia global para tres caras, incluyendo el intervalo en `f=0` | `original_fundingSupergradientSpec_false` + `corrected_fundingSupergradientSpec` |

Los puentes se declararon en
`lean/candidates/Ventura26LiquidityAllocation/PaperFinancialMainExactCandidate.lean`.
**Solo 3.2 y 3.3** tienen objetivo literal `PaperInterface.*Spec`.
Para 3.5, la primera compilación **FALLÓ** (Lean CI
[42456592968](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/42456592968)).
La inspección mostró que el `PaperInterface.fundingSupergradientSpec`
fue escrito formalmente como

```text
((0 < RD -> RD < RL -> IsFundingSupergradient RL RD face slope)
  <-> FundingSupergradientCases RL RD face slope)
```

y no como la especificación económica correcta

```text
(0 < RD -> RD < RL ->
  (IsFundingSupergradient RL RD face slope
   <-> FundingSupergradientCases RL RD face slope))
```

Es un error sustantivo de ámbito de `→` frente a `↔`, no
simplemente una táctica `intro` que no compiló. Contraejemplo:
`RL=RD=1`, `face=0`, `slope=2`. La premisa de spread
estricto es falsa y la implicación de la izquierda resulta
verdadera vacíamente, mientras que los casos de la derecha son
falsos (el intervalo admisible sería `[1,1]`).
Por tanto, el enunciado original **no puede demostrarse**
en lógica consistente. No se modifica el checkpoint;
se añade el teorema `original_fundingSupergradientSpec_false`
y una proposición independiente
`fundingSupergradientCorrectedSpec` con prueba
`corrected_fundingSupergradientSpec`.
La compilación y auditoría de axiomas de esas dos declaraciones
**siguen pendientes de CI** antes de elevar su estatus.
No modificar todavía `formalization_status` del ledger fuente.

El problema no invalida la fórmula económica del paper,
que ya contiene `R^L>R^D>0`; invalida la transcripción lógica
del objetivo fuente cuando las tasas están fuera de ese dominio.

Al cotejar **los siete últimos resultados principales**:
el Lema 3.1 dispone del predicado fuente `RobustCollateral`,
y ahora existe un candidato exacto para patrimonio futuro no negativo, aún bajo prueba Lean;
el Lema 3.4 tiene un teorema fuente de recuperación de cartera
`signedFundingEquivalence` que no eleva por sí solo óptimos
intertemporales; el Lema 3.7 tiene la cota de tasa interbancaria
`otcCorridorWeight_mem` pero no la monotonicidad global prometida
en `tightness`; y los resultados 4.3 y 4.5 siguen sin prueba
completa equivalente a su enunciado histórico.

**Brecha especialmente relevante para 4.3:** `allocationLossIdentitySpec`
en `PaperInterface.lean` enuncia parte del referente eficiente y
la no negatividad de la pérdida, pero **no** contiene la derivada
`d𝓛 = α(κ_H-ω_H)d log(k_H/k_L)` incluida en el paper.
Aun una prueba exitosa de ese `Spec` sería estrictamente más débil
que el lema académico completo.

**Brecha especialmente relevante para 4.5:** el `Spec` Lean original
requiere dos equilibrios competitivos estocásticos completos para
riesgos positivos pequeños, mientras que el paper vigente enuncia
solo persistencia de soluciones reducidas **suponiendo** que
la continuación es contractiva. No puede reutilizarse el resultado
reducido para afirmar verdadero el `Spec` más fuerte.

## 4 ter. Auditoría dirigida del núcleo de existencia y suficiencia en anexos

Se amplió el cotejo a cinco proposiciones de riesgo especialmente alto:
`prop:firm_sufficiency_infinite` (A.17.1),
`prop:general_regime_sufficiency` (A.32.1),
`prop:finite_prefix_equilibrium` (A.32.2),
`prop:certified_small_risk_equilibrium` (A.30.1)
y `prop:nonlinear_local_path` (A.15.2).
Las cinco tienen declaraciones Lean **relacionadas pero de
alcance insuficiente** para sus enunciados originales.

- `parent_firmOptimal` y `parent_firm_dominates` demuestran
  optimalidad de empresas en un **testigo estacionario concreto**;
  no la suficiencia intertemporal para todo árbol y régimen financiero.
- `firmOptimal_twoSidedVariation_derivative_zero` obtiene una
  condición **necesaria** de optimalidad por variación, no una
  suficiencia universal de sistemas KKT.
- `parent_competitiveEquilibrium` acredita un equilibrio
  estacionario literal condicionado a `reservesPre≤G`;
  no ensambla una continuación estocástica con un prefijo perturbado.
- `boundaryRoot_spec` exhibe una raíz del residual de
  recursos de frontera bajo paquetes de signo, no el equilibrio
  de todas las condiciones de empresas, hogar, bancos y precios.
- `source_economic_negative_remuneration_shock_two_roots`
  presupone una reducción implícita y signos locales;
  no certifica las contracciones uniformes ni la
  optimalidad del testigo con riesgo `0<η≤10^-31`.

Esta revisión eleva el número de resultados con cotejo
dirigido a **24/57**; los otros **33** siguen sin revisión
individual. No significa que estas cinco proposiciones hayan
quedado demostradas en Lean. Se conserva la marca
`paper_proof_equivalent_in_lean=not_established`.
El inventario exacto y las obligaciones individuales están en
`paper/lean_crosswalk_57.json`.

## 5. Obligaciones antes de promover cualquier resultado

1. Comparar **enunciado literal**, todos los cuantificadores y
   dominios. Un resultado para un testigo estacionario no cubre
   una afirmación general en un árbol estocástico.
2. Conciliar los datos numéricos y los vectores fuente:
   `Z`, `I`, el calendario del shock y `tail`. Las
   equivalencias de cero de ocho filas no demuestran por sí
   mismas identidad de todas las derivadas del operador de 34 filas.
3. Obtener evidencia de compilación y axiomas del **commit exacto**
   que contiene el módulo enlazado, sin `sorryAx` ni axiomas
   auxiliares especiales sin justificar.
4. Para elevar raíces del sistema reducido, demostrar
   factibilidad por historia, optimalidad individual,
   clearing, apoyo por precios, continuación y terminalidad;
   distinguir KKT necesarias de suficiente optimalidad.
5. Emitir veredicto por resultado: `same_statement_proved`,
   `strictly_weaker`, `conditional_different_statement`,
   `counterexample_to_original` o `still_unreviewed`;
   solo los casos `same_statement_proved` pasan a estado
   integral, y únicamente si las hipótesis están cotejadas.

## 6. Orden de cierre recomendado

**P0 (entrega):** revisar 4.2, 4.4, 4.5, 4.1 y las
identidades de capacidad empresarial; reescribir las
afirmaciones de alcance demasiado amplio en vez de
pretender que cada una ya está formalizada.

**P1 (reproducción):** contrastar integralmente operadores
fuente y Python de 34 filas y sus derivadas, con hashes
de escenario, radios y signos. No aplicar a una IRF de
`h=-10^{-5}` un certificado que cubre solo
`|h|≤10^{-15}`.

**P2 (manuscrito):** cerrar la comparación literal entre
proposición y Lean, añadir el cotejo realmente manuscrito
del autor y el veredicto crítico, revisar las fuentes
bibliográficas y pasar el control visual de PDFs. No
fusionar PR #2 antes del cierre de los checks.

No se hace afirmación de que todas estas tareas deban
completarse para disponer de un paper **condicional** y
honesto para el curso; sí son necesarias antes de
declarar cerrado el programa científico general.
