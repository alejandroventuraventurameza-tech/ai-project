# IE Project 18 — tres familias de filas SOURCE reales en ambas fechas (12-XI-2026)

## Resultados validados antes de este incremento

El workflow `Lean stationary policy and payment bridge (pinned)` del commit `69d3337b01b81614af68acead0d7383780a1f9c0` concluyo `success` en la ejecucion [43274128696](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/43274128696). La identidad exacta de la fila SOURCE real `.commonPledgeOne`, su reconstruccion logaritmica y la equivalencia de conjuntos de ceros bajo condiciones de dominio fueron verificadas por el kernel.

Los seis lemas algebraicos de conversion log-nivel y cizallas Euler ya habian sido verificados; no se deben confundir con una correspondencia economica SOURCE/Python completa.

## Nuevo alcance SOURCE real: seis ecuaciones a dos fechas

El modulo `lean/candidates/Ventura26LiquidityAllocation/SourceSixScalarRowsLogBridgeCandidate.lean` apunta directamente a `localReducedRemainingResidual` y `localReducedPrefixResidual` de `EconomicModel.lean`.

Las tres familias incluidas son:

**Transicion nominal del banco (fila local 0).** `S_B(d) = d.nextBankFace - bankRenewalFactor(P)*d.controls.loanRate*d.currentBankFace/d.controls.inflation`. El denominador de normalizacion es el valor nominal predicho `B(d)`. Con `B(d) ≠ 0` y `1+S_B(d)/B(d)>0`, `log(1+S_B/B)=0 ↔ S_B=0`.

**Oferta de trabajo de los hogares (fila local 3).** `S_L(d)=d.controls.wage - P.laborScale*d.controls.workerConsumption^P.workerRiskAversion * (localPrefixAggregateLabor(P,d))^P.laborCurvature`. El denominador es el salario predicho `W(d)`. Bajo `W(d) ≠ 0` y `1+S_L(d)/W(d)>0`, la normalizacion logaritmica comparte el mismo conjunto de ceros.

**Euler del trabajador (fila local 4).** `S_H(d)=1 - R(d)`, donde `R(d)` contiene la tasa de deposito, la inflacion siguiente y el cociente intertemporal de utilidades marginales CRRA. En la carta positiva `R(d)>0`, el logaritmo `log(1-S_H)` tiene ceros equivalentes a `S_H`.

Las funciones `localPrefixDateZeroData` y `localPrefixDateOneData` del SOURCE conectan estas tres familias a las seis ecuaciones reducidas de fechas cero y uno. El `tail` de fecha dos permanece la regla abstracta SOURCE real: no se confunde con el terminal numerico `P0`.

El nuevo modulo contiene **12 teoremas candidatos**: tres expresiones exactas de nivel, tres equivalencias de ceros logaritmicos y seis identidades de insercion en las dos fechas. Se anadio al workflow Lean con inspeccion `#print axioms` y rechazo de `sorryAx`. **Su categoria actual es PENDIENTE DE KERNEL** hasta obtener el resultado de GitHub Actions de la revision de integracion.

## Hipotesis y limites cientificos

1. Cada equivalencia de ceros requiere condiciones de dominio sobre denominadores y razones positivas, aun no deducidas del equilibrio economico general.
2. Una identidad de SOURCE reducida no garantiza que un punto de la implementacion Python sea una raiz SOURCE.
3. El contrato SOURCE `tail` aun no se ha identificado funcionalmente con el `P0` de la implementacion numerica sobre un abierto.
4. Ninguna de las nuevas proposiciones establece la existencia de un equilibrio completo, los KKT de firmas y bancos ni los signos del crecimiento de largo plazo.

## Proximo bloque

Tras revisar la compilacion de estas seis filas, extender la normalizacion al par de filas de regimen de colateral y formalizar las dos cizallas Euler *directamente* con los terminos del SOURCE. A continuacion derivar hipotesis de positividad del conjunto admisible y cerrar la carta exacta SOURCE–Python antes de transportar un certificado de inversa economica.

PR #2 sigue en borrador y `main` no se fusiona.
