# Auditoría SOURCE: portador intertemporal, contabilidad y obligaciones abiertas

**Fecha:** 9 de noviembre de 2026 (Lima). **Rama:** `work/lean-ci-validation-otc-20261106`. **PR:** #2, borrador. La revisión del repositorio y los certificados de CI se deben leer por su SHA, no solo por la fecha del documento.

## Objeto económico auditado

Sea `R★ = boundarySourceRate`, raíz única del **tipo bruto de préstamo** en
`[41/40,129/125]`, no una innovación libre de la tasa de remuneración de
reservas ni un coeficiente de encaje. Se fijan

```lean
P := boundaryPrimitives G boundarySourceRate
I := boundaryInitialState G boundarySourceRate
d := sourceBoundaryDateData G
X := sourceBoundaryLiteralAllocation G
```

El portador `X : Allocation LocalBridgePhase` tiene campos para **todas**
las fechas e historias; `d` usa la fecha cero de frontera, la fecha uno
con lags/innovaciones anunciadas y una cola estacionaria explícita. Que
exista este `X` no implica `CompetitiveEquilibrium P I X`: su construcción
no demuestra optimalidad, mercado de bancos, KKT, TVC, tasa de supervivencia,
ni convergencia a un equilibrio competitivo completo.

## Resultados certificados y trazabilidad mínima

- **DEMOSTRADO**, compuerta Lean focalizada #42708660600, SHA
  `143bac75583483f667cff320c4913fd571a616e3`: la tasa SOURCE tiene
  raíz única, 33 filas reducidas, positividad y regímenes iniciales descritos
  por las declaraciones exactas del módulo `BoundaryNormalizationBridgeCandidate`.
- **DEMOSTRADO**, compuerta #42712322505, SHA
  `97368560b706356eb4595dde379cf0364b560f9c`: bajo hipótesis
  literales de realización, las transiciones de patrimonio bancario en fechas
  cero y uno son consecuencia de la reducción; la superficie de coordenadas
  no identifica impuestos.
- **DEMOSTRADO**, compuerta #42717003155, SHA
  `fb533616191470404c200673ef2df53cabc2c373`: el portador
  explícito y el balance bancario `BankBalance P X`, así como las pruebas
  previas importadas, compilan con auditoría de `#print axioms` sin `sorryAx`.
  `BankBalance` es una igualdad de stocks, no `BankOptimal`.
- **DEMOSTRADO**, compuerta #42717672368, SHA
  `cb89e939d30cb49930004abba863b7413c84d50b`: el módulo
  `BoundaryFullRealAccountingCandidate.lean` compila con auditoría de
  `#print axioms` sin `sorryAx`. Quedan demostradas para `X` las
  identidades `AggregateProduction`, `CapitalClears`,
  `AccountingIdentities` y `CurrentNominalFaceConsistency`, además de
  las equivalencias exactas que aíslan los residuos fiscales, reales y
  domésticos. Estas equivalencias **no** descargan sus premisas económicas.

## Brechas remanentes de equilibrio completo

`CompetitiveEquilibrium` en `EconomicModel.lean` exige de forma
conjunta 22 familias de condiciones, además de preservar primitivas,
herencias y el estado del instrumento inicial. Las siguientes son **ABIERTAS**
para `X` salvo prueba posterior específica:

1. **Dominio y política:** `MonetaryPolicyPrimitiveDomain`,
   `PositiveDomain`, `MonetaryPolicyRules`, incluidas innovaciones en
   fechas y estados correctos y deuda pública positiva para `G` adecuado.
2. **Agentes:** `FirmOptimal` para H/L, `HouseholdOptimal`,
   `BankPopulationEquilibrium`, `RetailOptimal` y
   `CapitalProducerOptimal`, con suficiencia global y condiciones
   terminales; no basta Euler/KKT reducido.
3. **Presupuestos/mercados:** `FirmBudgetFlows`,
   `HouseholdBudgetFlows`, `InheritedNominalFaceConsistency`,
   `CapitalProducerAccounts`, `FiscalClosure`, `ResourceClears`.
   Algunas identidades contables están cerradas pero no todas las
   condiciones de factibilidad.
4. **Liquidación OTC:** los flujos interbancarios netos del banco común no
   se anulan por `BankBalance`. `SettlementClears` y los márgenes de
   facilidad deben verificarse para cada historia admitida.
5. **Dinámica/crecimiento:** una cola estacionaria elegida por
   construcción no es prueba de que agentes optimizadores la seleccionen.
   Tampoco demuestra selección S/B, persistencia estocástica, óptimo
   asignativo ni crecimiento sostenido.

## Cortes exactos del siguiente módulo

El candidato `BoundaryFullRealAccountingCandidate.lean` plantea

```text
ResourceClears(P,X) <-> SourceRealResourceCompatibility(P,I,X_raw)
HouseholdBudgetFlows(P,I,X) <-> SourceFiscalHouseholdCompatibility(P,I,X_real)
SettlementClears(P,X_raw) -> FiscalClosure(P,I,X)
```

Las equivalencias **no prueban sus lados derechos**. Su virtud es exponer
qué debe verificarse en las variables fuente, sin ocultarlo en un supuesto de
equilibrio ni en los 33 residuales. `CurrentNominalFaceConsistency`
requiere demostrar `loanRate_t ≠ 0` para todas las fechas.

## Próxima compuerta

Conservar el certificado Lean focalizado #42717672368 en `cb89e939` y
recuperar la auditoría completa de candidatos de esa misma revisión. Después,
derivar las filas de recursos y
el presupuesto doméstico literal, el saldo OTC por historia, y por separado
el conjunto de condiciones de optimalidad y transversalidad. Mantener
`main` sin cambios y el PR en borrador hasta las compuertas científicas.
