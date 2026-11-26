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

## Cierre literal de recursos en el portador SOURCE

- **DEMOSTRADO**, compuerta Lean de frontera #42720016791, SHA
  `b18e1def5a37baf94d037c5f14fafecd9a4d305b`: el módulo
  `BoundaryFullResourceClearingCandidate.lean` establece
  `ResourceClears (boundaryPrimitives G boundarySourceRate)
  (sourceBoundaryLiteralAllocation G)` sin `sorryAx`. La prueba contiene:
  (a) recursos de fechas 0 y 1 y de toda la cola estacionaria como filas
  reducidas; (b) capital heredado al inicio; (c) identidad entre el capital
  elegido en t y el instalado en t+1; (d) producto efectivo y cuentas de
  inversión/costo coincidentes con los datos reducidos. Este certificado
  **no** es un resultado de óptimo privado, factibilidad total, ni existencia
  de equilibrio competitivo.

El argumento utiliza productividad agregada uno en las tres fases de este
testigo artificial. No se extiende por sí mismo a shocks agregados generales,
intervenciones persistentes ni otra distribución estocástica. La auditoría
global de todos los candidatos constituye una compuerta independiente de
la focalizada.

## Liquidación OTC y cuentas fiscales del SOURCE

- **DEMOSTRADO**, compuerta Lean de frontera #42722416369, SHA
  `a14d825c5bc18311dc3a14c2dadc87c78cc79429`:
  `BoundaryFullSettlementCandidate.lean` verifica
  `SettlementClears (boundaryPrimitives G boundarySourceRate)
  (sourceBoundaryLiteralAllocation G)` y
  `FiscalClosure (boundaryPrimitives G boundarySourceRate)
  (boundaryInitialState G boundarySourceRate)
  (sourceBoundaryLiteralAllocation G)`. Incluye la cota estricta de
  depósitos frente a reservas en fecha cero, los dominios bancarios
  exactos en fechas uno y posteriores, y la correspondencia del encaje
  con la historia admisible del árbol determinista. El certificado
  audita `#print axioms` sin `sorryAx`.
- Estas ecuaciones cierran el mercado OTC *agregado del portador común* y
  las cuentas fiscales residuales; no construyen una población bancaria
  dinámicamente óptima, ni demuestran por sí mismas
  `BankPopulationEquilibrium`, `HouseholdBudgetFlows` o
  `CompetitiveEquilibrium`. El parámetro `G` permanece simbólico; su
  dominio económico positivo debe verificarse al cerrar
  `MonetaryPolicyPrimitiveDomain`.

## Capital físico y presupuestos empresariales

- **DEMOSTRADO**, commit `7b021e61f8ffdcd525901d6c44871dae87fc6b67`,
  compuerta Lean #42723290194 y auditoría general #42723281305:
  `sourceBoundaryLiteralAllocation_capitalProducerAccounts` prueba
  `CapitalProducerAccounts P X` con capital e inversión estrictamente
  positivos en todas las fechas admitidas. No certifica
  `CapitalProducerOptimal`.
- **DEMOSTRADO (compuerta focalizada)**, commit
  `d195b1fd271d0da06578df0be49b10cb3686cd07`,
  compuerta Lean #42725580101: el módulo
  `BoundaryFullFirmBudgetCandidate.lean` demuestra
  `FirmBudgetFlows P I X` al conectar las filas reducidas con las
  promesas nominales heredadas y la riqueza de cada empresa.
  La auditoría general #42725570386 se comprueba por separado
  y no debe darse por aprobada sin ver su resultado.

## Advertencia: compatibilidad financiera inicial

- **NUMÉRICO (NO prueba Lean)**: el diagnóstico de 70 dígitos indica
  `Delta_Face ≈ +0.08291496457343135383655` en la raíz SOURCE;
  el estado estacionario anterior da esencialmente cero. El residual
  de recursos de la frontera es asimismo esencialmente cero. La
  definición exacta de `InheritedNominalFaceConsistency` requiere
  `Delta_Face = 0`, por lo que esta condición no puede tratarse como
  cerrada por las 33 ecuaciones.
- Diagnóstico reproducible y obligación de certificación exacta:
  `docs/SOURCE_INHERITED_FACE_DIAGNOSTIC_20261109.md` y
  `scripts/audit_source_inherited_nominal_faces.py`.
  Probar formalmente el signo mediante un intervalo racional está
  **PENDIENTE**. No reparar silenciosamente los depósitos heredados ni
  declarar equilibrio completo.

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
3. **Presupuestos/mercados:** `HouseholdBudgetFlows` e
   `InheritedNominalFaceConsistency` siguen pendientes. Los predicados
   `FirmBudgetFlows`, `CapitalProducerAccounts`, `FiscalClosure` y
   `ResourceClears` cuentan con certificación focalizada para el testigo,
   pero no eliminan el residual heredado ni las exigencias de optimalidad.
4. **Liquidación OTC:** `SettlementClears` ya está demostrado para el
   portador común y todas las historias admitidas. Sigue pendiente el
   equilibrio de la **población bancaria** con Bellman y factibilidad
   individual; no se deduce de la igualdad agregada.
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
registrar la auditoría general de `FirmBudgetFlows`; acotar el residual
nominal heredado del SOURCE con garantías exactas; verificar
`BankRenewalFlows` y resolver de forma económicamente legítima el estado
inicial antes de probar `HouseholdBudgetFlows`. Después, certificar
factibilidad, optimalidad y transversalidad. Mantener
`main` sin cambios y el PR en borrador hasta las compuertas científicas.
