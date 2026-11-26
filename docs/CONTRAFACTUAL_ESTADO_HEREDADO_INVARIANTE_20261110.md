# IE — Contrafactual monetario con estado heredado invariante (especificación de reparación)

**Fecha:** 2026-11-10. **Rama:** `work/lean-ci-validation-otc-20261106`. **Estado:** `PENDIENTE` como existencia de equilibrio; protocolo de construcción y falsación, no solución declarada.

## 1. Diagnóstico comprobado y alcance

El candidato SOURCE construye `boundaryInitialState G R`: las caras nominales empresariales heredadas, capital y cara bancaria varían con la tasa de crédito contemporánea `R`. Por ello, comparar dos tasas usando dos instancias de dicho constructor no constituye un experimento de política monetaria *no anticipada* con los mismos activos y pasivos al inicio.

Hay una identidad de descomposición de la brecha de caras nominales sobre el SOURCE original, certificada por Lean, y una auditoría racional independiente del intervalo `R ∈ [1.029135,1.029136]` que acota la brecha por abajo en `0.082885242451942429580652`. **No confundir:** los tres signos necesarios en las expresiones originales de Lean siguen sin prueba de kernel. Véase `docs/SOURCE_FACE_GAP_INTERVAL_PROOF_LEDGER_20261109.md`.

## 2. Cronología admisible del shock

Para `t = -1`, se determinan `S_{-1}` (estado económico completo, incluidas caras nominales, deuda y depósitos de hogares, reservas y pasivos bancarios, capital instalado, distribución de firmas y activos del banco central). Sea `\varepsilon_0` la innovación monetaria anunciada **después** de fijado `S_{-1}`.

Se imponen, para cada rama `j ∈ {S,B}` y para ambos escenarios `e ∈ {base,shock}`:

```text
S_{-1}^{j,base} = S_{-1}^{j,shock} = Sbar_{-1}^{j}
policyInnovation_0^{j,base} = 0
policyInnovation_0^{j,shock} = -10^-5
policyInnovation_t^{j,e} = 0   for all t > 0
reserveRequirementCoefficient_t^{j,e} = 0.10
```

La invariancia inicial es una condición de diseño del experimento, no una identidad deducible de las 33 ecuaciones reducidas. Se pueden permitir *diferentes* estados entre las ramas S y B solamente si se declara expresamente qué comparación se está realizando; el shock dentro de cada rama exige el mismo estado.

**Unidad:** `-10^-5` es una innovación en la regla de *remuneración de reservas*, no una variación en el coeficiente de encaje. El equilibrio puede implicar variaciones endógenas de la tasa de crédito y de la liquidez bancaria.

## 3. Contrato formal que deben satisfacer las nuevas trayectorias

Definir un objeto `FullEquilibriumCandidate (j,e)` que contenga, como mínimo, trayectoria de asignaciones, precios, tasas, préstamos, ahorro, faces de deuda, efectivo/reservas, posiciones de facilidad y transferencias fiscales. No usar `boundaryInitialState G R` como función del precio contemporáneo para el estado heredado.

La validación requiere, para **todo** `t ≥ 0` y escenarios `e`:

1. Presupuestos de hogares, empresarios H/L, bancos y gobierno, con calendario preciso de vencimiento y renovación.
2. Identidades de liquidación OTC y de conservación de recursos (incluido `t=0`, antes y después del shock).
3. Factibilidad de posiciones individuales y del balance agregado de bancos; preservación de todas las *caras nominales heredadas*.
4. Optimalidad privada, incluidos KKT completos, desigualdades de colateral, holguras, complementariedad y condiciones de suficiencia pertinentes.
5. Consistencia de expectativas, precios y reglas de política; condiciones iniciales y de transversalidad (TVC) en la continuación infinita.
6. Para una IRF, existencia (o selección explícita) de las dos trayectorias, con el *mismo* `Sbar_{-1}^{j}`, y cálculo de su diferencia.

Una solución del prefijo reducido, un residual pequeño, o una prueba de ecuaciones necesarias no reemplazan los puntos anteriores.

## 4. Dos líneas de trabajo que no deben confundirse

### A. Auditoría negativa de SOURCE (primero)

Conservar la construcción SOURCE *sin corregir depósitos ad hoc*. Cerrar en Lean las tres obligaciones consignadas en el ledger: signos de los dos extremos racionales del residual de recursos y cota **uniforme** `inheritedNominalFaceGap > 0.08` en el intervalo. Solo entonces se puede afirmar la imposibilidad correspondiente sobre el candidato SOURCE, conforme al teorema condicional existente.

### B. Construcción positiva (independiente)

Fijar un estado estacionario heredado `Sbar_{-1}` previamente factible y auditado; resolver base y shock con el mismo `Sbar_{-1}`. Si la liquidación o el presupuesto de fecha cero falla, cambiar flujos **endógenos o una especificación declarada** y volver a resolver, **no** retocar depósitos heredados ni faces empresariales para cuadrar una identidad. Se exige comparar el ajuste de bancos, empleo, inversión y precios bajo ambas ramas.

## 5. Compuertas de entrega y criterios de rechazo

- `DEMOSTRADO`: teorema Lean sobre expresiones originales con ejecución y auditoría de axiomas del SHA exacto.
- `NUMÉRICO EXACTO`: intervalos racionales sobre traducción independiente, sin promoción a prueba del objeto Lean.
- `NUMÉRICO`: trayectorias reproducibles con tasas, márgenes KKT, residuos, sensibilidad a horizonte y condiciones terminales.
- `PENDIENTE`: equilibrio competitivo infinito, interpretación causal y crecimiento de largo plazo mientras no haya pruebas/soluciones suficientes.

**Criterio de rechazo:** si las caras nominales de `t=-1` cambian al sustituir `\varepsilon_0=0` por `-10^-5`, ese objeto no es el contrafactual no anticipado anunciado. Si el cierre financiero en `t=0` falla, no presentar la trayectoria como equilibrio. Si un estado/teorema está certificado solo en el reducido, no etiquetarlo como equilibrio completo.

## 6. Próximo objetivo de formalización

Importar las fórmulas SOURCE de `BoundaryInheritedFaceIntervalBridgeCandidate.lean` y reducir los tres hechos numéricos a desigualdades en el kernel sin `sorry` ni axiomas artificiales; de manera separada, introducir una estructura `PredeterminedState` que no dependa de `R_0`. El siguiente reporte de avance debe consignar el SHA y los runs propios de ambos bloques y nunca extrapolar el éxito de uno al otro.
