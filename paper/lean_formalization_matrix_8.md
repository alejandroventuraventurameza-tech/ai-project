# Cotejo de los ocho resultados del paper compacto — 25/11/2026

La rama `archive/ie-paper-full-20261118` conserva el artículo histórico de 145 páginas y los registros de 57 resultados. **Esta rama candidata reduce el paper sometido a exactamente ocho resultados numerados distintos**, identificados abajo. No elimina código, datos ni pruebas Lean históricas; los separa del objeto evaluable.

| Etiqueta en el paper compacto | Resultado | Evidencia relacionada | Estado exacto para este paper |
|---|---|---|---|
| `prop:local_macro_multiplicity` | Dos raíces locales de complementariedad | `ScalarComplementarityMultiplicityCandidate.lean` y un certificado económico condicional | **ABIERTO**: no se han identificado/satisfecho como teorema Lean las hipótesis de diferenciabilidad, raíz interior y la recuperación SOURCE |
| `prop:compact_exact_tail_power` | Decaimiento de potencias de matriz decimal | `exact_linear_tail_power_certificate.py` con fracciones exactas | **ABIERTO EN LEAN**: cotejo matemático condicional y certificado racional Python; no declaración Lean equivalente |
| `lem:compact_robust_tail_power` | Robustez en bola de norma matricial | `exact_linear_tail_power_certificate.py`, cota recursiva de mayorantes | **ABIERTO EN LEAN**: telescopado y recursión demostrados por escrito y evaluados con fracciones, no equivalencia literal |
| `prop:compact_source_collateral_effective_wedge` | Cuña de precios efectivos con garantía vinculante | Lemas SOURCE de cuña financiera kernel-verified citados en `body_compact_after.tex` | **ABIERTO PARA ESTE ENUNCIADO**: verificar correspondencia exacta de `J`, pignorabilidades y dominio con el paper |
| `lem:repayment` | Cobertura de pago y patrimonio no negativo | `PaperRepaymentExactCandidate.lean` (teorema de interfaz fuente relacionado) | **ABIERTO PARA ESTA VERSIÓN**: candidato verificado sobre `repaymentSpec`, pero el enunciado del artículo compacto debe cotejarse contra el Lean actual |
| `lem:v0m_original_6_2` | Prohibición de préstamos y depósitos interiores simultáneos | `FinancialCore.lean`, `PaperFinancialMainExactCandidate.lean` | **ABIERTO PARA ESTA VERSIÓN**: hipótesis KKT normalizadas, positividad y dominio deben compararse literalmente |
| `prop:v0m_original_6_3` | Derivada de capital máximo financiable | `FinancialCore.lean`, `PaperFinancialMainExactCandidate.lean` | **ABIERTO PARA ESTA VERSIÓN**: cotejar existencia del máximo y derivada con la especificación completa de `n,q,H,R^L` |
| `lem:allocation_loss_identity` | Referente eficiente y derivada de pérdida asignativa | `PaperAllocationLossElasticityCandidate.lean`, lemas físico-MPK y fuente integrados | **ABIERTO PARA ESTA VERSIÓN**: los 42 teoremas relacionados no acreditan automáticamente igualdad literal de la proposición reformulada |

**Ninguna fila se marca como prueba completa por semejanza de nombres**. El artículo sí contiene demostraciones analíticas, y hay pruebas Lean auxiliares revisadas; el estado de un lado no sustituye la comprobación del otro.

## Protocolo aún pendiente

1. Fijar commit del PDF definitivo y comprobar que coincide con las fuentes.
2. Para cada resultado leer el enunciado en `paper/paper.tex` / `paper/appendix_eight_results.tex` y su especificación Lean exacta, comparando tipos, dominios, signos, cuantificadores y condiciones de contorno.
3. Reportar por fila `proved`, `proved under extra assumptions` (especificar cuáles) u `open` (bloqueo concreto). Nunca inventar una ejecución completa de AppliedModelingLib.
4. Compilar el módulo anclado (o documentar de forma honesta por qué no pudo ejecutarse) y conservar salida de `python3 scripts/paper_contribution.py check Ventura26LiquidityAllocation --fast`.
5. Incorporar la misma clasificación a la tabla dentro del PDF. La tabla ya está escrita en `paper/appendix_eight_results.tex`; necesita compilación PDF y revisión.

La matriz más amplia de 60 está preservada en `paper/lean_formalization_matrix_60.md` para trazabilidad y **no corresponde al alcance de la versión compacta**.
