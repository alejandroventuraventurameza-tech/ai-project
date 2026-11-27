# Cotejo de los ocho resultados del paper compacto — 25/11/2026

La rama `archive/ie-paper-full-20261118` conserva el artículo histórico de 145 páginas y los registros de 57 resultados. **Esta rama candidata reduce el paper sometido a exactamente ocho resultados numerados distintos**, identificados abajo. No elimina código, datos ni pruebas Lean históricas; los separa del objeto evaluable.

| Etiqueta en el paper compacto | Resultado | Evidencia relacionada | Estado exacto para este paper |
|---|---|---|---|
| `prop:local_macro_multiplicity` | Dos raíces locales de complementariedad | `CurrentCompactProp31C1Bridge.lean`: `prop31_scalar_from_only_C1_hypotheses`, Actions #45874767483 | **DEMOSTRADO EN LEAN PARA LA FUNCIÓN ESCALAR C1 ABSTRACTA** bajo signos y derivadas exigidos; **ABIERTO** construir dicha función y recuperación SOURCE real desde las 33 ecuaciones |
| `prop:compact_exact_tail_power` | Decaimiento de potencias de matriz decimal | `CurrentCompactBlock48Tail.lean`: `prop51_unconditional_exact`, Actions #45865176408; certificado racional Python repetido #45933840987 | **DEMOSTRADO EN LEAN PARA LOS 36 DECIMALES FIJADOS DE F0**, norma real inducida y todos los k/x; **ABIERTO** identificar F0 con la dinámica derivada del equilibrio SOURCE |
| `lem:compact_robust_tail_power` | Robustez en bola de norma matricial | `CurrentCompactRobustFiniteCertificate.lean`: `lemma52_decimal_current_exact`, Actions #45871289804; certificado racional Python #45933840987 | **DEMOSTRADO EN LEAN PARA TODA MATRIZ REAL 6×6 A A DISTANCIA ≤10^-4 DE F0**, tres cláusulas del lema; **ABIERTO** verificar la distancia del Jacobiano SOURCE efectivo a F0 |
| `prop:compact_source_collateral_effective_wedge` | Cuña de precios efectivos con garantía vinculante | Lemas SOURCE de cuña financiera kernel-verified citados en `body_compact_after.tex` | **ABIERTO PARA ESTE ENUNCIADO**: verificar correspondencia exacta de `J`, pignorabilidades y dominio con el paper |
| `lem:repayment` | Cobertura de pago y patrimonio no negativo | `PaperRepaymentExactCandidate.lean` (teorema de interfaz fuente relacionado) | **ABIERTO PARA ESTA VERSIÓN**: candidato verificado sobre `repaymentSpec`, pero el enunciado del artículo compacto debe cotejarse contra el Lean actual |
| `lem:v0m_original_6_2` | Prohibición de préstamos y depósitos interiores simultáneos | `FinancialCore.lean`, `PaperFinancialMainExactCandidate.lean` | **ABIERTO PARA ESTA VERSIÓN**: hipótesis KKT normalizadas, positividad y dominio deben compararse literalmente |
| `prop:v0m_original_6_3` | Derivada de capital máximo financiable | `FinancialCore.lean`, `PaperFinancialMainExactCandidate.lean` | **ABIERTO PARA ESTA VERSIÓN**: cotejar existencia del máximo y derivada con la especificación completa de `n,q,H,R^L` |
| `lem:allocation_loss_identity` | Referente eficiente y derivada de pérdida asignativa | `PaperAllocationLossElasticityCandidate.lean`, lemas físico-MPK y fuente integrados | **ABIERTO PARA ESTA VERSIÓN**: los 42 teoremas relacionados no acreditan automáticamente igualdad literal de la proposición reformulada |

**Actualización posterior al corte:** los resultados escalares de la Proposición 3.1 y las afirmaciones matemáticas sobre la matriz decimal de la Proposición 5.1 y el Lema 5.2 tienen teoremas Lean explícitos y compuertas verificadas. Esto **no** implica que la función escalar del sistema económico real o el Jacobiano SOURCE completo coincidan con esos objetos. Las otras cinco correspondencias literales paper–Lean requieren auditoría por especificación exacta, aunque existan lemas auxiliares. No se eleva un teorema por semejanza de nombres.

## Protocolo aún pendiente

1. Fijar commit del PDF definitivo y comprobar que coincide con las fuentes.
2. Para cada resultado leer el enunciado en `paper/paper.tex` / `paper/appendix_eight_results.tex` y su especificación Lean exacta, comparando tipos, dominios, signos, cuantificadores y condiciones de contorno.
3. Reportar por fila `proved`, `proved under extra assumptions` (especificar cuáles) u `open` (bloqueo concreto). Nunca inventar una ejecución completa de AppliedModelingLib.
4. Compilar el módulo anclado (o documentar de forma honesta por qué no pudo ejecutarse) y conservar salida de `python3 scripts/paper_contribution.py check Ventura26LiquidityAllocation --fast`.
5. Incorporar la misma clasificación a la tabla dentro del PDF. La tabla ya está escrita en `paper/appendix_eight_results.tex`; necesita compilación PDF y revisión.

La matriz más amplia de 60 está preservada en `paper/lean_formalization_matrix_60.md` para trazabilidad y **no corresponde al alcance de la versión compacta**.


## Adenda manuscrita posterior al cierre del 26/11/2026

El [PDF auténtico de 12 páginas](../hand/ai-ieproject.pdf) ya está adjunto al repositorio, SHA-256 `14b081edf35c52882bd433021980a8beb12cdf805733aa4b4bca5839d9fcb8a1`. El [cotejo de los ocho resultados](../hand/AUDITORIA_ECUACIONES_MANUSCRITAS_8_20261127.md) y la [verificación numérica racional reejecutada](https://github.com/alejandroventuraventurameza-tech/ai-project/actions/runs/45933840987) confirman la cobertura y las cotas del F0 decimal. Las hojas llegaron después de las 22:00 de Lima; esta actualización no reescribe la cronología del PDF científico ya sometido.
