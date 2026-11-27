# Control manuscrito del artículo de ocho resultados

**Estado histórico al 25/11/2026:** **0/8** derivaciones recibidas. **Actualización posterior, 26/11/2026 (22:07 Lima): 8/8 resultados con manuscritos auténticos recibidos, subidos a GitHub y cotejados; las hipótesis de seis pruebas y las cotas racionales de las otras dos se registran en [auditoría matemática](AUDITORIA_ECUACIONES_MANUSCRITAS_8_20261127.md). La equivalencia integral Lean continúa pendiente.** Véase [registro y copia del original](REGISTRO_MANUSCRITOS_RECIBIDOS_20261126.md). Las guías son material tipografiado, **no** evidencia personal del autor. La versión anterior de 60 resultados está preservada en la rama histórica.

| Orden | Etiqueta | Prueba | Guía para el iPad | Manuscrito real |
|---:|---|---|---|---|
| 1 | `prop:local_macro_multiplicity` | Complementariedad local | Primera tanda: Proposición 4.2 | Recibido y cotejado, págs. 1–3 |
| 2 | `lem:repayment` | Repago por garantía robusta | Primera tanda: Lema 3.1 | Recibido y cotejado, págs. 3–4 |
| 3 | `lem:v0m_original_6_2` | No ahorrar y endeudarse a la vez | Primera tanda: Lema 3.2 | Recibido y cotejado, págs. 4–5 |
| 4 | `prop:v0m_original_6_3` | Capacidad financiable | Primera tanda: Proposición 3.3 | Recibido y cotejado, págs. 5 |
| 5 | `lem:allocation_loss_identity` | Pérdida asignativa y MPK | Primera tanda: Lema 4.3 | Recibido y cotejado, págs. 6–8 |
| 6 | `prop:compact_exact_tail_power` | Potencias de matriz de 48 pasos | `GUIA_CUERPO_3_RESULTADOS_20261125.md` | Recibido y cotejado, págs. 9 |
| 7 | `lem:compact_robust_tail_power` | Mayorante matricial robusto | `GUIA_CUERPO_3_RESULTADOS_20261125.md` | Recibido y cotejado, págs. 10–11 |
| 8 | `prop:compact_source_collateral_effective_wedge` | Cuña de precio efectivo | `GUIA_CUERPO_3_RESULTADOS_20261125.md` | Recibido y cotejado, págs. 11–12 |

Para cada demostración, colocar: etiqueta, hipótesis, manipulación sin saltos, nombre de teorema/regla aplicado, dominio y signos, conclusión y comentario propio sobre verificación o corrección de IA.

**Evidencia requerida:** archivo(s) PDF auténticos exportados del iPad (con hojas numeradas y legibles) vinculados por etiqueta. Antes de marcar «aprobada», cotejar su enunciado con el PDF *definitivo*, no con la versión extensa de 145 páginas. No suponer que el autor ha finalizado notas sin recibirlas.


## Correspondencia entre las hojas de iPad y la numeración nueva del PDF

**Verificación directa:** se extrajeron los encabezados de las ocho proposiciones/lemas del PDF compacto compilado (16 páginas, SHA-256 `5672d626f3bc4a79227ede4d61b7bde1f826607699bfe8b789e7300f70747e92`). La numeración cambia al mover cuatro resultados al apéndice; la **etiqueta LaTeX** constituye el identificador estable.

| Etiqueta LaTeX | Numeración histórica que usa la primera tanda | Numeración impresa en el PDF compacto | Página del PDF |
|---|---|---|---:|
| `prop:local_macro_multiplicity` | Proposición **4.2** | Proposición **3.1** | 4 |
| `lem:repayment` | Lema **3.1** | Lema **A.1.1** | 13 |
| `lem:v0m_original_6_2` | Lema **3.2** | Lema **A.1.2** | 13 |
| `prop:v0m_original_6_3` | Proposición **3.3** | Proposición **A.1.3** | 14 |
| `lem:allocation_loss_identity` | Lema **4.3** | Lema **A.1.4** | 14 |
| `prop:compact_exact_tail_power` | Resultado nuevo del cuerpo compacto | Proposición **5.1** | 8 |
| `lem:compact_robust_tail_power` | Resultado nuevo del cuerpo compacto | Lema **5.2** | 8 |
| `prop:compact_source_collateral_effective_wedge` | Resultado nuevo del cuerpo compacto | Proposición **5.3** | 10 |

**Instrucción para el autor:** no rehacer las hojas ya escritas. Añadir, en el encabezado o índice de la digitalización, ambos números y la etiqueta LaTeX. La demostración y sus hipótesis deben cotejarse contra **la versión compacta** antes de marcarse revisadas. **Actualización:** el PDF auténtico de doce páginas ya fue recibido y preservado en Drive; su cobertura está en el registro vinculado. La fecha de recepción es posterior al corte de las 22:00, y ninguna prueba está marcada como aprobada matemáticamente.


## Fuente recibida y estado académico

Se recibió `ai-ieproject.pdf` (12 páginas), SHA-256 `14b081edf35c52882bd433021980a8beb12cdf805733aa4b4bca5839d9fcb8a1`. **Cobertura 8/8 recibida**. Original en Drive privado: https://drive.google.com/file/d/1fq4tjuBwCBGerDX6sNwDeCPP89VuaXWv/view?usp=drivesdk . El [PDF original está alojado en GitHub](ai-ieproject.pdf), con Git blob exacto `7cc7b4378dabda89fd28eb623fa6c034c47a6ef4`; la auditoría manuscrito–paper se completó y las cotas matriciales fueron reejecutadas con aritmética racional. La formalización literal Lean de los ocho enunciados sigue abierta.
