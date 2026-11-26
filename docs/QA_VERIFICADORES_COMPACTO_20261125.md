# Auditoría de compatibilidad de las verificaciones — 25/11/2026

**Estado:** candidato, sin ejecución integral posterior a los cambios.

## Defecto detectado y corrección

La versión compacta del paper tiene ocho resultados y el documento original tenía 57. El code/verify.py del proyecto incluía varias auditorías que leían paper/paper.tex y exigían el SHA, los enunciados y las etiquetas del trabajo histórico. Dejar esas rutas intactas habría hecho fallar el control oficial.

Se preservó la fuente histórica byte por byte en paper/historical/paper_full_20261118.tex, Git blob SHA 033dfbd41ff30eb1c167a4d468cb3751d6fe2d46, el mismo del 18/11. El ledger original permanece en paper/result_ledger.json. Ninguna prueba anterior fue eliminada ni se bajó su estándar.

## Scripts actualizados

| Archivo | Cambio y alcance |
|---|---|
| code/v0m/verify_v0m.py | Coteja 57 resultados y SHA-256 del histórico, no del compacto |
| code/v0m/sampled_checks.py | Registra el hash del histórico al realizar sus 5,000 casos |
| code/audit_claim_scope.py | Conserva las dos proposiciones y objeciones SOURCE del histórico |
| code/irf/audit_prefix_rows.py | Comprueba etiquetas del histórico y mantiene la auditoría 33x33 |
| code/irf/audit_financial_blocks.py | Comprueba etiquetas financieras contra el histórico |
| code/verify_compact_paper.py (nuevo) | Comprueba ocho resultados, ocho entornos de prueba, citas, finanzas racionales, pérdida asignativa y certificado matricial |
| code/verify.py | Ejecuta la nueva compuerta después de las verificaciones anteriores |

Inspección estática efectuada: 74 scripts invocados directamente por code/verify.py y seis scripts dependientes de V0M; se rastrearon referencias directas al paper, el ledger y SHA. Esto no prueba que no existan dependencias indirectas más profundas.

## Evidencia y límites

- PDF compacto: compilación local de 11 páginas de cuerpo, 16 totales; 0 desbordamientos y 0 referencias indefinidas en el último log.
- Pruebas prototipo independientes: 80 casos racionales financieros/escalares y 80 comparaciones de derivada de pérdida asignativa mediante paso complejo, aprobadas localmente.
- Fuente histórica: Git blob SHA exacto confirmado en la nueva rama.
- **Pendiente:** ejecución INTEGRAL de python code/verify.py sobre el último checkout, comprobación Lean de AppliedModelingLib con el PDF final y sincronización del PDF compacto en GitHub.
- Manuscritos del autor: todavía 0/8 auténticos incorporados a la rama.

**Veredicto:** se reparó la incompatibilidad estructural y se agregó control para el paper compacto. No equivale a CI verde y no autoriza todavía el merge.
